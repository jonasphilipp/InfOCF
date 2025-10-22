"""
Inference Operators Base Classes

This module provides the abstract base class for all inference operators in InfOCF.
Concrete inference operators like p-entailment, system Z, system W, and c-inference
inherit from this base class and implement specific inference algorithms.
"""

# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import multiprocessing as mp
from abc import ABC, abstractmethod
from time import perf_counter_ns
from typing import Any, MutableMapping, cast

from pysmt.shortcuts import And, Not, is_unsat

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from inference.deadline import Deadline
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class Inference(ABC):
    """
    Abstract base class for all inference operators in conditional logic.

    This class defines the common interface and functionality shared by all
    inference operators in InfOCF. Concrete implementations must override
    the abstract methods to provide specific inference algorithms.

    The inference process typically involves:
    1. Preprocessing the belief base (optional)
    2. Evaluating queries using the specific inference algorithm
    3. Managing timeouts and performance metrics

    Attributes
    ----------
    epistemic_state : dict[str, Any]
        Internal state containing belief base, solver configuration, timing
        information, and other inference parameters. Key components include:
        - 'belief_base': BeliefBase instance
        - 'smt_solver': str, name of SMT solver to use
        - 'preprocessing_done': bool, preprocessing completion flag
        - 'preprocessing_time': float, preprocessing duration in ms
        - Various timing and status flags

    Notes
    -----
    All inference operators follow a common pattern:
    - Initialize with epistemic state containing belief base and configuration
    - Optionally preprocess the belief base for efficiency
    - Evaluate conditional queries using specific inference rules
    - Handle timeouts and provide performance metrics

    Subclasses should implement:
    - `_preprocess_belief_base()`: Optional preprocessing logic
    - `_inference()`: Core inference algorithm for single queries
    """

    # Explicit attribute annotation for static type checkers
    epistemic_state: dict[str, Any]

    def __init__(self, epistemic_state: dict[str, Any]) -> None:
        self.epistemic_state = epistemic_state

    """
    Preprocessing wrapper method. Handles timeout and measures time.

    Context:
        Wraps abstract _preprocess_belief_base method.

    Parameters:
        Timeout in seconds.

    Side Effects:
        preprocessing_time and preprocessing_timed_out in epistemic_state
    """

    def preprocess_belief_base(self, preprocessing_timeout: int) -> None:
        """
        Preprocess the belief base before running inference.

        Parameters
        ----------
        preprocessing_timeout : int
            Timeout in seconds. If 0, no timeout is enforced.

        Notes
        -----
        Updates timing and status fields in the epistemic state:
        ``preprocessing_time``, ``preprocessing_done``, and ``preprocessing_timed_out``.
        """
        if self.epistemic_state["preprocessing_done"]:
            logger.info(
                "Preprocessing already completed, skipping",
                extra={
                    "preprocessing_time_ms": self.epistemic_state["preprocessing_time"],
                    "belief_base_name": self.epistemic_state["belief_base"].name,
                    "inference_system": self.epistemic_state["inference_system"],
                    "weakly": self.epistemic_state["weakly"],
                },
            )
            return

        # self._epistemic_state._preprocessing_timeout = preprocessing_timeout
        empty = len(self.epistemic_state["belief_base"].conditionals) == 0
        assert not empty, "belief base empty"
        cons, _ = consistency(
            self.epistemic_state["belief_base"],
            solver=self.epistemic_state["smt_solver"],
            weakly=self.epistemic_state.get("weakly", False),
        )
        assert cons != False, "belief base inconsistent"
        deadline = (
            Deadline.from_duration(preprocessing_timeout)
            if preprocessing_timeout
            else None
        )
        try:
            preprocessing_start_time = perf_counter_ns() / 1e6
            self._preprocess_belief_base(self.epistemic_state["weakly"], deadline)
            self.epistemic_state["preprocessing_time"] += (
                perf_counter_ns() / 1e6 - preprocessing_start_time
            )
            self.epistemic_state["preprocessing_done"] = True

            # INFO-level logging for successful preprocessing completion
            logger.info(
                "Belief base preprocessing completed successfully",
                extra={
                    "preprocessing_time_ms": self.epistemic_state["preprocessing_time"],
                    "belief_base_name": self.epistemic_state["belief_base"].name,
                    "inference_system": self.epistemic_state["inference_system"],
                    "timeout_used": preprocessing_timeout,
                    "conditionals_count": len(
                        self.epistemic_state["belief_base"].conditionals
                    ),
                },
            )

        except TimeoutError:
            self.epistemic_state["preprocessing_time"] = preprocessing_timeout * 1000
            self.epistemic_state["preprocessing_timed_out"] = True

            # INFO-level logging for preprocessing timeout
            logger.info(
                "Belief base preprocessing timed out",
                extra={
                    "preprocessing_timeout": preprocessing_timeout,
                    "partial_preprocessing_time_ms": self.epistemic_state[
                        "preprocessing_time"
                    ],
                    "belief_base_name": self.epistemic_state["belief_base"].name,
                    "inference_system": self.epistemic_state["inference_system"],
                },
            )
        except Exception as e:
            raise e

    """
    General inference wrapper method. Selects kind (single/multi) of inference to perform.

    Context:
        Wraps single/multi inference methods.

    Parameters:
        Conditional dictionay, timeout in s and boolen indication if parallel inferences are to be performed.

    Returns:
        result dictionary mapping query string -> (index, result, timed_out, time_ms)
    """

    def inference(
        self,
        queries: dict[int, Conditional],
        timeout: int,
        multi_inference: bool,
    ) -> dict[str, tuple[int, bool, bool, float]]:
        """
        Run inference over a set of queries.

        Parameters
        ----------
        queries : dict
            Mapping from index to ``Conditional`` queries.
        timeout : int
            Per-query timeout in seconds. If 0, no timeout is enforced.
        multi_inference : bool
            If True, use parallel evaluation where possible.

        Returns
        -------
        dict
            A mapping ``{str(query): (index, result, timed_out, time_ms)}``.
        """
        # INFO-level logging for inference operation start
        logger.info(
            "Starting inference operations",
            extra={
                "query_count": len(queries),
                "timeout": timeout,
                "multi_inference": multi_inference,
                "inference_system": self.epistemic_state["inference_system"],
                "belief_base_name": self.epistemic_state["belief_base"].name,
                "preprocessing_completed": self.epistemic_state["preprocessing_done"],
            },
        )

        if (
            not self.epistemic_state["preprocessing_done"]
            and not self.epistemic_state["preprocessing_timed_out"]
        ):
            raise Exception("preprocess belief_base before running inference")
        if self.epistemic_state["preprocessing_timed_out"]:
            result_dict: dict[str, tuple[int, bool, bool, float]] = {
                str(q): (i, False, False, 0.0) for i, q in queries.items()
            }
        elif multi_inference:
            result_dict = self.multi_inference(queries, timeout)
        else:
            result_dict = self.single_inference(queries, timeout)

        # INFO-level logging for inference operation completion
        successful_queries = sum(1 for result in result_dict.values() if not result[2])
        timed_out_queries = len(queries) - successful_queries
        total_inference_time = sum(result[3] for result in result_dict.values())

        logger.info(
            "Inference operations completed",
            extra={
                "query_count": len(queries),
                "successful_queries": successful_queries,
                "timed_out_queries": timed_out_queries,
                "total_inference_time_ms": total_inference_time,
                "average_query_time_ms": total_inference_time / len(queries)
                if queries
                else 0,
                "multi_inference": multi_inference,
                "inference_system": self.epistemic_state["inference_system"],
                "weakly": self.epistemic_state["weakly"],
            },
        )
        return result_dict

    """
    Singular inference wrapper method. Handles timeout and measures time.


    Context:
        Wraps abstract _inference() method in a way that multiple inferences are performed sequentially only.
        Called by inferene().

    Parameters:
        Conditional dictionay, timeout in seconds.

    Returns:
        result dictionay
    """

    def single_inference(
        self, queries: dict[int, Conditional], timeout: int
    ) -> dict[str, tuple[int, bool, bool, float]]:
        """
        Evaluate queries sequentially.

        Parameters
        ----------
        queries : dict
            Mapping from index to ``Conditional`` queries.
        timeout : int
            Per-query timeout in seconds. If 0, no timeout is enforced.

        Returns
        -------
        dict
            A result mapping ``{str(query): (index, result, timed_out, time_ms)}``.
        """
        result_dict: dict[str, tuple[int, bool, bool, float]] = {}
        for index, query in queries.items():
            deadline = Deadline.from_duration(timeout) if timeout else None
            try:
                start_time = perf_counter_ns() / 1e6
                result = self.general_inference(query, deadline=deadline)
                time = perf_counter_ns() / 1e6 - start_time
                result_dict[str(query)] = (index, result, False, time)
            except TimeoutError:
                result_dict[str(query)] = (
                    index,
                    False,
                    True,
                    float(timeout * 1000),
                )
            except Exception as e:
                raise e
        return result_dict

    """
    Parallel inference wrapper method.

    Context:
        Wraps _multi_inference_worker() method in a way that multiple inferences are performed in parallel
        if possible and sequentially only in parallel capacity exhausted. Called by inference().

    Parameters:
        Conditional dictionay, timeout in seconds.

    Returns:
        result dictionay
    """

    def multi_inference(
        self, queries: dict[int, Conditional], timeout: int
    ) -> dict[str, tuple[int, bool, bool, float]]:
        """
        Evaluate queries in parallel using multiprocessing.

        Parameters
        ----------
        queries : dict
            Mapping from index to ``Conditional`` queries.
        timeout : int
            Per-query timeout in seconds. If 0, no timeout is enforced.

        Returns
        -------
        dict
            A result mapping ``{str(query): (index, result, timed_out, time_ms)}``.
        """
        indices = queries.keys()

        with mp.Manager() as manager:
            # Shared dict across processes. Treat as a generic mutable mapping for typing.
            mp_return_dict = cast(
                MutableMapping[int, tuple[int, bool, bool, float]],
                manager.dict(),
            )
            processes: list[tuple[mp.Process, int, Conditional]] = []

            for i in indices:
                query = queries[i]
                p = mp.Process(
                    target=self._multi_inference_worker,
                    args=(i, query, mp_return_dict, timeout),
                )
                processes.append((p, i, query))
                p.start()

            for p, i, query in processes:
                p.join(timeout + 10)
                if p.is_alive():
                    p.terminate()
                    p.join()  # Ensure the process has terminated
                    mp_return_dict[processes.index((p, i, query))] = (
                        i,
                        False,
                        True,
                        0.0,
                    )

            # results = [mp_return_dict[i] if i in return_dict else (str(q), (i, False, True, 0))  for i, q in queries.items()]
            result_dict: dict[str, tuple[int, bool, bool, float]] = {
                str(q): mp_return_dict[i]
                if i in mp_return_dict
                else (i, False, True, float(timeout * 1000))
                for i, q in queries.items()
            }
            return result_dict

    """
    Inference wrapper method. Handles timeout and measures time.


    Context:
        Wraps abstract _inference() method. Called by multi_inference().

    Parameters:
        Conditional dictionay, timeout in seconds.

    Side Effects:
        result dictionay
    """

    def _multi_inference_worker(
        self,
        index: int,
        query: Conditional,
        mp_return_dict: MutableMapping[int, tuple[int, bool, bool, float]],
        timeout: int,
    ) -> None:
        """
        Worker function used by ``multi_inference``.

        Parameters
        ----------
        index : int
            Index of the query.
        query : Conditional
            Query to evaluate.
        mp_return_dict : dict
            Multiprocessing shared dict to write results into.
        timeout : int
            Timeout in seconds.
        """
        deadline = Deadline.from_duration(timeout) if timeout else None
        try:
            start_time = perf_counter_ns() / 1e6
            result = self.general_inference(query, deadline=deadline)
            time = perf_counter_ns() / 1e6 - start_time
            mp_return_dict[index] = (index, result, False, float(time))
        except TimeoutError:
            mp_return_dict[index] = (index, False, True, float(timeout * 1000))
        except Exception as e:
            raise e

    def general_inference(
        self,
        query: Conditional,
        weakly: bool | None = None,
        deadline: Deadline | None = None,
    ) -> bool:
        """
        Run the concrete inference implementation with quick unsatisfiability checks.

        Parameters
        ----------
        query : Conditional
            Query to evaluate.
        weakly : bool, optional
            Whether to use weak semantics; defaults to epistemic state's setting.

        Returns
        -------
        bool
            True if the conditional is entailed under the configured operator.
        """
        if weakly is None:
            weakly = bool(self.epistemic_state.get("weakly", False))

        if is_unsat(query.antecedence) or is_unsat(
            And(query.antecedence, Not(query.consequence))
        ):
            logger.debug("general_inference query selffullfilling")
            return True
        else:
            return self._inference(query, weakly, deadline)

    @abstractmethod
    def _inference(
        self, query: Conditional, weakly: bool, deadline: Deadline | None
    ) -> bool:
        """Concrete inference implementation for a single query."""

    @abstractmethod
    def _preprocess_belief_base(self, weakly: bool, deadline: Deadline | None) -> None:
        """Concrete preprocessing implementation for the selected operator."""
