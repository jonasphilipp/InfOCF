# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import multiprocessing as mp
from abc import ABC, abstractmethod
from time import perf_counter, perf_counter_ns

from pysmt.shortcuts import And, Not, is_unsat

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class Inference(ABC):
    """
    Context:
        Abstract class intitialization inherited by implementing classes

    Parameters:
        Initialized epistemic_state
    """

    def __init__(self, epistemic_state: dict) -> None:
        self.epistemic_state = epistemic_state

    """
    Preprocessing wrapper method. Handles timeout and measures time.

    Context:
        Wraps abstract _preprocess_belief_base method.

    Parameters:
        Timeout in seconds.

    Side Effects:
        kill_time, preprocessing_time and preprocessing_timed_out in epistemic_state
    """

    def preprocess_belief_base(self, preprocessing_timeout: int) -> None:
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
            self.epistemic_state["belief_base"], self.epistemic_state["smt_solver"]
        )
        assert cons != False, "belief base inconsistent"
        if preprocessing_timeout:
            self.epistemic_state["kill_time"] = preprocessing_timeout + perf_counter()
        else:
            self.epistemic_state["kill_time"] = 0
        try:
            preprocessing_start_time = perf_counter_ns() / 1e6
            self._preprocess_belief_base(self.epistemic_state["weakly"])
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

    Side Effects:
        result_dict in epistemic_state
    """

    def inference(self, queries: dict, timeout: int, multi_inference: bool) -> None:
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
            Exception("preprocess belief_base before running inference")
        if self.epistemic_state["preprocessing_timed_out"]:
            self.epistemic_state["result_dict"].update(
                {str(q): (i, False, False, 0) for i, q in queries.items()}
            )
        elif multi_inference:
            self.epistemic_state["result_dict"].update(
                self.multi_inference(queries, timeout)
            )
        else:
            self.epistemic_state["result_dict"].update(
                self.single_inference(queries, timeout)
            )

        # INFO-level logging for inference operation completion
        successful_queries = sum(
            1
            for result in self.epistemic_state["result_dict"].values()
            if not result[2]
        )
        timed_out_queries = len(queries) - successful_queries
        total_inference_time = sum(
            result[3] for result in self.epistemic_state["result_dict"].values()
        )

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

    def single_inference(self, queries: dict, timeout: int) -> dict:
        result_dict = dict()
        for index, query in queries.items():
            if timeout:
                self.epistemic_state["kill_time"] = timeout + perf_counter()
            else:
                self.epistemic_state["kill_time"] = 0
            try:
                start_time = perf_counter_ns() / 1e6
                result = self.general_inference(query)
                time = perf_counter_ns() / 1e6 - start_time
                result_dict[str(query)] = (index, result, False, time)
            except TimeoutError:
                result_dict[str(query)] = (index, False, True, timeout * 1000)
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

    def multi_inference(self, queries: dict, timeout: int) -> dict:
        indices = queries.keys()

        with mp.Manager() as manager:
            mp_return_dict = manager.dict()
            processes = []

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
                        query,
                        (i, False, True, 0),
                    )

            # results = [mp_return_dict[i] if i in return_dict else (str(q), (i, False, True, 0))  for i, q in queries.items()]
            result_dict = {
                str(q): mp_return_dict[i]
                if i in mp_return_dict
                else (i, False, True, timeout)
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
        self, index: int, query: Conditional, mp_return_dict: dict, timeout: int
    ) -> None:
        if timeout:
            self.epistemic_state["kill_time"] = timeout + perf_counter()
        else:
            self.epistemic_state["kill_time"] = 0
        try:
            start_time = perf_counter_ns() / 1e6
            result = self.general_inference(query)
            time = perf_counter_ns() / 1e6 - start_time
            mp_return_dict[index] = (index, result, False, time)
        except TimeoutError:
            mp_return_dict[index] = (index, False, True, timeout * 1000)
        except Exception as e:
            raise e

    def general_inference(self, query: Conditional, weakly: bool = None):
        if weakly is None:
            weakly = self.epistemic_state.get("weakly", False)

        if is_unsat(query.antecedence) or is_unsat(
            And(query.antecedence, Not(query.consequence))
        ):
            logger.debug("general_inference query selffullfilling")
            return True
        elif is_unsat(And(query.antecedence, query.consequence)):
            logger.debug("general_inference query inconsistent")
            return False
        else:
            return self._inference(query, weakly)

    @abstractmethod
    def _inference(self, query: Conditional, weakly: bool) -> bool:
        pass

    @abstractmethod
    def _preprocess_belief_base(self, weakly: bool) -> None:
        pass
