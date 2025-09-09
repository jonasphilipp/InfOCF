# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from typing import Any

# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------
import pandas as pd
from pysmt.environment import get_env

from inference.belief_base import BeliefBase
from inference.c_inference import CInference
from inference.inference import Inference
from inference.lex_inf import LexInf
from inference.lex_inf_z3 import LexInfZ3
from inference.p_entailment import PEntailment
from inference.queries import Queries
from inference.system_w import SystemW
from inference.system_w_z3 import SystemWZ3
from inference.system_z import SystemZ
from infocf.log_setup import get_logger

logger = get_logger(__name__)

"""
Creates epistemic state dict. Everything we know or find out about a belief base and also some meta
information relevant to further operations is stored in the epistemic state dict.

Context:
    Called before any inference operations are performed to create data structure to store information.

Parameters:
    Parsed belief base, and strings declaring inference system, smt_solver and pmaxsat_solver.

Returns:
    Initialized epistemic state dict.
"""


def create_epistemic_state(
    belief_base: BeliefBase,
    inference_system: str,
    smt_solver: str,
    pmaxsat_solver: str,
    weakly: bool,
) -> dict[str, Any]:
    """
    Create and initialize the epistemic state structure.

    Parameters
    ----------
    belief_base : BeliefBase
        Parsed belief base.
    inference_system : str
        One of ``{"p-entailment", "system-z", "system-w", "c-inference", "lex_inf"}``.
    smt_solver : str
        SMT solver name (e.g., ``"z3"``).
    pmaxsat_solver : str
        MaxSAT solver name (ignored for p-entailment and system-z).
    weakly : bool
        Whether to use weak semantics where applicable.

    Returns
    -------
    dict
        Initialized epistemic state dictionary.
    """
    epistemic_state: dict[str, Any] = {}

    epistemic_state["belief_base"] = belief_base
    epistemic_state["inference_system"] = inference_system
    epistemic_state["smt_solver"] = smt_solver
    epistemic_state["pmaxsat_solver"] = pmaxsat_solver
    epistemic_state["preprocessing_done"] = False
    epistemic_state["preprocessing_timed_out"] = False
    epistemic_state["preprocessing_time"] = 0
    epistemic_state["weakly"] = weakly

    return epistemic_state


"""
Creates instance of an inference object specific to an inference system.

Context:
    Called before inferene operations are performed. Required to perform inferences over queries later on.

Parameters:
    Initialized epistemic state dict.

Returns:
    Instanciated inference object.
"""


def create_inference_instance(epistemic_state: dict[str, Any]) -> Inference:
    """
    Instantiate the concrete inference class based on the epistemic state.

    Parameters
    ----------
    epistemic_state : dict
        Epistemic state produced by ``create_epistemic_state``.

    Returns
    -------
    Inference
        Instantiated inference implementation.
    """
    inference_system = epistemic_state["inference_system"]

    # INFO-level logging for inference system initialization
    logger.info(
        "Initializing inference system",
        extra={
            "inference_system": inference_system,
            "smt_solver": epistemic_state["smt_solver"],
            "pmaxsat_solver": epistemic_state["pmaxsat_solver"],
            "belief_base_name": epistemic_state["belief_base"].name,
        },
    )

    if inference_system == "p-entailment":
        inference_instance = PEntailment(epistemic_state)
    elif inference_system == "system-z":
        inference_instance = SystemZ(epistemic_state)
    elif inference_system == "system-w":
        # this optimizer selection method is a placeholed and will be replaced
        if epistemic_state["pmaxsat_solver"] == "z3":
            inference_instance = SystemWZ3(epistemic_state)
            # DEBUG-level logging for Z3-specific system-w initialization
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug(
                    "Using Z3-based System W implementation",
                    extra={"pmaxsat_solver": "z3", "implementation": "SystemWZ3"},
                )
        else:
            inference_instance = SystemW(epistemic_state)
            # DEBUG-level logging for standard system-w initialization
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug(
                    "Using standard System W implementation",
                    extra={
                        "pmaxsat_solver": epistemic_state["pmaxsat_solver"],
                        "implementation": "SystemW",
                    },
                )
    elif inference_system == "c-inference":
        inference_instance = CInference(epistemic_state)
    elif inference_system == "lex_inf":
        if epistemic_state["pmaxsat_solver"] == "z3":
            inference_instance = LexInfZ3(epistemic_state)
            # DEBUG-level logging for Z3-specific lex_inf initialization
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug(
                    "Using Z3-based Lexicographic Inference implementation",
                    extra={"pmaxsat_solver": "z3", "implementation": "LexInfZ3"},
                )
        else:
            inference_instance = LexInf(epistemic_state)
            # DEBUG-level logging for standard lex_inf initialization
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug(
                    "Using standard Lexicographic Inference implementation",
                    extra={
                        "pmaxsat_solver": epistemic_state["pmaxsat_solver"],
                        "implementation": "LexInf",
                    },
                )
    else:
        logger.error(
            "Invalid inference system provided",
            extra={
                "inference_system": inference_system,
                "available_systems": [
                    "p-entailment",
                    "system-z",
                    "system-w",
                    "c-inference",
                    "lex_inf",
                ],
            },
        )
        raise Exception("no correct inference system provideid")

    # INFO-level logging for successful initialization
    logger.info(
        "Inference system initialized successfully",
        extra={
            "inference_system": inference_system,
            "instance_class": inference_instance.__class__.__name__,
            "smt_solver": epistemic_state["smt_solver"],
            "pmaxsat_solver": epistemic_state["pmaxsat_solver"],
        },
    )

    return inference_instance  # type: ignore


class InferenceOperator:
    epistemic_state: dict[str, Any]

    """
    Initializes InferenceOperator.

    Context:
        Called to automatically initialize and instanciate epistemic state and inference object.

    Parameters:
        Parsed belief base and stings declaring inference system, smt_solver and pmaxsat_solver.
    """

    def __init__(
        self,
        belief_base: BeliefBase,
        inference_system: str,
        smt_solver: str = "z3",
        pmaxsat_solver: str = "rc2",
        weakly: bool = False,
    ) -> None:
        """
        Initialize the high-level operator wrapper.

        Parameters
        ----------
        belief_base : BeliefBase
            Parsed belief base.
        inference_system : str
            Name of the inference system.
        smt_solver : str, default "z3"
            SMT solver backend.
        pmaxsat_solver : str, default "rc2"
            PMAX-SAT solver backend (unused for some operators).
        weakly : bool, default False
            Whether to use weak semantics where applicable.
        """
        inference_system = inference_system.lower()
        smt_solver = smt_solver.lower()
        if inference_system in ["p-entailment", "system-z"]:
            pmaxsat_solver = ""
        else:
            pmaxsat_solver = pmaxsat_solver.lower()
        available_solvers = get_env().factory.all_solvers().keys()
        assert (
            smt_solver in available_solvers
        ), f"only {available_solvers} are available as solver"
        self.epistemic_state = create_epistemic_state(
            belief_base, inference_system, smt_solver, pmaxsat_solver, weakly
        )

    """
    Performs inference.

    Context:
        Called to find out if (collection of) queries can be inferred from belief base under
        specific inference system.

    Parameters:
        Parsed queries object. Optional: Timeouts, queries name, boolean idicating if multiple
        inferences should be performed in parallel, decimal points to which time measurement results
        should be rounded to.

    Returns:
        Pandas data frame containing detailed information about the performed inference.
    """

    def inference(
        self,
        queries: Queries,
        total_timeout: int = 0,
        inference_timeout: int = 0,
        preprocessing_timeout: int = 0,
        queries_name: str = "",
        multi_inference: bool = False,
        decimals: int = 1,
    ) -> pd.DataFrame:
        """
        Run end-to-end inference over a set of queries and return a report.

        Parameters
        ----------
        queries : Queries
            Container of conditional queries.
        total_timeout : int, default 0
            Global timeout budget in seconds; 0 disables.
        inference_timeout : int, default 0
            Per-query timeout in seconds; 0 disables.
        preprocessing_timeout : int, default 0
            Preprocessing timeout in seconds; 0 disables.
        queries_name : str, default ""
            Optional label for this batch.
        multi_inference : bool, default False
            If True, attempt parallel evaluation.
        decimals : int, default 1
            Rounding precision for time metrics.

        Returns
        -------
        pandas.DataFrame
            A dataframe with per-query results and timing information.
        """
        if queries_name:
            queries.name = queries_name

        # INFO-level logging for batch operation start
        logger.info(
            "Starting inference batch processing",
            extra={
                "inference_system": self.epistemic_state["inference_system"],
                "smt_solver": self.epistemic_state["smt_solver"],
                "pmaxsat_solver": self.epistemic_state["pmaxsat_solver"],
                "query_count": len(queries.conditionals),
                "queries_name": queries.name,
                "belief_base_name": self.epistemic_state["belief_base"].name,
                "signature_size": len(self.epistemic_state["belief_base"].signature),
                "conditionals_count": len(
                    self.epistemic_state["belief_base"].conditionals
                ),
                "multi_inference": multi_inference,
                "total_timeout": total_timeout,
                "preprocessing_timeout": preprocessing_timeout,
                "inference_timeout": inference_timeout,
            },
        )

        columns = [
            "index",
            "result",
            "signature_size",
            "number_conditionals",
            "preprocessing_time",
            "inference_time",
            "preprocessing_timed_out",
            "inference_timed_out",
            "belief_base",
            "queries",
            "query",
            "inference_system",
            "smt_solver",
            "pmaxsat_solver",
        ]

        # Build an empty DataFrame with desired columns without relying on "columns=" typing quirks
        df = pd.DataFrame({c: [] for c in columns})

        inference_instance = create_inference_instance(self.epistemic_state)

        if total_timeout and preprocessing_timeout:
            preprocessing_timeout = min(total_timeout, preprocessing_timeout)
        elif total_timeout:
            preprocessing_timeout = total_timeout

        # INFO-level logging for preprocessing phase
        logger.info(
            "Starting preprocessing phase",
            extra={
                "preprocessing_timeout": preprocessing_timeout,
                "inference_system": self.epistemic_state["inference_system"],
            },
        )

        inference_instance.preprocess_belief_base(preprocessing_timeout)

        # INFO-level logging for preprocessing completion
        logger.info(
            "Preprocessing phase completed",
            extra={
                "preprocessing_time_ms": self.epistemic_state["preprocessing_time"],
                "preprocessing_timed_out": self.epistemic_state[
                    "preprocessing_timed_out"
                ],
                "preprocessing_done": self.epistemic_state["preprocessing_done"],
            },
        )

        if total_timeout and inference_timeout:
            inference_timeout = min(
                total_timeout - self.epistemic_state["preprocessing_time"] / 1000,
                inference_timeout,
            )
        elif total_timeout:
            inference_timeout = (
                total_timeout - self.epistemic_state["preprocessing_time"] / 1000
            )

        # INFO-level logging for query processing phase
        logger.info(
            "Starting query processing phase",
            extra={
                "inference_timeout": inference_timeout,
                "query_count": len(queries.conditionals),
                "multi_inference": multi_inference,
            },
        )

        results = inference_instance.inference(
            queries.conditionals, inference_timeout, multi_inference
        )

        # DEBUG-level logging for detailed results processing
        if logger.isEnabledFor(logging.DEBUG):
            successful_queries = sum(
                1 for result in results.values() if not result[2]
            )  # not timed out
            timed_out_queries = len(results) - successful_queries
            logger.debug(
                "Query processing completed - detailed breakdown",
                extra={
                    "total_queries": len(results),
                    "successful_queries": successful_queries,
                    "timed_out_queries": timed_out_queries,
                    "results_summary": {
                        str(k): {"result": v[1], "timed_out": v[2], "time_ms": v[3]}
                        for k, v in list(results.items())[:3]
                    },  # Sample first 3 for debug
                },
            )

        for index, query in enumerate(queries.conditionals.values()):
            query = str(query)
            df.at[index, "index"] = results[query][0]
            df.at[index, "result"] = results[query][1]
            df.at[index, "preprocessing_timed_out"] = self.epistemic_state[
                "preprocessing_timed_out"
            ]
            df.at[index, "preprocessing_time"] = round(
                self.epistemic_state["preprocessing_time"], decimals
            )
            df.at[index, "inference_timed_out"] = results[query][2]
            df.at[index, "inference_time"] = round(results[query][3], decimals)
            df.at[index, "inference_system"] = self.epistemic_state["inference_system"]
            df.at[index, "smt_solver"] = self.epistemic_state["smt_solver"]
            df.at[index, "pmaxsat_solver"] = self.epistemic_state["pmaxsat_solver"]
            df.at[index, "belief_base"] = self.epistemic_state["belief_base"].name
            df.at[index, "queries"] = queries.name
            df.at[index, "query"] = query
            df.at[index, "signature_size"] = len(
                self.epistemic_state["belief_base"].signature
            )
            df.at[index, "number_conditionals"] = len(
                self.epistemic_state["belief_base"].conditionals
            )

        # INFO-level logging for batch operation completion with performance summary
        total_inference_time = sum(
            results[str(q)][3] for q in queries.conditionals.values()
        )
        logger.info(
            "Inference batch processing completed",
            extra={
                "query_count": len(queries.conditionals),
                "preprocessing_time_ms": self.epistemic_state["preprocessing_time"],
                "total_inference_time_ms": round(total_inference_time, decimals),
                "preprocessing_timed_out": self.epistemic_state[
                    "preprocessing_timed_out"
                ],
                "inference_timeouts": sum(
                    1 for result in results.values() if result[2]
                ),
                "successful_queries": sum(
                    1 for result in results.values() if not result[2]
                ),
                "queries_name": queries.name,
                "belief_base_name": self.epistemic_state["belief_base"].name,
            },
        )

        return df
