# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from time import perf_counter
from warnings import warn

from pysmt.shortcuts import Not, Solver

from inference.conditional import Conditional
from inference.consistency_sat import consistency
from inference.inference import Inference
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class SystemZ(Inference):
    """
    Implementation of _preprocess_belief_base() method of inference interface/abstract class.
    Calculates z partition.

    Context:
        Called before inference on queries can be performed.

    Side Effects:
        partition in epistemic_state
    """

    def _preprocess_belief_base(self, weakly: bool) -> None:
        partition, _ = consistency(
            self.epistemic_state["belief_base"],
            solver=self.epistemic_state["smt_solver"],
            weakly=weakly,
        )
        if not partition:
            warn("belief base inconsistent")
        self.epistemic_state["partition"] = partition  # type: ignore

    """
    Implementation of _inference() method of inference interface/abstract class.
    Performs actual inference.

    Context:
        Called to perform inference after preprocessing has been done. Calls recursive part of
        inference algorithm.

    Parameters:
        Query conditional

    Returns:
        result boolean
    """

    def _inference(self, query: Conditional, weakly: bool) -> bool:
        assert self.epistemic_state["partition"], "belief_base inconsistent"
        solver = Solver(name=self.epistemic_state["smt_solver"])
        if not weakly:
            result = self._rec_inference(
                solver, len(self.epistemic_state["partition"]) - 1, query
            )  # type: ignore
        else:
            taut_solver = Solver(name=self.epistemic_state["smt_solver"])
            taut_solver.add_assertion(query.antecedence)
            for c in self.epistemic_state["partition"][-1]:
                taut_solver.add_assertion(Not(c.make_not_A_or_B()))
            if not taut_solver.solve():
                return True
            result = self._rec_inference(
                solver, len(self.epistemic_state["partition"]) - 2, query
            )  # type: ignore

        return result

    """
    Recursive part of inference algorithm.

    Context:
        Called by _inference().

    Parameters:
        Solver object, partition_index integer, query conditional

    Returns:
        result of inference as bool
    """

    def _rec_inference(
        self, solver: Solver, partition_index: int, query: Conditional
    ) -> bool:  # type: ignore
        if (
            self.epistemic_state["kill_time"]
            and perf_counter() > self.epistemic_state["kill_time"]
        ):
            raise TimeoutError
        assert type(self.epistemic_state["partition"]) == list
        part = self.epistemic_state["partition"][partition_index]
        [solver.add_assertion(Not(c.make_A_then_not_B())) for c in part]
        solver.push()
        solver.add_assertion(query.make_A_then_B())
        v = solver.solve()
        solver.pop()
        solver.push()
        solver.add_assertion(query.make_A_then_not_B())
        f = solver.solve()
        solver.pop()

        if not v:
            return False

        if f:
            if partition_index == 0:
                return False
            return self._rec_inference(solver, partition_index - 1, query)
        return True
