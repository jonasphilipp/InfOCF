"""
P-Entailment Inference Operator

A conditional (B|A) is p-entailed by Delta iff (B|A) holds
in every preferential model of Delta.

For weakly consistent belief bases, the extended Pinf algorithm is used:
check if nf(Delta'_inf) union {A} is unsatisfiable, where nf computes the
material counterpart {A -> B | (B|A) in Delta}.
"""

from pysmt.shortcuts import Not, Solver

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from inference.deadline import Deadline
from inference.inference import Inference
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class PEntailment(Inference):
    """P-entailment inference operator using SAT-based consistency checking."""

    def _preprocess_belief_base(self, weakly: bool, deadline: Deadline | None) -> None:
        self.epistemic_state["preprocessing_done"] = True

    def _inference(
        self, query: Conditional, weakly: bool, deadline: Deadline | None
    ) -> bool:
        """
        Check if query is p-entailed.

        Standard mode (weakly=False): check if Delta union {(not B|A)} is
        strongly inconsistent.

        Extended mode (weakly=True, Pinf): compute tolerance partition of
        Delta union {(not B|A)}, then check if nf(last_layer) union {A}
        is unsatisfiable.
        """
        belief_base = self.epistemic_state["belief_base"]
        solver_name = self.epistemic_state["smt_solver"]
        conditionals = belief_base.conditionals.copy()

        # falsified query: (not B|A)
        falsified_query = Conditional(Not(query.consequence), query.antecedence, None)
        conditionals[0] = falsified_query
        extended_bb = BeliefBase(
            belief_base.signature, conditionals, f"{belief_base.name}_queried"
        )

        if not weakly:
            partition, _ = consistency(extended_bb, solver=solver_name, weakly=False)
            return partition is False

        # Pinf algorithm for weakly consistent bases
        partition, _ = consistency(extended_bb, solver=solver_name, weakly=True)
        if partition is False:
            return True

        # check if nf(last_layer) union {query.antecedence} is unsatisfiable
        last_layer = partition[-1]
        with Solver(name=solver_name) as solver:
            for c in last_layer:
                solver.add_assertion(c.make_not_A_or_B())
            solver.add_assertion(query.antecedence)
            return not solver.solve()
