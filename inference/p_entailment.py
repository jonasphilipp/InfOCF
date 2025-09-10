"""
P-Entailment Inference Operator

This module implements the p-entailment inference operator for conditional belief bases.
P-entailment is the weakest form of inference in conditional logic and is based on
the principle that a conditional (B|A) is accepted if the belief base remains consistent
when the falsified conditional (~B|A) is added.
"""

# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import Not

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from inference.deadline import Deadline

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from inference.inference import Inference
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class PEntailment(Inference):
    """
    P-Entailment inference operator implementation.

    This class implements p-entailment using SAT-based consistency checking.

    Parameters
    ----------
    epistemic_state : dict
        Dictionary containing the belief base, solver configuration, and other
        inference parameters. Must contain keys:
        - 'belief_base': BeliefBase instance
        - 'smt_solver': str, name of SMT solver to use

    Attributes
    ----------
    epistemic_state : dict
        Internal state containing belief base and solver information

    Examples
    --------
    >>> from infocf import BeliefBase, PEntailment
    >>> # Create a simple belief base
    >>> signature = ['p', 'q', 'r']
    >>> conditionals = {0: Conditional(p, q, '(p|q)')}  # (p|q) means if p then q
    >>> bb = BeliefBase(signature, conditionals, 'example')
    >>> # Create p-entailment instance
    >>> epistemic_state = {'belief_base': bb, 'smt_solver': 'z3'}
    >>> inference = PEntailment(epistemic_state)
    >>> # Query whether (r|p) is entailed (is r accepted given p?)
    >>> result = inference.query('(r|p)')
    >>> print(f"Query result: {result}")
    """

    def _preprocess_belief_base(self, weakly: bool, deadline: Deadline | None) -> None:
        """
        Preprocess the belief base for p-entailment inference.

        For p-entailment, minimal preprocessing is required since the algorithm
        works directly with the original belief base. This method simply marks
        preprocessing as complete.

        Parameters
        ----------
        weakly : bool
            Whether to use weak consistency (unused in p-entailment)
        deadline : Deadline or None
            Timeout deadline (unused in p-entailment preprocessing)

        Notes
        -----
        P-entailment doesn't require complex preprocessing like other inference
        operators (e.g., System Z partitioning), so this method is minimal.
        """
        self.epistemic_state["preprocessing_done"] = True

    def _inference(
        self, query: Conditional, weakly: bool, deadline: Deadline | None
    ) -> bool:
        """
        Perform p-entailment inference for a single conditional query.

        Implements the core p-entailment algorithm by checking whether adding
        the falsified query (~B|A) to the belief base causes inconsistency.
        If inconsistency occurs, the original query (B|A) is accepted.

        Parameters
        ----------
        query : Conditional
            The conditional query to evaluate, of the form (B|A)
        weakly : bool
            Whether to use weak consistency (unused in p-entailment)
        deadline : Deadline or None
            Timeout deadline for the inference operation

        Returns
        -------
        bool
            True if the query is accepted (entailed), False otherwise

        Notes
        -----
        The algorithm creates a temporary belief base by adding the falsified
        conditional (~B|A) and checks its consistency. If the extended belief
        base is inconsistent, then the original conditional (B|A) must be true
        to restore consistency.

        The method uses the configured SMT solver to perform consistency checking.
        """
        belief_base = self.epistemic_state["belief_base"]
        solver_name = self.epistemic_state["smt_solver"]
        conditionals = belief_base.conditionals.copy()

        # Create falsified query: ~B|A (negation of consequence given antecedence)
        falsified_query = Conditional(Not(query.consequence), query.antecedence, None)

        # Add falsified query to belief base (temporarily)
        conditionals[0] = falsified_query
        name = f"{belief_base.name}_queried"
        extended_belief_base = BeliefBase(belief_base.signature, conditionals, name)

        # Check consistency of extended belief base
        partition, _ = consistency(extended_belief_base, solver=solver_name)

        # If partition is not a list, the belief base is inconsistent
        # This means the original query must be accepted to maintain consistency
        return type(partition) != list
