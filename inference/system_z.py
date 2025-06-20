# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from inference.inference import Inference
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from warnings import warn
from pysmt.shortcuts import Solver, Not, is_unsat, And
from time import process_time

from infocf import get_logger

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
    def _preprocess_belief_base(self) -> None:
            partition, _ = consistency(self.epistemic_state['belief_base'], solver=self.epistemic_state['smt_solver'])
            if not partition: warn('belief base inconsistent')
            self.epistemic_state['partition'] = partition #type: ignore

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
    def _inference(self, query: Conditional) -> bool:
        assert self.epistemic_state['partition'], 'belief_base inconsistent' 
        solver = Solver(name=self.epistemic_state['smt_solver'])
        result = self._rec_inference(solver, len(self.epistemic_state['partition']) -1, query) # type: ignore
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
    def _rec_inference(self, solver: Solver, partition_index: int, query: Conditional) -> bool: #type: ignore
        if self.epistemic_state['kill_time'] and process_time() > self.epistemic_state['kill_time']:
            raise TimeoutError
        assert type(self.epistemic_state['partition']) == list
        part = self.epistemic_state['partition'][partition_index]
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
            return self._rec_inference(solver, partition_index -1, query)
        return True

