# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging

# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import Not

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from inference.inference import Inference
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from inference.belief_base import BeliefBase

from infocf import get_logger

logger = get_logger(__name__)


class PEntailment(Inference):
    
 
    def _preprocess_belief_base(self) -> None:
        self.epistemic_state['preprocessing_done'] = True


    def _inference(self, query: Conditional) -> bool:
        belief_base = self.epistemic_state['belief_base']
        solver_name = self.epistemic_state['smt_solver']
        conditionals = belief_base.conditionals.copy() 
        falsified_query = Conditional(Not(query.consequence), query.antecedence, None)
        
        conditionals[0] = falsified_query
        name = f'{belief_base.name}_queried'
        belief_base = BeliefBase(belief_base.signature, conditionals, name)
        partition, _ = consistency(belief_base, solver=solver_name)
        return type(partition) != list
