from inference.inference import Inference
from inference.tseitin_transformation import TseitinTransformation
from inference.consistency_sat import consistency_indices
from inference.optimizer import create_optimizer
from inference.conditional import Conditional
from z3 import unsat, Or, is_true
from warnings import warn
from pysat.formula import WCNF

class SystemW(Inference):
    """
    Implementation of _preprocess_belief_base() method of inference interface/abstract class. 
    Calculates z partition.

    Context:
        Called before inference on queries can be performed.

    Side Effects:
        partition in epistemic_state
    """
    def _preprocess_belief_base(self) -> None:
        self.epistemic_state['partition'], _ = consistency_indices(self.epistemic_state['belief_base'], self.epistemic_state['smt_solver'])
        if not self.epistemic_state['partition']: warn('belief base inconsistent')
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        tseitin_transformation.belief_base_to_cnf(False, True, True)
   

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
        #self._inference_start()
        #self._translation_start()
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        translated_query = tseitin_transformation.query_to_cnf(query)
        self.epistemic_state['v_cnf_dict'][0] = translated_query[0]
        self.epistemic_state['f_cnf_dict'][0] = translated_query[1]
        wcnf = WCNF()
        result = self._rec_inference(wcnf ,len(self.epistemic_state['partition']) -1)
        #self._inference_end()
        return result

    
    """
    Recursive part of inference algorithm.

    Context:
        Called by _inference().

    Parameters:
        Set of hard_constraints in wcnf format, partition_index integer

    Returns:
        result of inference as bool 
    """
    def _rec_inference(self, hard_constraints: WCNF, partition_index: int) -> bool:
        assert type(self.epistemic_state['partition']) == list
        part = self.epistemic_state['partition'][partition_index]
        wcnf = hard_constraints.copy()
        for index in part:
            softc = self.epistemic_state['nf_cnf_dict'][index]
            [wcnf.append(s, weight=1) for s in softc]
        wcnf_prime = wcnf.copy()
        [wcnf.append(c) for c in self.epistemic_state['v_cnf_dict'][0]]
        [wcnf_prime.append(c) for c in self.epistemic_state['f_cnf_dict'][0]]
        optimizer = create_optimizer(self.epistemic_state)
        ignore = list(filter(lambda x: x != part, self.epistemic_state['partition']))
        xi_i_list = optimizer.minimal_correction_subsets(wcnf, ignore=ignore)
        xi_i_prime_list = optimizer.minimal_correction_subsets(wcnf_prime, ignore=ignore)
        xi_i_set = frozenset([frozenset(l) for l in xi_i_list])
        xi_i_prime_set = frozenset([frozenset(l) for l in xi_i_prime_list])
        if not any_subset_of_all(xi_i_set, xi_i_prime_set):
            return False
        for xi_i in xi_i_set & xi_i_prime_set:
            if partition_index == 0:
                return False
            hard_constraints_new = hard_constraints.copy()
            for i in xi_i:
                [hard_constraints_new.append(c) for c in self.epistemic_state['f_cnf_dict'][i]]
            for i in frozenset(part) - xi_i:
                [hard_constraints_new.append(c) for c in self.epistemic_state['nf_cnf_dict'][i]]
            result = self._rec_inference(hard_constraints_new, partition_index -1)
            if result == False:
                return False
        return True


"""
Checks if any element of set A is subset of all elements in set B

Context:
    Called by _rec_inference to make decisions about expanding searchtree

Parameters:
    Two sets of sets

Returns:
    decision as bool
"""
def any_subset_of_all(A: frozenset, B: frozenset) -> bool:
    return all(any(a.issubset(b) for a in A) for b in B)
