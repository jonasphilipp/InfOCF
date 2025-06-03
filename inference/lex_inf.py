from inference.inference import Inference
from inference.tseitin_transformation import TseitinTransformation
from inference.consistency_sat import consistency_indices
from inference.optimizer import create_optimizer
from inference.conditional import Conditional
from warnings import warn
from pysat.formula import WCNF

class LexInf(Inference):
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
        wcnf_v = WCNF()
        wcnf_f = WCNF()
        [wcnf_v.append(c) for c in self.epistemic_state['v_cnf_dict'][0]]
        [wcnf_f.append(c) for c in self.epistemic_state['f_cnf_dict'][0]]
        result = self._rec_inference(wcnf_v, wcnf_f, len(self.epistemic_state['partition']) -1)
        #self._inference_end()
        return result

    
    """
    Recursive part of inference algorithm.

    Context:
        Called by _inference().

    Parameters:
        Two sets of hard_constraints in wcnf format, partition_index integer

    Returns:
        result of inference as bool 
    """
    def _rec_inference(self, hard_constraints_v: WCNF, hard_constraints_f: WCNF,  partition_index: int) -> bool:
        #print(partition_index)
        assert type(self.epistemic_state['partition']) == list
        part = self.epistemic_state['partition'][partition_index]
        #print(f'part: {part}')
        for index in part:
            softc = self.epistemic_state['nf_cnf_dict'][index]
            [hard_constraints_v.append(s, weight=1) for s in softc]
            [hard_constraints_f.append(s, weight=1) for s in softc]
        optimizer = create_optimizer(self.epistemic_state)
        ignore = [item for sublist in self.epistemic_state['partition'] if sublist != part for item in sublist]
        mcs_v = optimizer.minimal_correction_subsets(hard_constraints_v, ignore=ignore)
        mcs_f = optimizer.minimal_correction_subsets(hard_constraints_f, ignore=ignore)
        #print(f'mcs_v: {mcs_v}')
        #print(f'mcs_f: {mcs_f}')
        if not mcs_v:
            #print('minimal_correction_subsets not found for verification')
            return False
        if not mcs_f:
            #print('minimal_correction_subsets not found for falsification')
            return True
        min_len_v = min(len(xi) for xi in mcs_v)
        min_len_f = min(len(xi) for xi in mcs_f)
        min_mcs_v = [xi for xi in mcs_v if len(xi) == min_len_v]
        min_mcs_f = [xi for xi in mcs_f if len(xi) == min_len_f]
        
        if min_len_v < min_len_f:
            return True
        if min_len_f < min_len_v:
            return False
        for xi_v in min_mcs_v:
            for xi_f in min_mcs_f:
                if partition_index == 0:
                    return False
                hard_constraints_new_v = hard_constraints_v.copy()
                hard_constraints_new_f = hard_constraints_f.copy()
                for i in part:
                    if i in xi_v: 
                        [hard_constraints_new_v.append(c) for c in self.epistemic_state['f_cnf_dict'][i]]
                    else:
                        [hard_constraints_new_v.append(c) for c in self.epistemic_state['nf_cnf_dict'][i]]
                    if i in xi_f: 
                        [hard_constraints_new_f.append(c) for c in self.epistemic_state['f_cnf_dict'][i]]
                    else:
                        [hard_constraints_new_f.append(c) for c in self.epistemic_state['nf_cnf_dict'][i]]
                result = self._rec_inference(hard_constraints_new_v, hard_constraints_new_f, partition_index - 1)
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
