from inference.inference import Inference
from inference.tseitin_transformation import TseitinTransformation
from inference.consistency_sat import consistency_indices
from inference.optimizer import Optmizer
from inference.conditional import Conditional
from inference.epistemic_state import EpistemicStateW
from inference.optimizer import Optmizer
from z3 import unsat, Or, is_true
from warnings import warn
from pysat.formula import WCNF

class SystemW(Inference):

    def _preprocess_belief_base(self) -> None:
        self.epistemic_state._partition, _ = consistency_indices(self.epistemic_state._belief_base, self.epistemic_state.solver)
        if not self.epistemic_state._partition: warn('belief base inconsistent')
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        tseitin_transformation.belief_base_to_cnf(False, True, True)
    
    def _inference(self, query) -> bool:
        #self._inference_start()
        assert type(self.epistemic_state) == EpistemicStateW, "Please use compatible epistemic state"
        #self._translation_start()
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        translated_query = tseitin_transformation.query_to_cnf(query)
        self.epistemic_state._ABs[0] = translated_query[0]
        self.epistemic_state._AnotBs[0] = translated_query[1]
        wcnf = WCNF()
        result = self._rec_inference(wcnf ,len(self.epistemic_state._partition) -1)
        #self._inference_end()
        return result

    def _rec_inference(self, hard_constraints, partition_index):
        assert type(self.epistemic_state._partition) == list
        part = self.epistemic_state._partition[partition_index]
        wcnf = hard_constraints.copy()
        for index in part:
            softc = self.epistemic_state._notAorBs[index]
            [wcnf.append(s, weight=1) for s in softc]
        wcnf_prime = wcnf.copy()
        [wcnf.append(c) for c in self.epistemic_state._ABs[0]]
        [wcnf_prime.append(c) for c in self.epistemic_state._AnotBs[0]]
        optimizer = Optmizer(self.epistemic_state)
        xi_i_list = optimizer.minimal_correction_subsets(wcnf)
        xi_i_prime_list = optimizer.minimal_correction_subsets(wcnf_prime)
        xi_i_set = frozenset([frozenset(l) for l in xi_i_list])
        xi_i_prime_set = frozenset([frozenset(l) for l in xi_i_prime_list])
        if not any_subset_of_all(xi_i_set, xi_i_prime_set):
            return False
        for xi_i in xi_i_set & xi_i_prime_set:
            if partition_index == 0:
                return False
            hard_constraints_new = hard_constraints.copy()
            for i in xi_i:
                [hard_constraints_new.append(c) for c in self.epistemic_state._AnotBs[i]]
            for i in frozenset(part) - xi_i:
                [hard_constraints_new.append(c) for c in self.epistemic_state._notAorBs[i]]
            result = self._rec_inference(hard_constraints_new, partition_index -1)
            if result == False:
                return False
        return True

# Function to extract 
def get_all_xi_i(opt, part: list[Conditional]):
    xi_i_set = set() 
    for conditional in part:
        opt.add_soft(conditional.make_A_then_not_B() == False)
    while True:
        if opt.check() == unsat:
           return xi_i_set
        m = opt.model()
        xi_i = frozenset([c for c in part if is_true(m.eval(c.make_A_then_not_B()))])
        xi_i_set.add(xi_i)
        if xi_i == frozenset(): 
            return xi_i_set
        opt.add(Or([c.make_A_then_not_B() == False for c in xi_i]))
 
def any_subset_of_all(A, B):
    return all(any(a.issubset(b) for a in A) for b in B)
