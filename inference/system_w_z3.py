from inference.inference import Inference
from inference.conditional import Conditional
from inference.conditional_z3 import Conditional_z3
from inference.epistemic_state import EpistemicStateZ
from inference.consistency_sat import consistency
from z3 import z3, unsat, Or, is_true, unknown
from warnings import warn
from time import process_time
#from optimizer_z3 import Optimizer

def makeOptimizer():
    opt = z3.Optimize()
    opt.set(priority='pareto')
    opt.add_soft(z3.BoolVal(True), id ="dummy1")
    opt.add_soft(z3.BoolVal(True), id ="dummy2")

    #z3.set_param(verbose=1)
    return opt

class SystemWZ3(Inference):

    def _preprocess_belief_base(self) -> None:
        partition, _ = consistency(self.epistemic_state._belief_base, self.epistemic_state.solver)
        if not partition: warn('belief base inconsistent')
        self.epistemic_state._partition = []
        for part in partition: # type: ignore
            translated_part = []
            for conditional in part:
                translated_condtional = Conditional_z3.translate_from_existing(conditional)
                translated_part.append(translated_condtional)
            self.epistemic_state._partition.append(translated_part)
    
    def _inference(self, query) -> bool:
        #self._inference_start()
        assert type(self.epistemic_state) == EpistemicStateZ, "Please use compatible epistemic state"
        #self._translation_start()
        query_z3 = Conditional_z3.translate_from_existing(query)
        #self._translation_end()
        opt = makeOptimizer()
        opt.set(timeout=int(1000*(self.epistemic_state._kill_time - process_time())))
        result = self._rec_inference(opt, len(self.epistemic_state._partition) -1, query_z3)
        #self._inference_end()
        return result

    def _rec_inference(self, opt, partition_index, query):
        assert type(self.epistemic_state._partition) == list
        part = self.epistemic_state._partition[partition_index]
        opt.push()
        opt.add(query.make_A_then_B())
        xi_i_set = self.get_all_xi_i(opt, part)
        opt.pop()
        opt.push()
        opt.add(query.make_A_then_not_B())
        xi_i_prime_set = self.get_all_xi_i(opt, part)
        opt.pop()
        if not any_subset_of_all(xi_i_set, xi_i_prime_set):
            return False
        for xi_i in xi_i_set & xi_i_prime_set:
            if partition_index == 0:
                return False
            opt.push()
            [opt.add(c.make_A_then_not_B()) for c in xi_i]
            [opt.add(c.make_A_then_not_B() == False) for c in part if c not in xi_i]
            result = self._rec_inference(opt, partition_index -1, query)
            opt.pop()
            if result == False:
                return False
        return True

    # Function to extract 
    def get_all_xi_i(self, opt, part: list[Conditional]):
        xi_i_set = set() 
        for conditional in part:
            opt.add_soft(conditional.make_A_then_not_B() == False)
        while True:
            if process_time() > self.epistemic_state._kill_time:
                raise TimeoutError
            check = opt.check()
            if check == unsat:
               return xi_i_set
            m = opt.model()
            xi_i = frozenset([c for c in part if is_true(m.eval(c.make_A_then_not_B()))])
            xi_i_set.add(xi_i)
            if xi_i == frozenset(): 
                return xi_i_set
            opt.add(Or([c.make_A_then_not_B() == False for c in xi_i]))
 
def any_subset_of_all(A, B):
    return all(any(a.issubset(b) for a in A) for b in B)
