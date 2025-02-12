from inference.inference import Inference
from inference.conditional import Conditional
from inference.conditional_z3 import Conditional_z3
from inference.consistency_sat import consistency
from z3 import Optimize, z3, unsat, Or, is_true, unknown
from warnings import warn
from time import process_time

from pysmt.shortcuts import Solver, Not, is_unsat, And


def makeOptimizer() -> Optimize:
    opt = z3.Optimize()
    opt.set(priority='pareto')
    opt.add_soft(z3.BoolVal(True), id ="dummy1")
    opt.add_soft(z3.BoolVal(True), id ="dummy2")
    return opt

class LexInfZ3(Inference):
    """
    Implementation of _preprocess_belief_base() method of inference interface/abstract class. 
    Calculates z partition.

    Context:
        Called before inference on queries can be performed.

    Side Effects:
        partition in epistemic_state
    """
    def _preprocess_belief_base(self) -> None:
        partition, _ = consistency(self.epistemic_state['belief_base'], self.epistemic_state['smt_solver'])
        if not partition: warn('belief base inconsistent')
        self.epistemic_state['partition'] = []
        for part in partition: # type: ignore
            translated_part = []
            for conditional in part:
                translated_condtional = Conditional_z3.translate_from_existing(conditional)
                translated_part.append(translated_condtional)
            self.epistemic_state['partition'].append(translated_part)
    
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
        #self._translation_start()
        query_z3 = Conditional_z3.translate_from_existing(query)
        #self._translation_end()
        opt_v = makeOptimizer()
        opt_v.set(timeout=int(1000*(self.epistemic_state['kill_time'] - process_time())))
        opt_f = makeOptimizer()
        opt_f.set(timeout=int(1000*(self.epistemic_state['kill_time'] - process_time())))
        result = self._rec_inference(opt_v, opt_f, len(self.epistemic_state['partition']) -1, query_z3)
        #self._inference_end()
        return result
    
    """
    Recursive part of inference algorithm.

    Context:
        Called by _inference().

    Parameters:
        Optimizer (pmaxsat_solver) object, partition_index integer, query conditional_z3

    Returns:
        result of inference as bool 
    """
    def _rec_inference(self, opt_v: Optimize, opt_f: Optimize, partition_index: int, query: Conditional) -> bool:
        assert type(self.epistemic_state['partition']) == list
        part = self.epistemic_state['partition'][partition_index]
        opt_v.push()
        opt_v.add(query.make_A_then_B())
        xi_i_set = self.get_all_xi_i(opt_v, part)
        opt_v.pop()
        opt_f.push()
        opt_f.add(query.make_A_then_not_B())
        xi_i_prime_set = self.get_all_xi_i(opt_f, part)
        opt_f.pop()
        #print(f'xi_i_set {xi_i_set}')
        #print(f'xi_i_prime_set {xi_i_prime_set}')
        if not xi_i_set:
            #print('no falsification mcs')
            return False
        if not xi_i_prime_set:
            #print('no verification mcs')
            return True
        
        v = min([len(s) for s in xi_i_set])
        f = min([len(s) for s in xi_i_prime_set])
        if f < v:
            return False
        if v < f:
            return True
        for xi_i in [s for s in xi_i_set if len(s) == v]:
            for xi_i_prime in [s for s in xi_i_prime_set if len(s) == f]:
                if partition_index == 0:
                    return False
                opt_v.push()
                opt_f.push()
                [opt_v.add(c.make_A_then_not_B()) for c in xi_i]
                [opt_v.add(c.make_A_then_not_B() == False) for c in part if c not in xi_i]
                [opt_f.add(c.make_A_then_not_B()) for c in xi_i_prime]
                [opt_f.add(c.make_A_then_not_B() == False) for c in part if c not in xi_i_prime]
                result = self._rec_inference(opt_v, opt_f, partition_index -1, query)
                opt_v.pop()
                opt_f.pop()
                if result == False:
                    return False
        return True


    """
    Minimal Correction Subset Calculation

    Context:
        Called by _rec_inference()

    Parameters:
        Optimizer (pmaxsat_solver) object, part of partition as list

    Returns:
        Minimal Correction Subset of negated falsified conditionals in part of partition 
        given hard constraint already contained in optimizer

    """
    def get_all_xi_i(self, opt: Optimize, part: list[Conditional]) -> set:
        xi_i_set = set() 
        for conditional in part:
            opt.add_soft(conditional.make_A_then_not_B() == False)
        while True:
            if self.epistemic_state['kill_time'] and process_time() > self.epistemic_state['kill_time']:
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

"""
Checks if any element of set A is subset of all elements in set B

Context:
    Called by _rec_inference to make decisions about expanding searchtree

Parameters:
    Two sets of sets

Returns:
    decision as bool
"""
def any_subset_of_all(A: set , B: set) -> bool:
    return all(any(a.issubset(b) for a in A) for b in B)
