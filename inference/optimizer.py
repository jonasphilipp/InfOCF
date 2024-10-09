from time import process_time
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
from inference.epistemic_state import EpistemicStateWCNF
from abc import ABC, abstractmethod

    

class Optimizer(ABC):
    epistemic_state: EpistemicStateWCNF


    def __init__(self, epistemic_state: EpistemicStateWCNF):
        self.epistemic_state = epistemic_state

    @abstractmethod
    def minimal_correction_subsets(self, wcnf: WCNF, ignore_index: int = 0):
        return list()


    """
    Takes model and returns all IDs of CNFs in notAorBs (i.e. Not(A, Not(B))) that are not satisfied 
    by the model

    Context:
        Helper function called by compile_constraint and compile_and_encode_query

    Parameters:
        RC2 model; cost of the model; ID of CNF in notAorBs to be ignored (important to implement 
        the 'i!=j, AB[i]/notAB[i], notAorB[j]' requirement in compile_constraint)

    Returns:
        Set of IDs
    """
    def get_violated_conditional(self, model: list[int], cost: int, ignore: int) -> set[int]:
        violated = set()
        if cost > 0:
            counter = 0
            for index, conditional in self.epistemic_state._notAorBs.items():
                if index == ignore:
                    continue
                for clause in conditional:
                    if not any(x in clause for x in model):
                        counter += 1
                        violated.add(index)
                    if counter == cost:
                        return violated
        return violated

    """
    Takes indices of violated CNFs and creates new CNF that can be added as hard constraint to the 
    solver. Based on the idea of restraining the solver from violating the same conjuction of CNFs 
    again.

    Context:
        Helper function called by compile_constraint in order to add new hard constraint to solver
        and make solver solve for different possible world

    Parameters:
        set of indices of unsatisfied CNFs in notAorBs

    Returns:
        int CNF equivalent to disjunction of all CNFs referred to by input indices
    """ 
    def exclude_violated(self, violated: set[int]) -> list[list[int]]:
        return_constraints = []
        helper_variables_clause = []

        for index in violated:
            id = self.epistemic_state._pool.id(index)
            for clause in self.epistemic_state._notAorBs[index]:
                new_clause = clause[:]
                new_clause.append(id * (-1))
                return_constraints.append(new_clause)
        
            helper_variables_clause.append(id)
        return_constraints.append(helper_variables_clause)
        return return_constraints


"""
Removes supersets and converts sets to lists

Context:
    Helper function called by compile_constraint 

Parameters:
    list of sets (some sets might be supersets of other sets)

Returns:
    lists of lists (none of the inner lists will be a superset of other inner list)
"""
def remove_supersets(lst_of_sets: list[set[int]]) -> list[list[int]]:
    lst_of_sets = sorted(lst_of_sets, key=len)
    filtered = []

    for a in lst_of_sets:
        is_superset = False
        for b in filtered:
            if b.issubset(a):
                is_superset = True
                break
        if not is_superset:
            filtered.append(a)

    return [list(s) for s in filtered]


class OptimizerRC2(Optimizer):
    def minimal_correction_subsets(self, wcnf: WCNF, ignore_index: int = 0):
        xMins = []
        sat_solver = self.epistemic_state.optimizer[4:]
        if not sat_solver: sat_solver = 'g3'
        with RC2(wcnf, solver=sat_solver) as rc2:
            while True:
                if process_time() > self.epistemic_state._kill_time:
                    raise TimeoutError

                model = rc2.compute()
                
                if model == None:
                    break
                
                cost = rc2.cost
                
                violated = self.get_violated_conditional(model, cost, ignore_index)
                
                if not violated:
                    xMins.append(violated)
                    break
                
                xMins.append(violated)
                clauses_to_add = self.exclude_violated(violated)

                [rc2.add_clause(clause) for clause in clauses_to_add]
        
        xMins_lst = remove_supersets(xMins)
        return xMins_lst


def create_optimizer(epistemic_state: EpistemicStateWCNF) -> Optimizer:
    if epistemic_state.optimizer.startswith('rc2'):
        optimizer = OptimizerRC2(epistemic_state)
    else:
        Exception('no correct optimizer provided')
    return optimizer #type: ignore
