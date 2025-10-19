from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
import z3
import math
from inference.z3tools import *

def filtersubsets(k, J):
    return [q for q in k if all([(t in J) for t in q])]

def getOptimizer():
    opt = z3.Optimize()
    opt.set(priority='pareto')
    opt.set(maxsat_engine='rc2')
    return opt

class WeakCz3():

    def __init__(self,bb) -> None:
            partition, _ = consistency(bb, 'z3', weakly=True)
            if not partition: warn('belief base inconsistent')
            self.beliefbase = transform_beliefbase_to_z3(bb)
            self.partition = transform_partition_to_z3(partition)
    
    def preprocess(self):
        #TODO

    def rank(self, formula):
        """
        assumes weakly consistent cnflayers, i.e. cnflayer[-1] has rank infinity
        """
        opt = getOptimizer()
        opt.add(formula)
        ##TODO

    def rank_query(self, query):
        #TODO
        query = transform_conditional_to_z3(query)
        vf = query.make_A_then_B()
        ff = query.make_A_then_not_B()
        #TODO

    def inference(self,query):
        #TODO

    #replaces every items in the argument by it's sum representation
    def makeSummation(self, minima: dict) -> dict[int, list]:
        results = dict()
        for index, summ in minima.items():
            interim = []
            for subsum in summ:
                if subsum:
                    interim.append(z3.Sum([z3.Int(f'eta_{i}') for i in subsum]))
                else:
                    interim.append(0)  # Or use 0 directly
            results[index] = interim
        return results

    def freshVars(self, i: int) -> tuple:
        return z3.Int(f'mv_{i}'), z3.Int(f'mf_{i}')

    def minima_encoding(self, mv: int, eta:int, vsums: list, fsums: list) -> list:
        ands = [(mv < i) for i in ssums]
        ors = z3.Not(z3.And([(mv<i) for i in ssums]))
        ands.append(ors)
        implicit = [(eta +i >mv) for i in fsums]
        ands.extend(implicit)
        return ands

    def encoding(self, etas: dict, vSums: dict, fSums: dict) -> list:
        csp = []
        for index, eta in etas.items():
            mv, mf = self.freshVars(index)
            vMin = self.minima_encoding(mv, eta, vSums[index], fSums[index])
            csp.extend(vMin)
        return csp

    def translate(self) -> list:
        eta = {i: z3.Int(f'eta_{i}') for i, _ in enumerate(self.epistemic_state['belief_base'].conditionals, start=1)}
        gteZeros = [(e >= Int(0)) for e in eta.values()]
        vSums = self.makeSummation(self.epistemic_state['vMin'])
        fSums = self.makeSummation(self.epistemic_state['fMin'])
        csp = self.encoding(eta, vSums, fSums)
        csp.extend(gteZeros)
        return csp

