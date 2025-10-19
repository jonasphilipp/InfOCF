from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
import z3
import math
from inference.z3tools import *
from inference.consistency_sat import checkTautologies, test_weakly, consistency
from pysmt.shortcuts import Solver,Implies

def filtersubsets(k, J):
    return [q for q in k if all([(t in J) for t in q])]

def getOptimizer():
    opt = z3.Optimize()
    opt.set(priority='pareto')
    opt.set(maxsat_engine='rc2')
    return opt


def simplyfy(d):
    ## only simplifies view onto the dict, does not do any rewriting
    return [a for a,b in d.items() if b==1]

class WeakCz3():

    def __init__(self,bb) -> None:
            partition, _ = consistency(bb, 'z3', weakly=True)
            if not partition: warn('belief base inconsistent')
            self.bb = transform_beliefbase_to_z3(bb)
            self.partition = transform_partition_to_z3(partition)
            self.originalbb = bb
            is_weakly = test_weakly(self.originalbb)
            assert(is_weakly)
            ### Compute tolerance partition
            J_inf = partition[-1]
            J_delta = dict()
            solver = Solver(name='z3')
            [solver.add_assertion(Implies(c.antecedence,c.consequence)) for c in J_inf]
            for i,c in self.originalbb.conditionals.items():
                if solver.solve([c.make_A_then_not_B()]):
                    J_delta[i] = c
            self.J_delta = J_delta
    
            self.compile_constraints()
            self.base_csp = self.translate()
    



    def compile_constraints(self):

        """
        because the constraint for the falsifying case is almost the same as for the verifying case,
        this method uses the assumption stack, which is roughly 1% faster than not using the assumption stack
        """
        opt = getOptimizer()
        objectives = {j:opt.add_soft(c.make_A_then_not_B() == False, id=j) for j,c in self.bb.conditionals.items()}    #setting id's to setup multidimensional pareto optimization
        V,F = dict(), dict()
        J_delta_keys = self.J_delta.keys()

        for i,c in enumerate(self.bb.conditionals, start=1):
            #t1 = time()
            if i not in J_delta_keys: continue
            cond = self.bb.conditionals[i]
            antecedence = cond.antecedence
            consequence = cond.consequence
            opt.push()
            opt.add(antecedence)
            vMin, fMin = [], []
            opt.push() 
            opt.add(consequence)
            while opt.check() == z3.sat:
                ss =simplyfy({j:k.value() for j,k in objectives.items() if i!=j})
                vMin.append(ss)
            opt.pop()
            opt.add(z3.Not(consequence))
            while opt.check() == z3.sat:
                ss = simplyfy({j:k.value() for j,k in objectives.items() if i!=j})
                fMin.append(ss)
            opt.pop()
            V[i] = filtersubsets(vMin,J_delta_keys)
            F[i]= filtersubsets(fMin,J_delta_keys)
        self.vMin, self.fMin = V,F
        return V,F
                            

    def compile_and_encode_query(self, query):
        """
        uses inequality encoding to encode the query. 
        """
        J_delta_keys = self.J_delta.keys()
        opt = getOptimizer()
        objectives = {j:opt.add_soft(c.make_A_then_not_B() == False, id=j) for j,c in self.bb.conditionals.items()}    #setting id's for easier bookkeeping
        antecedence = query.antecedence
        consequence = query.consequence
        opt.push()
        opt.add(antecedence)
        opt.push() 
        opt.add(consequence)
        vMin, fMin = [], []
        while opt.check() == z3.sat:
            ss = simplyfy({j:k.value() for j,k in objectives.items()})
            vMin.append(ss)
        opt.pop()
        opt.add(z3.Not(consequence))
        while opt.check() == z3.sat:
            ss=simplyfy({j:k.value() for j,k in objectives.items()})
            fMin.append(ss)
        vMin = filtersubsets(vMin,J_delta_keys)
        fMin = filtersubsets(fMin,J_delta_keys)
        vSum = self.makeSummation({0:vMin})
        fSum = self.makeSummation({0:fMin})
        v, f = self.freshVars(0)
        ands = [(f <= i) for i in fSum[0]]
        ors = z3.Not(z3.And([(f<i) for i in fSum[0]]))
        ands.append(ors)
        implicit = [(0+i >=f) for i in vSum[0]]
        ands.extend(implicit)
        return ands



    def inference(self, query):
        query = transform_conditional_to_z3(query)
        base_csp = self.base_csp
        query_csp = self.compile_and_encode_query(query)
        s=z3.Solver()
        s.add(base_csp)
        s.add(query_csp)
        result = s.check()
        return s.check() == z3.unsat


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
        ands = [(mv <= i) for i in vsums]
        ors = z3.Not(z3.And([(mv<i) for i in vsums]))
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
        eta = {i: z3.Int(f'eta_{i}') for i, _ in enumerate(self.bb.conditionals, start=1) if i in self.J_delta.keys()}
        gteZeros = [(e >= (0)) for e in eta.values()]
        vSums = self.makeSummation(self.vMin)
        fSums = self.makeSummation(self.fMin)
        csp = self.encoding(eta, vSums, fSums)
        csp.extend(gteZeros)
        return csp

