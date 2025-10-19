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


def simplyfy(d):
    ## only simplifies view onto the dict, does not do any rewriting
    return [a for a,b in d.items() if b==1]

class WeakCz3():

    def __init__(self,bb) -> None:
            partition, _ = consistency(bb, 'z3', weakly=True)
            if not partition: warn('belief base inconsistent')
            self.beliefbase = transform_beliefbase_to_z3(bb)
            self.partition = transform_partition_to_z3(partition)
            self.originalbb = bb
            is_weakly = test_weakly(self.originalbb)
            assert(is_weakly)
            ### Compute tolerance partition
            J_inf = self.epistemic_state['partition'][-1]
            J_delta = dict()
            solver = Solver(name=self.epistemic_state['smt_solver'])
            [solver.add_assertion(Implies(c.antecedence,c.consequence)) for c in J_inf]
            for i,c in self.bb.conditionals.items():
                if solver.solve([c.make_A_then_not_B()]):
                    J_delta[i] = c
            self.J_delta = J_delta
    
            self.compile_constraint()
            self.base_csp = self.translate()
    



    def compile_constraints(self):

        """
        because the constraint for the falsifying case is almost the same as for the verifying case,
        this method uses the assumption stack, which is roughly 1% faster than not using the assumption stack
        """
        opt = makeOptimizer()
        objectives = {j:opt.add_soft(c.make_A_then_not_B() == False, id=j) for j,c in self.conditionals.items()}    #setting id's to setup multidimensional pareto optimization
        V,F = dict(), dict()
        J_delta_keys = J_delta.keys()

        for i,c in enumerate(self.conditionals, start=1):
            #t1 = time()
            if i not in J_delta_keys: continue
            cond = self.conditionals[i]
            antecedence = cond.antecedence
            consequence = cond.consequence
            opt.push()
            opt.add(antecedence)
            vMin, fMin = [], []
            opt.push() 
            opt.add(consequence)
            while opt.check() == sat:
                ss =simplyfy({j:k.value() for j,k in objectives.items() if i!=j}))
                vMin.append(filtersubsets(ss,J_delta_keys))
            opt.pop()
            opt.add(Not(consequence))
            while opt.check() == sat:
                ss = (simplyfy({j:k.value() for j,k in objectives.items() if i!=j}))
                fMin.append(filtersubsets(ss,J_delta_keys))
            opt.pop()
            V[i] = vMin
            F[i]= fMin
        self.vMin, self.fMin = V,F
        return V,F
                            

    def compile_and_encode_query(self, query):
        """
        uses inequality encoding to encode the query. 
        """
        J_delta_keys = J_delta.keys()
        opt = makeOptimizer()
        objectives = {j:opt.add_soft(makeAB(c) == False, id=j) for j,c in self.conditionals.items()}    #setting id's for easier bookkeeping
        antecedence = query.antecedence
        consequence = query.consequence
        opt.push()
        opt.add(antecedence)
        opt.push() 
        opt.add(consequence)
        vMin, fMin = [], []
        while opt.check() == sat:
            ss = simplyfy({j:k.value() for j,k in objectives.items()})
            vMin.append(filtersubsets(ss,J_delta_keys))
        opt.pop()
        opt.add(Not(consequence))
        while opt.check() == sat:
            ss=(simplyfy({j:k.value() for j,k in objectives.items()}))
            fMin.append(filtersubsets(ss,J_delta_keys))
        vSum = self.makeSummation({0:vMin})
        fSum = self.makeSummation({0:fMin})
        v, f = self.freshVars(0)
        vM = self.minima_encoding(v, vSum[0])
        fM = self.minima_encoding(f, fSum[0])
        csp = vM + fM + [mv >= mf]
        #print(len(csp))
        return csp


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

