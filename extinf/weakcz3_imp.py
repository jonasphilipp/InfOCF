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
from pysmt.shortcuts import Solver,Implies, Optimizer
from pysmt.optimizer import MaxSMTGoal
from extinf.ezp import EZP, get_J_delta

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

class WeakCz3IMP():

    def __init__(self,bb) -> None:
            self.bb = bb
            partition = EZP(bb)
            ### Compute tolerance partition
            J_inf = partition[-1]
            self.J_delta = get_J_delta(J_inf)
            self.compile_constraints()
            self.base_csp = self.translate()
    



    def compile_constraints(self):
        opt = Optimizer()
        J_delta_keys = self.J_delta.keys()
        [opt.add(z3.Implies(c.antecedence,c.consequence)) for j,c in self.bb.conditionals.items() if j not in J_delta_keys]
        goals= [MaxSMTGoal() for j,c in self.bb.conditionals.items()]   ##setting goals also in j_delta for easier bookkeeping 
        objectives = {g.add_soft(Not(c.falsifying()), weight=1) for j,c in goals.items()} 

        V,F = dict(), dict()

        for i,c in enumerate(self.bb.conditionals, start=1):
            #t1 = time()
            if i not in J_delta_keys: continue
            cond = self.bb.conditionals[i]
            opt.push()
            opt.add(cond.verifying())
            vMin, fMin = [], []
            for m,g in opt.pareto_optimize(goals):
                ss =simplyfy({j:k.py_value() for j,k in enumerate(g,start=1) if i!=j})
                vMin.append(ss)
            opt.pop()
            opt.add(cond.falsifying())
            vMin, fMin = [], []
            for m,g in opt.pareto_optimize(goals):
                ss =simplyfy({j:k.py_value() for j,k in enumerate(g,start=1) if i!=j})
                fMin.append(ss)
            opt.pop()
            V[i] = vMin
            F[i]= fMin
        self.vMin, self.fMin = V,F
        return V,F
                            

    def compile_and_encode_query(self, query):
        """
        uses inequality encoding to encode the query. 
        """
        opt = Optimizer()
        J_delta_keys = self.J_delta.keys()
        [opt.add(z3.Implies(c.antecedence,c.consequence)) for j,c in self.bb.conditionals.items() if j not in J_delta_keys]
        goals= [MaxSMTGoal() for j,c in self.bb.conditionals.items()]   ##setting goals also in j_delta for easier bookkeeping 
        objectives = {g.add_soft(Not(c.falsifying()), weight=1) for j,c in goals.items()} 
        opt.push()
        opt.add(query.verify())
        vMin, fMin = [], []
        for m,g in opt.pareto_optimize(goals):
            ss =simplyfy({j:k.py_value() for j,k in enumerate(g,start=1) if i!=j})
            vMin.append(ss)
        opt.pop()
        opt.add(query.falsifying())
        for m,g in opt.pareto_optimize(goals):
            ss =simplyfy({j:k.py_value() for j,k in enumerate(g,start=1) if i!=j})
            vMin.append(ss)
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

    def compile_query_into_psr(self, query):
        opt = Optimizer()
        J_delta_keys = self.J_delta.keys()
        [opt.add(z3.Implies(c.antecedence,c.consequence)) for j,c in self.bb.conditionals.items() if j not in J_delta_keys]
        goals= [MaxSMTGoal() for j,c in self.bb.conditionals.items()]   ##setting goals also in j_delta for easier bookkeeping 
        objectives = {g.add_soft(Not(c.falsifying()), weight=1) for j,c in goals.items()} 
        opt.push()
        opt.add(query.verify())
        vMin, fMin = [], []
        for m,g in opt.pareto_optimize(goals):
            ss =simplyfy({j:k.py_value() for j,k in enumerate(g,start=1) if i!=j})
            vMin.append(ss)
        opt.pop()
        opt.add(query.falsifying())
        for m,g in opt.pareto_optimize(goals):
            ss =simplyfy({j:k.py_value() for j,k in enumerate(g,start=1) if i!=j})
            vMin.append(ss)
        return vMin, fMin

