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
from extinf.ezp import EZP, get_J_delta
from extinf.weak_z_rank import SystemZRank
from time import perf_counter

def simplyfy(d):
    ## only simplifies view onto the dict, does not do any rewriting
    return [a for a,b in d.items() if b==1]

def getOptimizer():
    opt = z3.Optimize()
    opt.set(priority='pareto')
    opt.set(maxsat_engine='rc2')
    opt.add_soft(z3.BoolVal(True), weight=1,id='dummy1')
    opt.add_soft(z3.BoolVal(True), weight=1,id='dummy2')
    opt.add_soft(z3.BoolVal(True), weight=1,id='dummy3')
    return opt

class TimeoutException(Exception):
    pass
    

class WeakCz3IMP():

    def __init__(self,bb, timeout = 600) -> None:
            self.sysZ = SystemZRank(bb)
            self.bb = bb.transform_to_z3_objects()
            ezp = EZP(bb)
            self.J_delta = get_J_delta(ezp)
            self.compile_constraints()
            self.base_csp = self.translate()
            self.t1 = None
            self.timeout = timeout
            self.compile_constraints()


    def compile_constraints(self):

        V,F = dict(), dict()
        self.t1 = perf_counter()

        for i,c in self.bb.conditionals.items():
            #t1 = time()
            if i not in self.J_delta.keys(): continue
            vMin, fMin = self.compile_query_into_psr(c,i)
            V[i] = vMin
            F[i]= fMin
        self.vMin, self.fMin = V,F
        return V,F
                            

    def compile_and_encode_query(self, query):
        """
        uses inequality encoding to encode the query. 
        """
        self.t1 = perf_counter()
        vMin,fMin = self.compile_query_into_psr(query, -1)
        vSum = self.makeSummation({0:vMin})
        fSum = self.makeSummation({0:fMin})
        v, f = self.freshVars(0)
        ands = [(f <= i) for i in fSum[0]]
        ors = z3.Not(z3.And([(f<i) for i in fSum[0]]))
        ands.append(ors)
        implicit = [(i >=f) for i in vSum[0]]
        ands.extend(implicit)
        return ands



    def inference(self, query):
        if len(self.J_delta) != len(self.bb.conditionals):
            zvf, zff = self.sysZ.rank_query(query)
            if zff == float('inf'): return True
            if zvf == float('inf'): return False
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
        
        """
        if len(fsums)==len(vsums):
            if all([i in vsums for i in fsums]):
                print('lhs is rhs', fsums)
                return [eta > 0]
        """
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

    def compile_query_into_psr(self, query, index):
        opt = getOptimizer()
        J_delta_keys = self.J_delta.keys()
        [opt.add(z3.Not(c.falsify())) for j,c in self.bb.conditionals.items() if j not in J_delta_keys]
        objectives = {j:opt.add_soft(z3.Not(c.falsify()), weight=1,id=j) for j,c in self.bb.conditionals.items() if j in J_delta_keys} 
        opt.push()
        opt.add(query.verify())
        vMin, fMin = [], []
        while opt.check() != z3.unsat:
            ss =simplyfy({j:k.value().py_value() for j,k in objectives.items() if j!=index})
            vMin.append(ss)
            if perf_counter() - self.t1 > 600: raise TimeoutException()
        opt.pop()
        opt.add(query.falsify())
        while opt.check() != z3.unsat:
            ss =simplyfy({j:k.value().py_value() for j,k in objectives.items() if j!=index})
            fMin.append(ss)
            if perf_counter() - self.t1 > 600: raise TimeoutException()
        return vMin, fMin

