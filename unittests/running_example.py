import os
import sys
import unittest
import pandas as pd
from time import time

#from weakly_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries, samplingWeaklyCKB
#from strong_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries

#from inference.weak_c_inference import WeakCInference
#from inference.inference_operator import InferenceOperator
#from inference.consistency_sat import consistency,consistency_indices, get_J_delta, test_weakly
#from inference.weakly_system_z_rank import SystemZRankZ3
#from inference.weak_c_z3 import WeakCz3
from inference.conditional_z3 import Conditional_z3

from extinf.ezp    import  getEZP,test_weakly
from extinf.weakcz3_imp    import  WeakCz3IMP
from extinf.weaklexinf    import  LexInf
from extinf.weak_z_rank import  SystemZRank
from extinf.weak_p_entailment import ExtendedPEntailment
from parser.Wrappers import parse_belief_base, parseQuery

ex1=  """
signature
    f,b,w,p
conditionals
birds002{
    (f |b), (w|b), (b|p), (!f |p), (Bottom|!b)
}
"""
query1="(w|p)"
query2="(p|Top)"
ex2=  """
signature
    f,b,w,p
conditionals
birds002{
    (f |b), (w|b), (b|p), (!f |p), (Bottom|!b), (!w|p)
}
"""
#query2="(peaceful|quiet)"
import z3
class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        seed = 0 
        ckb=parse_belief_base(ex1)
        ckb2=parse_belief_base(ex2)
        print(test_weakly(ckb2))
        q1=parseQuery(query1)[1]
        q2=parseQuery(query2)[1]
        q2 = Conditional_z3.translate_from_existing(q2)
        print(getEZP(ckb))
        print(getEZP(ckb2))
        cinf =WeakCz3IMP(ckb)
        cinf.compile_constraints()
        csp = cinf.translate()
        eta = z3.Sum([z3.Int(f'eta_{i}') for i in [1,2,4]])
        opt = z3.Optimize()
        opt.add(csp)
        opt.minimize(eta)
        opt.check()
        print(opt.model())

        lexinf = LexInf(ckb2)
        #p = ExtendedPEntailment(ckb)
        #print(lexinf.rank_query(q2))



if __name__ == '__main__':
    unittest.main()
