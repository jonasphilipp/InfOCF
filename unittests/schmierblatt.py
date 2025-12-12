import os
import sys
import unittest
import pandas as pd
from time import time

from weakly_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries

from inference.weak_c_inference import WeakCInference
from inference.inference_operator import InferenceOperator
from inference.consistency_sat import consistency,consistency_indices
from inference.weakly_system_z_rank import SystemZRankZ3
from inference.weak_c_z3 import WeakCz3
#from inference.weakcz3_imp import WeakCz3IMP
from extinf.weakcz3_imp import WeakCz3IMP

from parser.Wrappers import parse_belief_base, parseQuery

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        VAR,COND, baseckb, weakckb, queriesSTR, ct, cs = sampleCKBandQueries(100,100,1,15,1,1811)
        #satqueries, c1 = sampleSATQueries(ckb, VAR, 10, 1, 3)
        #unsatqueries, c2 = sampleUNSATQueries(ckb, VAR, 10, 1, 3)
        queries, c3, countinfty = queriesSTR
        #satqueries = [parseQuery(i) for i in satqueries]
        #unsatqueries = [parseQuery(i) for i in unsatqueries]
        queries = [parseQuery(i) for i in queries]

        t1=time()
        weakCinf = WeakCz3IMP(weakckb)
        #print(weakCinf.vMin)
        #print(weakCinf.fMin)
        t2=time()
        print(t2-t1, 'weak')
        #corrections.preprocess_belief_base()
        bb = weakckb
        z = SystemZRankZ3(bb)
        t1=time()
        corrections = WeakCz3(weakckb)
        #base = WeakCz3(weakckb)
        #print(base.epistemic_state['vMin'])
        #print(base.epistemic_state['fMin'])
        t2=time()
        print(t2-t1,'base')
        #print("suggested", t2-t1)
        #[print(z.rank_query(c)) for i,c in bb.conditionals.items()]
        print('di')
        [print(corrections.inference(c),weakCinf.inference(c), z.rank_query(c),c) for i,c in bb.conditionals.items()]
        ##print('trivial sat')
        #[print(weakCinf.inference(c[1]),z.rank_query(c[1]), c[1]) for c in satqueries]
        #print('trivial unsat')
        #[print(weakCinf.inference(c[1]),z.rank_query(c[1]), c[1]) for c in unsatqueries]
        print('-----')
        [print(corrections.inference(c[1]),weakCinf.inference(c[1]),z.rank_query(c[1]), c[1]) for c in queries]
        print('total cbb sampled', ct)
        print('strongly cbb sampled', cs)
        print('total queries sampled',c3)
        print('queries ranked infty',countinfty)




if __name__ == '__main__':
    unittest.main()
