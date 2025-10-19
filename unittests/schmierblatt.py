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

from parser.Wrappers import parse_belief_base, parseQuery

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        VAR,COND, ckb, queriesSTR = sampleCKBandQueries(20,20,1,3,10,0)
        satqueries, c1 = sampleSATQueries(ckb, VAR, 10, 1, 3)
        unsatqueries, c2 = sampleUNSATQueries(ckb, VAR, 10, 1, 3)
        queries, c3, cinf = queriesSTR
        satqueries = [parseQuery(i) for i in satqueries]
        unsatqueries = [parseQuery(i) for i in unsatqueries]
        queries = [parseQuery(i) for i in queries]

        weakCinf = WeakCz3(ckb)
        corrections = WeakCInference(ckb)
        corrections.preprocess_belief_base()
        bb = weakCinf.originalbb
        z = SystemZRankZ3(bb)
        t1=time()
        t2=time()
        print("suggested", t2-t1)
        #[print(z.rank_query(c)) for i,c in bb.conditionals.items()]
        print('di')
        [print(corrections.inference(c), weakCinf.inference(c), z.rank_query(c),c) for i,c in bb.conditionals.items()]
        print('trivial sat')
        [print(weakCinf.inference(c[1]),z.rank_query(c[1]), c[1]) for c in satqueries]
        print('trivial unsat')
        [print(weakCinf.inference(c[1]),z.rank_query(c[1]), c[1]) for c in unsatqueries]
        print(c3, cinf)
        [print(weakCinf.inference(c[1]),z.rank_query(c[1]), c[1]) for c in queries]




if __name__ == '__main__':
    unittest.main()
