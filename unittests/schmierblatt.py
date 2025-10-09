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

from parser.Wrappers import parse_belief_base, parse_queries

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        VAR,COND, ckb, queriesSTR = sampleCKBandQueries(10,10,1,9,10,0)
        #queries = parse_queries(queriesSTR)

        weakCinf = WeakCInference(ckb)
        bb = weakCinf.epistemic_state['belief_base']
        z = SystemZRankZ3(bb)
        t1=time()
        weakCinf.preprocess_belief_base()
        t2=time()
        print(weakCinf.epistemic_state['vMin'])
        print(weakCinf.epistemic_state['fMin'])
        print("suggested", t2-t1)
        [print(z.rank_query(c)) for i,c in bb.conditionals.items()]




if __name__ == '__main__':
    unittest.main()
