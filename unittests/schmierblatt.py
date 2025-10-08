import os
import sys
import unittest
import pandas as pd
from time import time

from weakly_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries

from inference.weak_c_inference import WeakCInference
from inference.weak_c_naive import NaiveCInference
from inference.weak_c_V3 import V3CInference
from inference.inference_operator import InferenceOperator
from inference.consistency_sat import consistency,consistency_indices

from parser.Wrappers import parse_belief_base, parse_queries

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        VAR,COND, ckb, queriesSTR = sampleCKBandQueries(10,10,1,9,10,0)
        #queries = parse_queries(queriesSTR)

        weakCinf = WeakCInference(ckb)
        naiveCinf = NaiveCInference(ckb)
        t1=time()
        weakCinf.preprocess_belief_base()
        t2=time()
        print("suggested", t2-t1)
        naiveCinf.preprocess_belief_base()
        t3=time()
        print("Naive")
        print(naiveCinf.epistemic_state['vMin'])
        print(naiveCinf.epistemic_state['fMin'])
        print("Suggested")
        print(weakCinf.epistemic_state['vMin'])
        print(weakCinf.epistemic_state['fMin'])
        """
        print("")
        print("Naive")
        print(naiveCinf.epistemic_state['fMin'])
        print("Suggested")
        print(weakCinf.epistemic_state['fMin'])
        """
        print("naive", t3-t2)
        print("suggested", t2-t1)




if __name__ == '__main__':
    unittest.main()
