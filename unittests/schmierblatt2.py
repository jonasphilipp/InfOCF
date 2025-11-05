import os
import sys
import unittest
import pandas as pd
from time import time

from weakly_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries, samplingWeaklyCKB
#from strong_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries

from inference.weak_c_inference import WeakCInference
from inference.inference_operator import InferenceOperator
from inference.consistency_sat import consistency,consistency_indices, get_J_delta, test_weakly
#from inference.weakly_system_z_rank import SystemZRankZ3

from parser.Wrappers import parse_belief_base, parseQuery

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        seed = 0 
        while True:
            seed +=1
            print(seed)
            VAR,COND, ckb, cs, ct = samplingWeaklyCKB(4,4,1,3)
            partition,_ = consistency(ckb, 'z3')
            if type(partition) == list : continue
            if not test_weakly(ckb): continue
            partition,_ = consistency(ckb, 'z3', True)
            jdelta = get_J_delta(ckb)
            if len(partition[-1]) == 1 and len(jdelta) == 2:
                print('found')
                break
        print(ckb.conditionals)






if __name__ == '__main__':
    unittest.main()
