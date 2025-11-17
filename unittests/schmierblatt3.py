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
from inference.weakcz3_imp import WeakCz3IMP

from parser.Wrappers import parse_belief_base, parseQuery

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        VAR,COND, ckb, queriesSTR, ct, cs = sampleCKBandQueries(20,20,1,10,20,6)
        weakCinf = WeakCz3(ckb)
        weakCIMP = WeakCz3IMP(ckb)
        print(weakCinf.vMin)
        print(weakCIMP.vMin)
        print(weakCinf.fMin)
        print(weakCIMP.fMin)



if __name__ == '__main__':
    unittest.main()
