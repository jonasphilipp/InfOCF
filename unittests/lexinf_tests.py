import os
import sys
import unittest
import pandas as pd
from time import time

from weakly_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries

#from inference.weak_c_inference import WeakCInference
#from inference.inference_operator import InferenceOperator
#from inference.consistency_sat import consistency,consistency_indices
#from inference.weakly_system_z_rank import SystemZRankZ3
#from inference.weak_c_z3 import WeakCz3
from extinf.weaklexinf import LexInf
from extinf.weak_z_rank import SystemZRank
from extinf.weak_p_entailment import ExtendedPEntailment

from parser.Wrappers import parse_belief_base, parseQuery

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        VAR,COND, ckb, queriesSTR, ct, cs = sampleCKBandQueries(50,50,2,16,10,27)
        #satqueries, c1 = sampleSATQueries(ckb, VAR, 10, 1, 3)
        #unsatqueries, c2 = sampleUNSATQueries(ckb, VAR, 10, 1, 3)
        #queries, c3, countinfty = queriesSTR
        #satqueries = [parseQuery(i) for i in satqueries]
        #unsatqueries = [parseQuery(i) for i in unsatqueries]
        #queries = [parseQuery(i) for i in queries]

        lexinf = LexInf(ckb)
        print(len(lexinf.ezp.partition[-1]))
        kz = SystemZRank(ckb)
        pent = ExtendedPEntailment(ckb)
        print('di')
        ##[print((c.verify())) for i,c in ckb.conditionals.items()]
        [print(lexinf.inference(c),pent.rank_query(c),kz.rank_query(c)) for i,c in ckb.conditionals.items()]




if __name__ == '__main__':
    unittest.main()
