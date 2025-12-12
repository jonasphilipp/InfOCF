import os
import sys
import unittest
import pandas as pd
from time import time

from weakly_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries, samplingWeaklyCKB
#from strong_generator import  sampleCKBandQueries, sampleQueries, sampleSATQueries, sampleUNSATQueries

#from inference.weak_c_inference import WeakCInference
#from inference.inference_operator import InferenceOperator
#from inference.consistency_sat import consistency,consistency_indices, get_J_delta, test_weakly
#from inference.weakly_system_z_rank import SystemZRankZ3
#from inference.weak_c_z3 import WeakCz3

from extinf.weakcz3_imp    import  WeakCz3IMP
from extinf.weaklexinf    import  LexInf
from extinf.weak_z_rank import  SystemZRank
from extinf.weak_p_entailment import ExtendedPEntailment
from parser.Wrappers import parse_belief_base, parseQuery

ex1=  """
signature
    races_fixed, bookies_crooked, trade_decline, police_happy
conditionals
birds002{
    (trade_decline|races_fixed;bookies_crooked),
    (police_happy|trade_decline),
    (!police_happy|Top)

}
"""
query1="(!races_fixed|Top)"

class InferenceCorrectnessTest(unittest.TestCase):

    def test_random_bothmethods_equal(self):
        seed = 0 
        ckb=parse_belief_base(ex1)
        query=parseQuery(query1)[1]
        cinf =WeakCz3IMP(ckb)
        kz=SystemZRank(ckb)
        lexinf = LexInf(ckb)
        p = ExtendedPEntailment(ckb)
        print(kz.rank_query(query))
        print(cinf.inference(query),query)
        #print('here')
        print(lexinf.inference(query))
        print(p.rank_query(query))



if __name__ == '__main__':
    unittest.main()
