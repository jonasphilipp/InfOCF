from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
import z3
from pysmt.shortcuts import Not
import math
from extinf.z3tools import *
from extinf.weak_z_rank import SystemZRank



class ExtendedPEntailment():
    ## TODO refactor to use lexinf 

    def __init__(self,bb) -> None:
        self.bb = bb



    def rank_query(self, query):
        #TODO
        tmp = {i:c for i,c in self.bb.conditionals.items()}
        tmpConditional = Conditional(Not(query.B), query.A, "", "")
        tmp[len(tmp)+1]=tmpConditional
        kappaz = SystemZRank(BeliefBase("",tmp,""))
        query = transform_conditional_to_z3(query)
        return kappaz.rank(query.A) == float('inf')







