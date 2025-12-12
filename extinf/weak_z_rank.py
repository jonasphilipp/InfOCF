from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
import z3
import math
from inference.z3tools import *
from extinf.weaklexinf import LexInf


def index_nz(x):
    if len(x) == 0: return 0
    if x[0] != 0: return 1
    if x[0] == 0: return 1 + index_nz(x[1:])

class SystemZRank():
    ## TODO refactor to use lexinf 

    def __init__(self,bb) -> None:
        self.lexinf = LexInf(bb)

    def rank(self, formula):
        reg  = self.lexinf.rank(formula)
        if all([x==0 for x in reg]): return 0
        if reg[0] > 0 : return float('inf')
        return len(reg) - index_nz(reg) + 1


    def rank_query(self, query):
        #TODO
        query = transform_conditional_to_z3(query)
        vf = query.verify()
        ff = query.falsify()
        return self.rank(vf), self.rank(ff)







