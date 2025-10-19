from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
import z3
import math
from inference.z3tools import *


def getOptimizer():
    opt = z3.Optimize()
    opt.set(priority='pareto')
    opt.set(maxsat_engine='rc2')
    return opt

class SystemZRankZ3():

    def __init__(self,bb) -> None:
            partition, _ = consistency(bb, 'z3', weakly=True)
            if not partition: warn('belief base inconsistent')
            self.beliefbase = transform_beliefbase_to_z3(bb)
            self.partition = transform_partition_to_z3(partition)
    
    def preprocess(self):
        #TODO

    def rank(self, formula):
        """
        assumes weakly consistent cnflayers, i.e. cnflayer[-1] has rank infinity
        """
        opt = getOptimizer()
        opt.add(formula)
        ##TODO

    def rank_query(self, query):
        #TODO
        query = transform_conditional_to_z3(query)
        vf = query.make_A_then_B()
        ff = query.make_A_then_not_B()
        #TODO







