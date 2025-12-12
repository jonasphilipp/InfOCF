from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
import z3
import math
from inference.z3tools import *


class SystemZRankZ3():

    def __init__(self,bb) -> None:
            partition, _ = consistency(bb, 'z3', weakly=True)
            if not partition: warn('belief base inconsistent')
            self.beliefbase = transform_beliefbase_to_z3(bb)
            self.partition = transform_partition_to_z3(partition)

    def _rank(self, formula):
        """
        assumes weakly consistent cnflayers, i.e. cnflayer[-1] has rank infinity
        """
        opt = z3.Optimize()
        opt.add(formula)
        partition = self.partition
        opt.add(z3.And([z3.Not(c.make_A_then_not_B()) for c in partition[-1]]))
        soft = partition[0:-1]
        for i,s in enumerate(soft):
            obj = opt.add_soft(z3.And([z3.Not(c.make_A_then_not_B()) for c in s]), weight=2**i)
        result = opt.check()

        if z3.unsat == result : return float('inf')
        if obj.value().py_value() == 0: return 0 

        value = math.floor(math.log2(obj.value().py_value()))
        #print(value, type(value))
        return value + 1

    def rank_query(self, query):
        #TODO
        query = transform_conditional_to_z3(query)
        vf = query.make_A_then_B()
        ff = query.make_A_then_not_B()
        return self._rank(vf), self._rank(ff)







