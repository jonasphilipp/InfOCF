from inference.conditional import Conditional
from inference.inference import Inference
from inference.consistency_sat import consistency
from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
from pysmt.shortcuts import Optimizer, Not
from pysmt.optimizer import MaxSMTGoal
import math
from inference.z3tools import *
from extinf.ezp import EZP


class LexInf():

    def __init__(self,bb) -> None:
            self.ezp = EZP(bb)

    def _rank(self, formula):
        """
        assumes weakly consistent cnflayers, i.e. cnflayer[-1] has rank infinity
        """
        opt = Optimizer(solver='z3')
        ### TODO replace z3 optimizer with pysmt optimizer
        opt.add(formula)
        soft = partition[::-1]
        goal = []
        for i,s in enumerate(soft):
            obj = MaxSMTGoal()
            for c in s:
                opj.add_soft_clause(Not(c.falsify()), weight=1)
            goal.append(obj)
        result = opt.lexicographic_optimize(goal)
        if result == (None,None): return [float('inf')]*len(goal)
        return [s.py_value() for m,s in result]

    def rank_query(self, query):
        #TODO
        vf = query.make_A_then_B()
        ff = query.make_A_then_not_B()
        return self._rank(vf), self._rank(ff)

