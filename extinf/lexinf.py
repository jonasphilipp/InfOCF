from warnings import warn
from time import process_time
from inference.belief_base import BeliefBase
from extinf.ezp import EZP
from inference.conditional_z3 import Conditional_z3
from z3 import Optimize, Not, unsat, sat



def lex_less(x,y):
    """
    assumes |x| =|y|
    due to recursion, it only works for reasonibly small inputs (smth like length 1800 iirc)
    is good enough for current research, which scales up to about length 100
    """
    if len(x) == len(y) == 0: return False
    if (x[0]) == (y[0]): return lex_less(x[1:], y[1:])
    if x[0] < y[0] : return True
    return False


def getOptimizer():
    opt = Optimize()
    opt.set(priority='lexicographic')
    opt.set(maxsat_engine='rc2')
    return opt


class LexInf():

    ### TODO find out how TV property will work
    def __init__(self,bb) -> None:
            self.ezp = EZP(bb)

    def rank(self, formula):
        """
        assumes weakly consistent cnflayers, i.e. cnflayer[-1] has rank infinity
        """
        opt = getOptimizer()
        opt.add(formula)
        soft = self.ezp.partition[::-1]
        goals = []
        for i,s in enumerate(soft):
            for c in s:
                goal =opt.add_soft(Not(c.falsify()), weight=1, id=i)
            goals.append(goal)
        result = opt.check()
        if result == unsat: return [float('inf')]*len(goals)
        #print([dir(s.value()) for s in goals])
        return [s.value().py_value() for s in goals]

    def rank_query(self, query):
        vf = query.verify()
        ff = query.falsify()
        v,f = self.rank(vf), self.rank(ff)
        return v,f

    def inference(self, query):
        query = Conditional_z3.translate_from_existing(query)
        v,f = self.rank_query(query)
        #print(v,f)
        return lex_less(v,f)

