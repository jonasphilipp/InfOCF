#from pysmt.shortcuts import Solver, Implies, is_sat
from z3 import Solver, Implies, sat
from inference.conditional_z3 import Conditional_z3

def toImplicit(conditionals):
    """
    Accepts a list of conditionals and returns a list of implications.
    assumes condtionals are already in z3 form
    """
    return [i.imply() for i in conditionals]




def test_weakly(ckb):
    conditionals = [Conditional_z3.translate_from_existing(i) for i in ckb.conditionals.values()]
    s= Solver()
    return s.check(toImplicit(conditionals)) == sat


def get_J_delta(ezp):
    ### assumes condtionals are already in z3 form
    ### compute J_delta
    conditionals = {i:Conditional_z3.translate_from_existing(c) for i,c in ezp.bb.conditionals.items()}
    J_inf = ezp.partition[-1]
    J_delta = dict()
    solver = Solver()
    [solver.add(c.imply()) for c in J_inf]
    for i,c in conditionals.items():
        if sat==solver.check([c.falsify()]):
            J_delta[i] = c
    return J_delta




def getEZP(ckb):
    conditionals = [Conditional_z3.translate_from_existing(i) for i in ckb.conditionals.values()]
    #partition is a list of lists
    partition = []
    while True:
        s=Solver()
        knowledge = toImplicit(conditionals)
        [s.add(k) for k in knowledge]
        T = []
        C = []
        for c in conditionals:
            #print(c)
            if sat == s.check([c.verify()]):
                T.append(c)
            else:
                C.append(c)
        partition.append(T)
        conditionals = C
        #if no conditionals remain, the ckb is consistent 
        if len(conditionals) == 0:
            ## is remainder always []?
            return partition + [[]]
        if len(T) == 0:
            ## the last element in partition will always be [], so we remove it
            return partition[0:-1] + [C]


class EZP:
    def __init__(self, bb):
        self.partition = getEZP(bb)
        self.bb = bb
        self.strong_consistency = self.partition[-1] == []
        self.weak_consistency = test_weakly(bb)

