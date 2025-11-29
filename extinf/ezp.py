from pysmt.shortcuts import Solver, Implies, is_sat

def toImplicit(conditionals):
    """
    Accepts a list of conditionals and returns a list of implications.
    """
    return [i.imply() for i in conditionals]




def test_weakly(ckb):
    conditionals = [i for i in ckb.conditionals.values()]
    with Solver(name='z3') as s:
        return s.solve(toImplicit(conditionals))


def get_J_delta(ezp):
    part = ezp[-1]
    ### compute J_delta
    J_inf = part[-1]
    J_delta = dict()
    solver = Solver(name='z3')
    [solver.add_assertion(c.imply()) for c in J_inf]
    for i,c in ckb.conditionals.items():
        if solver.solve([c.falsify()]):
            J_delta[i] = c
    return J_delta




def getEZP(ckb, solver='z3'):
    conditionals = [i for i in ckb.conditionals.values()]
    #partition is a list of lists
    partition = []
    while True:
        with Solver(name=solver) as s:
            knowledge = toImplicit(conditionals)
            [s.add_assertion(k) for k in knowledge]
            T = []
            C = []
            for c in conditionals:
                if s.solve(c.falsify()):
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

