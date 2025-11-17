from pysmt.shortcuts import Solver, Implies, is_sat

def toImplicit(conditionals):
    """
    Accepts a list of conditionals and returns a list of implications.
    """
    return [Implies(i.antecedence, i.consequence) for i in conditionals]




def test_weakly(ckb):
    conditionals = [i for i in ckb.conditionals.values()]
    with Solver(name='z3') as s:
        return s.solve(toImplicit(conditionals))


def get_J_delta(ckb):
    part,infty = weakEZP(ckb, 'z3', True)
    ### compute J_delta
    J_inf = infty
    J_delta = dict()
    solver = Solver(name='z3')
    [solver.add_assertion(Implies(c.antecedence,c.consequence)) for c in J_inf]
    for i,c in ckb.conditionals.items():
        if solver.solve([c.make_A_then_not_B()]):
            J_delta[i] = c
    ### hold them in epistemic state? lol
    return J_delta




def weakEZP(ckb, solver='z3', weakly=False):
    #print(solver)
    conditionals = [i for i in ckb.conditionals.values()]
    #partition is a list of lists
    partition = []
    ### We use the solver here, not the optimizer
    while True:
        with Solver(name=solver) as s:
            #if no conditionals remain, the ckb is consistent 
            knowledge = toImplicit(conditionals)
            [s.add_assertion(k) for k in knowledge]
            T = []
            C = []
            for c in conditionals:
                s.push()
                s.add_assertion(c.make_A_then_B())
                if s.solve():
                    T.append(c)
                else:
                    C.append(c)
                s.pop()
            partition.append(T)
            conditionals = C
            if len(conditionals) == 0:
                ## is remainder always []?
                return partition, []
            if len(T) == 0:
                ##partition might be empty?
                ## the last element will always be [], so we remove it
                ## moreover, if the belief base is inconsistent, partition will be = []
                ## so trying to access partition[0] or partition[-1] will result in error
                return partition[0:-1], C


