from pysmt.shortcuts import Solver, Implies, is_sat

def toImplicit(conditionals):
    """
    Accepts a list of conditionals and returns a list of implications.
    """
    return [Implies(i.antecedence, i.consequence) for i in conditionals]


def checkTautologies(conditionals):
    conditionals = [i for i in conditionals.values()]
    with Solver(name='z3'):
        for c in conditionals:
            case1 = is_sat(c.make_A_then_B())
            case2 = is_sat(c.make_A_then_not_B())
            if not case1 or not case2: return True


def consistency(ckb, solver='z3', weakly=False):
    #print(solver)
    conditionals = [i for i in ckb.conditionals.values()]
    #partition is a list of lists
    partition = []
    ### We use the solver here, not the optimizer
    calls = 0
    levels = 0
    while True:
        with Solver(name=solver) as s:
            #if no conditionals remain, the ckb is consistent 
            if len(conditionals) == 0:
                if weakly:
                    partition.append([])
                #print(calls, levels, [len(i) for i in partition], 'consistent')
                return partition, ([len(p) for p in partition],calls, levels)
            levels +=1
            #print(levels)
            s.push()
            knowledge = toImplicit(conditionals)
            #print(knowledge)
            [s.add_assertion(k) for k in knowledge]
            R = []
            C = []
            for c in conditionals:
                calls+=1
                s.push()
                s.add_assertion(c.make_A_then_B())
                if s.solve():
                    R.append(c)
                else:
                    C.append(c)
                s.pop()
            if R == []:
                #we found no parition, the ckb is inconsistent
                #Maybe throw an error instead?
                #print(calls, levels, 'False')
                if weakly:
                    # if weakly flag set and returend list hast non-empty list as last element, 
                    # then belief base is only weakly consistent
                    partition.append(C)
                    return partition, ([len(p) for p in partition],calls, levels)
                else:
                    return False, ([len(p) for p in partition], calls, levels)
            partition.append(R)
            conditionals = C
            #reset the solver sothat it wont consider the currently found partition anymore
            s.pop()


def consistency_indices(ckb, solver, weakly=False):
    conditionals = [i for i in ckb.conditionals]
    #partition is a list of lists
    partition = []
    ### We use the solver here, not the optimizer
    calls = 0
    levels = 0
    while True:
        with Solver(name=solver) as s:
            #if no conditionals remain, the ckb is consistent 
            if len(conditionals) == 0:
                if weakly:
                    partition.append([])
                #print(calls, levels, [len(i) for i in partition], 'consistent')
                return partition, ([len(p) for p in partition],calls, levels)
            levels +=1
            #print(levels)
            s.push()
            #[print(c, type(c)) for c in conditionals]
            knowledge = toImplicit([ckb.conditionals[i] for i in conditionals])
            [s.add_assertion(k) for k in knowledge]
            R = []
            C = []
            for i in conditionals:
                calls+=1
                s.push()
                s.add_assertion(ckb.conditionals[i].make_A_then_B())
                if s.solve():
                    R.append(i)
                else:
                    C.append(i)
                s.pop()
            if R == []:
                if weakly:
                    partition.append(C)
                    return partition, ([len(p) for p in partition],calls, levels)
                else:
                    return False, ([len(p) for p in partition], calls, levels)
            partition.append(R)
            conditionals = C
            #reset the solver sothat it wont consider the currently found partition anymore
            s.pop()

def set_core_minimize(s):
    s.set("sat.core.minimize",True)  # For Bit-vector theories
    #s.set("smt.core.minimize",True)  # For general SMT 



