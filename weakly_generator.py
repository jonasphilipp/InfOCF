from typing import List, Tuple, Dict, TypeVar

T = TypeVar('T')


import random
import os
import string
from collections import Counter

import sys
from inference.consistency_sat import consistency, test_weakly, get_J_delta
from inference.belief_base import BeliefBase
from parser.Wrappers import parseQuery,parseCKB
from inference.conditional import Conditional
from time import time_ns 
from pysmt.shortcuts import Solver,Implies
from inference.weakly_system_z_rank import SystemZRankZ3
from inference.weak_c_z3 import WeakCz3
from extinf.weaklexinf import LexInf
from extinf.weak_p_entailment import ExtendedPEntailment




def sample_operation():
    """
    returns a random operations that works on a list of formulas
    whether the operation is appropriate to do on the list, 
    i.e. the list has enough entries, has to be checked by the caller
    """
    def NotFormula(l):
        f = l.pop()
        l.insert(0, "(!%s)" %f)
    def AndFormula(l):
        f1 = l.pop()
        f2 = l.pop()
        l.insert(0, "(%s,%s)" %(f1,f2))
    def OrFormula(l):
        f1 = l.pop()
        f2 = l.pop()
        l.insert(0, "(%s;%s)" %(f1,f2))
    return random.choice([OrFormula,AndFormula,NotFormula])	


def sampleVars(variables:List[str], u)->Tuple[List[str],List[str]]:
    """
    returns two subsets of variables, possibly disjoint, possibly not.
    """
    #print(variables)
    V1 = random.choice(range(2,(u+1)//2))
    V2 = random.choice(range(2,(u+1)//2))
    tvars = variables
    random.shuffle(tvars)
    v1 = tvars[:V1]
    v2 = tvars[V1:V1+V2]

    return v1,v2



def sampleFormula(variables:List[str]):
    properties = variables
    while len(properties) > 1:
        op = sample_operation()
        op(properties)
        random.shuffle(properties)
    return properties[0]


def sampleConditional(variables:List[str], u)->List[str]:
    a,b = sampleVars(variables, u)
    return "(%s | %s)" % (sampleFormula(a),sampleFormula(b))

def sampleFact(variables,u):
    a,b = sampleVars(variables, u)
    return "(Bottom | !(%s))" % (sampleFormula(b))


def makeCKB(allVars:List[str], conditionals:List[str],filename:str):
    """
    Will tsave a list of variables strings and conditionals represented
    as strings, and save them as a valid CKB file.
    No sanity checks are performed.
    """
    name = os.path.basename(filename).split('.')[0]
    with open(filename, "w+") as f:
        print("signature", file=f)
        print(*allVars, sep=',', file=f)
        print('\n', f)
        print('conditionals', file=f)
        print(name +' {', file=f)
        print(*conditionals, sep=',\n', file=f)
        print('}',file=f)

        print('\n')
        

def makeQueryfile(conditionals:List[str], filename:str):
    with open(filename, "w+") as f:
        print(*conditionals, sep=',\n', file=f)



def createVariables(amount:int) ->List[str]:
    return [f'r{i}' for i in range(amount)]


def samplingWeaklyCKB(S:int,R:int,l:int, u:int) -> Tuple[str,Conditional,T]:
    """
    Will output a consistent CKB with S elements in the signature
    and R conditionals. 
    """
    count_total=0
    count_strongly=0
    while True:
        count_total+=1
        VAR = createVariables(S)
        conditionals = [(sampleConditional(VAR,u)) for _ in range(R)]
        COND= [parseQuery(c)[1] for c in conditionals]
        dummyCKB = BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(COND,start=1)}, "")
        part,_ = consistency(dummyCKB)
        if (part != False):
            count_strongly+=1
            facts = [parseQuery(sampleFact(VAR,u//2))[1] for i in range(R//20)]
            weakbb=BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(COND+facts,start=1)}, "")
            weak = test_weakly(weakbb)
            if (weak==True):
                print('ckb found')
                break
    return VAR, COND, dummyCKB, weakbb, count_total,count_strongly


def canonical(x):
    """ 
    return a somewhat canonicall representation of a list list
    """
    return sorted([sorted(i) for i in x])

def checkDifficult(v,f):
    """
    since compilation without checking for rank infinity can produce either [] or [[]], we check for both
    """
    if v == [[]] or v==[] : return False
    if f == [[]] or f==[] : return False
    if canonical(v) == canonical(f): 
        print('lhs is rhs', v)
        return False
    if len(f) < 2:
        print('pseudolinear')
        return False
    return True




def sampleQueries(ckb, VAR, Q, l, u):
    """
    attempts to sample non-trivial queries, that means neither qV nor qF get optimized down to zero.
    """
    found = []
    s = Solver(name='z3')
    [s.add_assertion(Implies(j.antecedence,j.consequence)) for j in (ckb).conditionals.values()]
    sysz = SystemZRankZ3(ckb)
    crep = WeakCz3(ckb)
    lexinf =LexInf(ckb)
    pent = ExtendedPEntailment(ckb)
    infty = float('inf')
    counter = 0
    counterInfty = 0 
    while len(found) < Q:
        query = (sampleConditional(VAR, u))
        counter +=1
        q=parseQuery(query)[1]

        vf,ff = sysz.rank_query(q)
        if ff == infty or vf == infty:
            counterInfty +=1
            continue
        if pent.rank_query(q)==True:
            print('follows by P')
            continue

        vMin, fMin = crep.compile_query_into_psr(q)
        difficult = checkDifficult(vMin, fMin)
        if difficult:
            if lexinf.inference(q)==False:
                print('bounded by lexinf')
                continue
            found.append(query)
    return found,counter,counterInfty
        

def sampleUNSATQueries(ckb, VAR, Q, l, u):
    """
    attempts to sample non-trivial queries, that means neither qV nor qF get optimized down to zero.
    """
    found = []
    s = Solver(name='z3')
    [s.add_assertion(Implies(j.antecedence,j.consequence)) for j in (ckb).conditionals.values()]
    counter = 0 
    while len(found) < Q:
        query = (sampleConditional(VAR,u))
        q=parseQuery(query)[1]
        s.push()
        difficult = (s.solve([q.make_A_then_B()])) and (not s.solve([q.make_A_then_not_B()]))
        counter += 1
        if difficult:
            found.append(query)
    return found, counter

def sampleSATQueries(ckb, VAR, Q, l, u):
    """
    attempts to sample non-trivial queries, that means neither qV nor qF get optimized down to zero.
    """
    found = []
    s = Solver(name='z3')
    [s.add_assertion(Implies(j.antecedence,j.consequence)) for j in (ckb).conditionals.values()]
    counter = 0
    while len(found) < Q:
        query = (sampleConditional(VAR, u))
        q=parseQuery(query)[1]
        s.push()
        difficult = (not s.solve([q.make_A_then_B()])) and (s.solve([q.make_A_then_not_B()]))
        counter +=1
        if difficult:
            found.append(query)
    return found, counter



def sampleCKBandQueries(S,R,l,u,Q,seed) -> T:
    """
    S : amount of variables in the signature
    R : amount of conditionals
    l : minimal amount of literals per conditional (at least 1)
    u : maximal amount of literals per conditional (at most S)
    Q : samples Q amount of sat queries and Q amount of unsat Queries
    seed: used for reproducability in pseudorandom generation
    """
    random.seed(seed)
    VAR, COND, baseckb, weakckb, ct, cs = samplingWeaklyCKB(S,R,l,u)
    queries = sampleQueries(weakckb, VAR, Q, l, u)
    return VAR, COND, baseckb, weakckb, queries, ct, cs






if __name__ == "__main__":
    """
    SR = [(4,4), (6,6), (8,8), (10,10)] + [(i,i+j) for i in range(10,24,2) for j in range(-6,8,2)]

    for i,(S,R) in enumerate(SR):
        VAR, COND, found_sat, found_unsat = sampleCKBandQueries(S,R,2,5,50,i)
        makeQueryfile(found_sat, 'esquaru/randomSAT_%i_%i_%i.cl' % (S,R, i))
        makeCKB(VAR, COND, 'esquaru/randomTest_%i_%i_%i.cl' % (S,R, i))
    

    """
