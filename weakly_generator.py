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


def sampleVars(variables:List[str], u, l=2)->Tuple[List[str],List[str]]:
    """
    returns two subsets of variables, possibly disjoint, possibly not.
    """
    #print(variables)

    V1 = random.choice(list(range(l,(u+1)//2)))
    V2 = random.choice(list(range(l,(u+1)//2)))
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


def sampleConditional(variables:List[str], u,l=2)->List[str]:
    a,b = sampleVars(variables, u,l)
    return "(%s | %s)" % (sampleFormula(a),sampleFormula(b))

def sampleFact(variables,u,l=2):
    a,b = sampleVars(variables, u,l)
    return "(Bottom | !(%s))" % (sampleFormula(b))


def makeCKB(allVars:List[str], conditionals:List[str],filename:str):
    """
    Will save a list of variables strings and conditionals represented
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
    while True:
        VAR = createVariables(S)
        conditionals = [(sampleConditional(VAR,u)) for _ in range(R)]
        COND= [parseQuery(c)[1] for c in conditionals]
        dummyCKB = BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(COND,start=1)}, "")
        part,_ = consistency(dummyCKB)
        if (part != False):
            facts = [parseQuery(sampleFact(VAR,u//2))[1] for i in range(R//20)]
            weakbb=BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(COND+facts,start=1)}, "")
            weak = test_weakly(weakbb)
            if (weak==True):
                print('ckb found')
                break
    return VAR, COND, dummyCKB, weakbb


def sampleCKB(S,R,u,l, depth):
    while True:
        VAR = createVariables(S)
        conditionals = [(sampleConditional(VAR,u,l)) for _ in range(R)]
        COND= [parseQuery(c)[1] for c in conditionals]
        dummyCKB = BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(COND,start=1)}, "")
        part,_ = consistency(dummyCKB)
        if (part != False):
            if part[-1] != []: continue
            if len(part) >= depth:
                print('CKB found')
                break
    return VAR, COND, dummyCKB

def sampleQueriesSimple(S,R,l,u):
    VAR = createVariables(S)
    conditionals = [(sampleConditional(VAR,u,l)) for _ in range(R)]
    return conditionals



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
    if len(f) < 3:
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
    while len(found) < Q:
        query = (sampleConditional(VAR, u))
        q=parseQuery(query)[1]

        vf,ff = sysz.rank_query(q)
        if ff == infty or vf == infty:
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
    return found
        

def checkQuery(ckb, query):
    """
    attempts to sample non-trivial queries, that means neither qV nor qF get optimized down to zero.
    """
    sysz = SystemZRankZ3(ckb)
    crep = WeakCz3(ckb)
    lexinf =LexInf(ckb)
    pent = ExtendedPEntailment(ckb)
    infty = float('inf')

    q=query
    vf,ff = sysz.rank_query(q)
    if ff == infty or vf == infty:
        return False
    if pent.rank_query(q)==True:
        print('follows by P')
        return False

    vMin, fMin = crep.compile_query_into_psr(q)
    difficult = checkDifficult(vMin, fMin)
    if not difficult:
        return False
    if lexinf.inference(q)==False:
        print('bounded by lexinf')
        return False
    return True


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


def sampleForLEXbenchmarks():
    S,R,u,l,d = 150,150,11,3,15
    for i in range(20):
        random.seed(i)
        VAR,COND, CKB = sampleCKB(S,R,u,l,d)
        queries = sampleQueriesSimple(S,20,l,u)
        print(f'found {i}th bench set')
        makeQueryfile(queries,  f'lex_benchmark/randomqq_{i}.cl')
        makeCKB(VAR, COND, f'lex_benchmark/randombb_{i}.cl')


def turnToFact(cond):
    c= cond[1:-1]
    con, ant = c.split('|')
    return f'(Bottom | ({ant}),!({con}))' 

def sampleForWeakCinfBenchmarkI():
    u,l = 11,3
    S = [50,80,110,140]
    for s in S:
        d = int(s * 0.1)
        R = int(s * 1.30)
        for i in range(10):
            random.seed(i)
            VAR,COND, CKB = sampleCKB(s,R,u,l,d)
            while True:
                facts = [sampleFact(VAR, u,l) for _ in range(int(s * 0.3))]
                cond= [parseQuery(c)[1] for c in COND+facts]
                dummyCKB = BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(cond,start=1)}, "")
                part,_ = consistency(dummyCKB)
                if (part != False):
                    if len(part) >= d:
                        print('CKB found')
                        break
            QUERIES = []
            for j in range(10):
                while True:
                    Q = sampleConditional(VAR, u,l)
                    q = parseQuery(Q)[1]
                    if checkQuery(CKB,q) and checkQuery(dummyCKB,q):
                        QUERIES.append(q)
                        break
            makeQueryfile(queries,  f'weakcinf1_benchmark/randomqq_{s}_{i}.cl')
            makeCKB(VAR, COND, f'weakcinf1_benchmark/randomsbb__{s}_{i}.cl')
            makeCKB(VAR, COND+facts, f'weakcinf1_benchmark/randomwbb_{s}_{i}.cl')



def sampleForWeakCinfBenchmarkII():
    u,l = 11,3
    S = [50,80,110,140]
    for s in S:
        d = int(s * 0.1)
        f = int(s * 0.3)
        t = int(s* 0.07)
        for i in range(10):
            random.seed(i)
            R = s
            VAR,COND, CKB = sampleCKB(s,R,u,l,d)
            while True:
                random.shuffle(COND)
                facts = [turnToFact(c) for c in COND[:f]]
                cond= [parseQuery(c)[1] for c in COND[f:]+facts]
                dummyCKB = BeliefBase([(v) for v in VAR], {i:c for i,c in enumerate(cond,start=1)}, "")
                part,_ = consistency(dummyCKB)
                if (part != False):
                    if len(part) >= t:
                        print('CKB found')
                        break
            QUERIES = []
            for j in range(10):
                while True:
                    Q = sampleConditional(VAR, u,l)
                    q = parseQuery(Q)[1]
                    if checkQuery(CKB,q) and checkQuery(dummyCKB,q):
                        QUERIES.append(q)
                        break
            makeQueryfile(queries,  f'weakcinf2_benchmark/randomqq_{s}_{i}.cl')
            makeCKB(VAR, COND, f'weakcinf2_benchmark/randomsbb__{s}_{i}.cl')
            makeCKB(VAR, COND[f:]+facts, f'weakcinf2_benchmark/randomwbb_{s}_{i}.cl')









if __name__ == "__main__":
    arg = sys.argv[1]
    if arg == '1':
        sampleForLEXbenchmarks()
    if arg == '2':
        sampleForWeakCinfBenchmarkII()
    if arg == '3':
        sampleForWeakCinfBenchmarkI()
