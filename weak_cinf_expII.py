import sys
from extinf.weakcz3_imp import WeakCz3IMP, TimeoutException
import pandas as pd
from parser.Wrappers import parseCKB, parseQuery, parse_queries, parse_belief_base
from time import perf_counter
from multiprocessing import Process, Queue
from inference.z3tools import *
import z3




def run_exp(folder, outfile, S):
    #df = pd.DataFrame(columns=['setting', 'signature', 'bb', 'query', 'time_compile', 'time_solve','result'])
    results = []
    for s in [S]:
        for i in range(10):
            print(f'running {s,i,folder}') 
            query = f'weakcinf1_benchmark/randomqq_{s}_{i}.cl'
            ckb = f'weakcinf1_benchmark/random{folder}bb_{s}_{i}.cl'
            with open(query) as f: query = f.read() 
            with open(ckb) as f: ckb = f.read() 
            
            QUERY = parseQuery(query)
            CKB = parseCKB(ckb)
            tc1=perf_counter()
            try:
                inf = WeakCz3IMP(CKB)
            except TimeoutException:
                r= {'setting':folder,'signature':s, 'bb':i, 'query':-1, 'time_compile':'Timeout', 'query_compile': 'Timeout', 'time_solve':'Timeout', 'result':'Timeout'}
                print(r)
                continue

            tc2 = perf_counter()
            ss=z3.Solver()
            ss.set(timeout=600000)
            ss.add(inf.base_csp)
            for j,q in QUERY.items():
                q = transform_conditional_to_z3(q)
                qt1=perf_counter()
                try:
                    q_csp = inf.compile_and_encode_query(q)
                except TimeoutException:
                    r= {'setting':folder,'signature':s, 'bb':i, 'query':j, 'time_compile':tc2-tc1, 'query_compile': 'Timeout', 'time_solve':'Timeout', 'result':'Timeout'}
                    print(r)
                    continue
                qt2=perf_counter()
                ss.push()
                ss.add(q_csp)
                t1 = perf_counter()
                res = ss.check()
                t2 = perf_counter()
                if res == z3.unknown:
                    r= {'setting':folder,'signature':s, 'bb':i, 'query':j, 'time_compile':tc2-tc1, 'query_compile': qt2-qt1, 'time_solve':'Timeout', 'result':'Timeout'}
                    print(r)
                    results.append(r)
                    ss.pop()
                    continue
                r= {'setting':folder,'signature':s, 'bb':i, 'query':j, 'time_compile':tc2-tc1, 'query_compile': qt2-qt1,'time_solve':t2-t1, 'result':res}
                print(r)
                results.append(r)
                ss.pop()
    df = pd.DataFrame(results)
    df.to_csv(outfile)


if __name__ == "__main__":
    arg = sys.argv[1]
    s = int(sys.argv[2])
    if arg == '1':
        folder = 'w'
        outfile = f'weakcinf1_benchmark/weak_results_{s}.csv'
        run_exp(folder, outfile,s)
    if arg == '2':
        folder = 's'
        outfile = f'weakcinf1_benchmark/strong_results_{s}.csv'
        run_exp(folder, outfile,s)
        














