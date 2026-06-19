import sys
from extinf.weakcz3_imp import WeakCz3IMP
from extinf.weakcz3_OLDENC import WeakCz3OLD
from extinf.weakcz3_BRAND import WeakCz3BRAND
import pandas as pd
from parser.Wrappers import parseCKB, parseQuery, parse_queries, parse_belief_base
from time import perf_counter
from multiprocessing import Process, Queue
from inference.inference_operator import InferenceOperator
from inference.belief_base import BeliefBase
from inference.z3tools import *
import z3





def run_exp(folder, outfile, func,myrange):
    #df = pd.DataFrame(columns=['setting', 'signature', 'bb', 'query', 'time_compile', 'time_solve','result'])
    results = []
    for i in myrange:
        query = f'cinf_encoding_benchmark/qq{i}.cl'
        ckb = f'cinf_encoding_benchmark/bb{i}.cl'
        with open(query) as f: query = f.read() 
        with open(ckb) as f: ckb = f.read() 
        
        QUERY = parseQuery(query)
        CKB = parseCKB(ckb)
        inf = func(CKB)
        s=z3.Solver()
        s.set(timeout=600000)
        s.add(inf.base_csp)

        for j,q in QUERY.items():
            q = transform_conditional_to_z3(q)
            q_csp = inf.compile_and_encode_query(q)
            s.push()
            s.add(q_csp)
            t1 = perf_counter()
            res = s.check()
            t2 = perf_counter()
            if res == z3.unknown:
                s.pop()
                r= {'setting':folder, 'bb':i, 'query':j, 'time_solve':'Timeout', 'result':'Timeout'}
                print(r)
                results.append(r)
                continue
            r= {'setting':folder, 'bb':i, 'query':j, 'time_solve':t2-t1, 'result':res}
            print(r)
            results.append(r)
            s.pop()
    df = pd.DataFrame(results)
    df.to_csv(outfile)



if __name__ == "__main__":
    arg = sys.argv[1]
    if arg == '1':
        R = range(1,11)
        algo = 'old'
        func = WeakCz3OLD
        outfile = f'cinf_encoding_benchmark/old_results_1.csv'
        run_exp(algo,outfile,func,R)
    if arg == '2':
        R = range(1,11)
        algo = 'new'
        func = WeakCz3IMP
        outfile = 'cinf_encoding_benchmark/new_results_1.csv'
        run_exp(algo,outfile, func,R)

    if arg == '3':
        R = range(11,21)
        algo = 'old'
        func = WeakCz3OLD
        outfile = f'cinf_encoding_benchmark/old_results_2.csv'
        run_exp(algo,outfile,func,R)
    if arg == '4':
        R = range(11,21)
        algo = 'new'
        func = WeakCz3IMP
        outfile = 'cinf_encoding_benchmark/new_results_2.csv'
        run_exp(algo,outfile, func,R)
    if arg == '5':
        R = range(21,31)
        algo = 'old'
        func = WeakCz3OLD
        outfile = f'cinf_encoding_benchmark/old_results_3.csv'
        run_exp(algo,outfile,func,R)
    if arg == '6':
        R = range(21,31)
        algo = 'new'
        func = WeakCz3IMP
        outfile = 'cinf_encoding_benchmark/new_results_3.csv'
        run_exp(algo,outfile, func,R)

    if arg == '7':
        R = range(1,11)
        algo = 'brand'
        func = WeakCz3BRAND
        outfile = 'cinf_encoding_benchmark/brand_results_1.csv'
        run_exp(algo,outfile, func,R)

    if arg == '8':
        R = range(11,21)
        algo = 'brand'
        func = WeakCz3BRAND
        outfile = 'cinf_encoding_benchmark/brand_results_2.csv'
        run_exp(algo,outfile, func,R)

    if arg == '9':
        R = range(21,31)
        algo = 'brand'
        func = WeakCz3BRAND
        outfile = 'cinf_encoding_benchmark/brand_results_3.csv'
        run_exp(algo,outfile, func,R)
