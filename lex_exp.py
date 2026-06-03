from inference.lex_inf_z3 import LexInfZ3
from extinf.weaklexinf import LexInf
from func_timeout import func_timeout, FunctionTimedOut
import pandas as pd
from parser.Wrappers import parseCKB, parseQuery
from time import perf_counter

def run_exp(algo, func, outfile):
    df = pd.DataFrame(columns=['algorithm','bb', 'query', 'time', 'result'])
    folder = 'lex_benchmark/'
    results = []
    for i in range(20):
        ckb = f'lex_benchmark/randomqq_{i}.cl')
        query = f'lex_benchmark/randombb_{i}.cl')
        QUERY = parseQuery(query)
        CKB = parseCKB(ckb)
        inf = func(CKB)
        for j,q in enumerate(QUERY):
            try:
                t1 = perf_counter()
                res = func_timeout(60, inf.inference, args=q)
                t2 = perf_counter()
            except FunctionTimedOut:
                r= {'algorithm':algo,'bb':i, 'query':j, 'time':'Timeout', 'result':'Timeout'}
                results.append(r)
                continue
            r= {'algorithm':algo,'bb':i, 'query':j, 'time':t2-t1, 'result':res}
            results.append(r)
    df = pd.concat([df,results])
    df.to_csv(outfile)


if __name__ == "__main__":
    arg = sys.argv[1]
    if arg == '1':
        algo = 'old'
        func = LexInfZ3
        outfile = 'lex_benchmark/old_results.csv'
        run_exp(algo,func, outfile)
    if arg == '2':
        algo = 'new'
        func = LexInf
        outfile = 'lex_benchmark/new_results.csv'
        run_exp(algo,func, outfile)
        














