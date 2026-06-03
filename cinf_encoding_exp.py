from inference.c_inference import CInference
from extinf.weakcz3_imp import WeakCz3IMP
from func_timeout import func_timeout, FunctionTimedOut
import pandas as pd
from parser.Wrappers import parseCKB, parseQuery
from time import perf_counter

def run_exp(algo, func, outfile):
    df = pd.DataFrame(columns=['algorithm','bb', 'query', 'time', 'result'])
    results = []
    for i in range(32):
        ckb = f'cinf_encoding_benchmark/qq_{i}.cl')
        query = f'cinf_encoding_benchmark/bb_{i}.cl')
        QUERY = parseQuery(query)
        CKB = parseCKB(ckb)
        inf = func(CKB)
        inf.compile_constraint()
        for j,q in enumerate(QUERY):
            try:
                t1 = perf_counter()
                res = func_timeout(600, inf.inference, args=q)
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
        func = CInference
        outfile = 'cinf_encoding_benchmark/old_results.csv'
        run_exp(algo,func, outfile)
    if arg == '2':
        algo = 'new'
        func = WeakCz3IMP
        outfile = 'cinf_encoding_benchmark/new_results.csv'
        run_exp(algo,func, outfile)
        














