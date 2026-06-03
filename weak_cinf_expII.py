from extinf.weakcz3_imp import WeakCz3IMP
from func_timeout import func_timeout, FunctionTimedOut
import pandas as pd
from parser.Wrappers import parseCKB, parseQuery
from time import perf_counter

def run_exp(folder, outfile):
    df = pd.DataFrame(columns=['setting', 'signature', 'bb', 'query', 'time_compile', 'time_solve','result'])
    results = []
    for s in [50,80,110,140]:
        for i in range(10):
            ckb = f'weakcinf2_benchmark/randomqq_{s}_{i}.cl')
            query = f'weakcinf2_benchmark/random{folder}bb_{s}_{i}.cl')
            QUERY = parseQuery(query)
            CKB = parseCKB(ckb)
            inf = WeakCz3IMP(CKB)
            tc1=perf_counter()
            inf.compile_constraint()
            tc2 = perf_counter()
            for j,q in enumerate(QUERY):
                try:
                    t1 = perf_counter()
                    res = func_timeout(600, inf.inference, args=q)
                    t2 = perf_counter()
                except FunctionTimedOut:
                    r= {'setting':folder,'signature':s, 'bb':i, 'query':j, 'time_compile':tc2-tc1, 'time_solve':'Timeout', 'result':'Timeout'}
                    results.append(r)
                    continue
                r= {'setting':folder,'signature':s, 'bb':i, 'query':j, 'time_compile':tc2-tc1, 'time_solve':t2-t1, 'result':res}
                results.append(r)
    df = pd.concat([df,results])
    df.to_csv(outfile)


if __name__ == "__main__":
    arg = sys.argv[1]
    if arg == '1':
        folder = 'w'
        outfile = 'weakcinf2_benchmark/weak_results.csv'
        run_exp(folder, outfile)
    if arg == '2':
        folder = 's'
        outfile = 'weakcinf2_benchmark/strong_results.csv'
        run_exp(folder, outfile)
        














