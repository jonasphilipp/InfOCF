import sys
from extinf.weakcz3_imp import WeakCz3IMP
import pandas as pd
from parser.Wrappers import parseCKB, parseQuery, parse_queries, parse_belief_base
from time import perf_counter
from multiprocessing import Process, Queue
from inference.lex_inf_z3 import LexInfZ3
from inference.belief_base import BeliefBase
from inference.inference_operator import InferenceOperator
from extinf.weaklexinf import LexInf



class TimeoutException(Exception):
    pass

def wrapper(queue, f,q):
    r = f(q)
    queue.put(r)


def wrapper2(queue, f,q,a,b):
    r = f(q,a,b)
    queue.put(r)

def func_timeout(my_function, my_args):
    Q = Queue()
    p = Process(target=wrapper, args=(Q,my_function,my_args,))
    p.start()

    p.join(timeout=60)

    if p.is_alive():
        p.terminate()
        p.join()
        raise TimeoutException()
    else:
        r =(Q.get())
        return r



def func_timeout2(my_function, my_args, a ,b ):
    Q = Queue()
    p = Process(target=wrapper2, args=(Q,my_function,my_args,a,b))
    p.start()

    p.join(timeout=60)

    if p.is_alive():
        p.terminate()
        p.join()
        raise TimeoutException()
    else:
        r =(Q.get())
        return r


def run_exp(folder, outfile, func):
    #df = pd.DataFrame(columns=['setting', 'signature', 'bb', 'query', 'time_compile', 'time_solve','result'])
    results = []
    for _ in [1]:
        for i in range(20):
            query = f'lex_benchmark/randomqq_{i}.cl'
            ckb = f'lex_benchmark/randombb_{i}.cl'
            with open(query) as f: query = f.read() 
            with open(ckb) as f: ckb = f.read() 
            
            QUERY = parseQuery(query)
            CKB = parseCKB(ckb)
            inf = func(CKB)
            for j,q in QUERY.items():
                try:
                    t1 = perf_counter()
                    if folder == 'old':
                        QQ = BeliefBase([],{0:q},"")
                        res = inf.inference(QQ, 1000000, False)
                        res = res['result'][0]
                        print('old lex')
                        print(res)
                    else:
                        res = inf.inference(q)
                        print('new lex')
                        print(res)
                    t2 = perf_counter()
                except TimeoutException:
                    r= {'setting':folder, 'bb':i, 'query':j, 'time_solve':'Timeout', 'result':'Timeout'}
                    print(r)
                    results.append(r)
                    continue
                r= {'setting':folder, 'bb':i, 'query':j, 'time_solve':t2-t1, 'result':res}
                print(r)
                results.append(r)
    df = pd.DataFrame(results)
    df.to_csv(outfile)




if __name__ == "__main__":
    arg = sys.argv[1]
    if arg == '1':
        algo = 'old'
        #func = LexInfZ3
        func = lambda belief_base: InferenceOperator(belief_base, 'lex_inf')
        outfile = 'lex_benchmark/old_results.csv'
        run_exp(algo, outfile ,func)
    if arg == '2':
        algo = 'new'
        func = LexInf
        outfile = 'lex_benchmark/new_results.csv'
        run_exp(algo,outfile ,func)
        














