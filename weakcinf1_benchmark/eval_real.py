import sys
sys.path.insert(0, '../extinf/')
sys.path.insert(0, '../parser/')
sys.path.insert(0, '..')

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
from extinf.ezp import test_weakly, getEZP, get_J_delta, EZP
from parser.Wrappers import parseQuery,parseCKB


def J(mypath):
    with open(mypath) as f:
        ckbpath = f.read()
    ckb = parseCKB(ckbpath)
    ezp = EZP(ckb)
    return len(get_J_delta(ezp))

def merge(old, new):
    old['time_compile'] = old['time_compile'].replace('Timeout', '600').astype(float)
    new['time_compile'] = new['time_compile'].replace('Timeout', '600').astype(float)
    old['time_solve'] = old['time_solve'].replace('Timeout', '600').astype(float)
    new['time_solve'] = new['time_solve'].replace('Timeout', '600').astype(float)
    print('solved weak',sum((new['time_solve'] < 599.9).values))
    print('solved strong',sum((old['time_solve'] < 599.9).values))
    print('compiled weak ', sum((new['time_compile'] < 599.9).values))
    print('compiled strong', sum((old['time_compile'] < 599.9).values))
    wct = []
    sct = []
    wst = []
    sst = []
    for idx1, row1 in old.iterrows():
        sID = row1['signature'], row1['bb'], row1['query']

        for idx2, row2 in new.iterrows():
            wID = row2['signature'], row2['bb'], row2['query']
            if sID == wID:
                if row2['time_compile']>= 600 or row1['time_compile']>= 600:
                    continue
                sct.append(row1['time_compile'])
                wct.append(row2['time_compile'])
                if row2['time_solve']>= 600 or row1['time_solve']>= 600:
                    continue
                sst.append(row1['time_solve'])
                wst.append(row2['time_solve'])
    wct = np.array(wct)
    sct = np.array(sct)
    wst = np.array(wst)
    sst = np.array(sst)
    print('shared solve', len(wst))
    print('shared compile', len(wct))
    print('---------')

    return sct, wct, sst, wst






def myStats(old, new, fname, labelX):
    #print(old.values)
    tt = np.sort(old)
    #print(tt)
    targ = np.argsort(old)
    new = new
    nn = new[targ]
    #print(tt)
    plt.xlabel(labelX, fontsize=18)
    plt.ylabel('time (sec)',fontsize=18)
    plt.xticks(fontsize=18)
    plt.yticks(fontsize=18)
    plt.plot(tt , label='strongly consistent')
    plt.plot(nn , label='weakly consistent')
    plt.legend(fontsize=18)
    plt.yscale('log')
    plt.savefig(fname, dpi=300,bbox_inches='tight')
    plt.clf()


def plotJ(res, J, fname):
    #print(old.values)
    tt = np.sort(res)
    #print(tt)
    targ = np.argsort(res)
    
    nn = J[targ]
    #print(tt)
    plt.plot(nn)
    plt.savefig(fname)
    plt.clf()


def myeval(s):
    old = pd.read_csv(f'strong_results_{s}.csv')
    new = pd.read_csv(f'weak_results_{s}.csv')
    sct, wct, sst, wst = merge(old, new)
    myStats(np.unique(sct), np.unique(wct), f'res_compile_{s}.png', 'belief base')
    myStats(sst, wst, f'res_solve_{s}.png', 'query')

if __name__ == "__main__":
    myeval(50)
    myeval(75)
    myeval(100)

