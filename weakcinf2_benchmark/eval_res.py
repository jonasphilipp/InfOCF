

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

def merge(old, new):
    old['time_compile'] = old['time_compile'].replace('Timeout', '600').astype(float)
    new['time_compile'] = new['time_compile'].replace('Timeout', '600').astype(float)
    old['time_solve'] = old['time_solve'].replace('Timeout', '600').astype(float)
    new['time_solve'] = new['time_solve'].replace('Timeout', '600').astype(float)
    wct = []
    sct = []
    wst = []
    sst = []
    for idx1, row1 in old.iterrows():
        sID = row1['signature'], row1['bb'], row1['query']
        for idx2, row2 in new.iterrows():
            wID = row2['signature'], row2['bb'], row2['query']
            if sID == wID:
                sct.append(row1['time_compile'])
                wct.append(row2['time_compile'])
                if sct[-1]>= 600 or wct[-1]>= 600:
                    continue
                sst.append(row1['time_solve'])
                wst.append(row2['time_solve'])
    wct = np.array(wct)
    sct = np.array(sct)
    wst = np.array(wst)
    sst = np.array(sst)
    return sct, wct, sst, wst






def myStats(old, new, fname):
    #print(old.values)
    tt = np.sort(old)
    #print(tt)
    targ = np.argsort(old)
    new = new
    nn = new[targ]
    #print(tt)
    plt.plot(tt , label='strongly consistent')
    plt.plot(nn , label='weakly consistent')
    plt.legend()
    plt.savefig(fname)
    plt.clf()


def myeval(s):
    old = pd.read_csv(f'strong_results_{s}.csv')
    new = pd.read_csv(f'weak_results_{s}.csv')
    sct, wct, sst, wst = merge(old, new)
    myStats(sct, wct, f'res_compile_{s}.png')
    myStats(sst, wst, f'res_solve_{s}.png')

if __name__ == "__main__":
    myeval(50)
    myeval(80)
    myeval(110)

