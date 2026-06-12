

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np


def merge(old, new):
    old['time_solve'] = old['time_solve'].replace('Timeout', '600').astype(float)
    new['time_solve'] = new['time_solve'].replace('Timeout', '600').astype(float)
    wst = []
    sst = []
    for idx1, row1 in old.iterrows():
        sID = row1['bb'], row1['query']
        for idx2, row2 in new.iterrows():
            wID = row2['bb'], row2['query']
            if sID == wID:
                if row1['time_solve'] >= 600 or row2['time_solve'] >= 600: continue
                assert row1['result'] == row2['result']
                sst.append(row1['time_solve'])
                wst.append(row2['time_solve'])
    wst = np.array(wst)
    sst = np.array(sst)
    return sst, wst






def myStats(old, new, fname):
    #print(old.values)
    tt = np.sort(old)
    #print(tt)
    targ = np.argsort(old)
    new = new
    nn = new[targ]
    #print(tt)
    plt.plot(np.cumsum(tt) , label='old encoding')
    plt.plot(np.cumsum(nn) , label='new encoding')
    plt.legend()
    plt.savefig(fname)
    plt.clf()


def myeval():
    old1 = pd.read_csv(f'old_results_1.csv')
    old2 = pd.read_csv(f'old_results_2.csv')
    old3 = pd.read_csv(f'old_results_3.csv')
    old = pd.concat([old1,old2,old3], ignore_index=True)
    new1 = pd.read_csv(f'new_results_1.csv')
    new2 = pd.read_csv(f'new_results_2.csv')
    new3 = pd.read_csv(f'new_results_3.csv')
    new = pd.concat([new1,new2,new3], ignore_index=True)
    sst, wst = merge(old, new)
    myStats(sst,wst, f'res_solve.png')

if __name__ == "__main__":
    myeval()

