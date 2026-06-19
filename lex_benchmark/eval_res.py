

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np



def myeval():
    old = pd.read_csv('old_results.csv')
    new = pd.read_csv('new_results.csv')
    told = old['time_solve']
    tnew = new['time_solve']
    tt = np.sort(told)
    targ = np.argsort(told)
    nn = tnew.values[targ]
    print(tt)
    print(nn)
    plt.xlabel('query')
    plt.ylabel('time (sec)')
    plt.plot(tt, label='old algorithm')
    plt.plot(nn, label='new algorithm')
    #plt.show()
    plt.legend()
    plt.yscale('log')
    plt.savefig('told.png')
    print(type(told))

myeval()

