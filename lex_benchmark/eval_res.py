

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
    nn = tnew[targ]
    plt.plot(tt)
    plt.plot(nn)
    #plt.show()
    plt.savefig('told.png')
    print(type(told))

myeval()

