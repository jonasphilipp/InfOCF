





import os
import shutil
import pathlib


S = [i for i in range(0,110,10)]
ind = [i for i in range(0,101)]
count = 1

for s in S:
    for j in ind:
        bb = f'foiks/folks/randomTest_{s}_{s}_{j}.cl'
        qq  = f'foiks/folks/randomQueries_{s}_{s}_{j}.cl'
        targetbb = f'combined/bb{count}.cl'
        targetqq= f'combined/qq{count}.cl'

        if os.path.isfile(f'foiks/folks/randomTest_{s}_{s}_{j}.cl'):
            shutil.copy(bb, targetbb)
            shutil.copy(qq, targetqq)
            count+=1

for s in S:
    for j in ind:
        bb = f'sum/randomTest_{s}_{s}_{j}.cl'
        qq  = f'sum/randomQueries_{s}_{s}_{j}.cl'
        targetbb = f'combined/bb{count}.cl'
        targetqq= f'combined/qq{count}.cl'

        if os.path.isfile(f'sum/randomTest_{s}_{s}_{j}.cl'):
            shutil.copy(bb, targetbb)
            shutil.copy(qq, targetqq)
            count+=1
