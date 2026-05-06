
Creates somewhat random, large CKB's, which are used to benchmark how fast the compillation algorithm is.
No interface implemented at the moment, change the parameters in `sampling.py`, then run `python sampling.py`



### upperBound.py
the method 'sampling' takes as input a list of variables (represented as strings), and a filename.
If the amount of variables is n, it prints into the file with the filename a CKB, such that 2^(n-1)
is the smallest possible solution for at least one eta.
See `Nonmonotonic reasoning from conditional knowledge bases with system W` from Komo and Beierle for
the theoretical details


### sampling.py
Attempts to model CKB's with a lot of 'exceptions within exceptions within exceptions' behavior.

### trueRandomSampling.py
Creates entirely random CKB's.
