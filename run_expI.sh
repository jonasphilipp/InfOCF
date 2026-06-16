

taskset -c 0 python3 weak_cinf_expI.py 1 50 & 
taskset -c 1 python3 weak_cinf_expI.py 1 75 & 
taskset -c 2 python3 weak_cinf_expI.py 1 100 & 
taskset -c 4 python3 weak_cinf_expI.py 2 50 & 
taskset -c 5 python3 weak_cinf_expI.py 2 75 & 
taskset -c 6 python3 weak_cinf_expI.py 2 100 
