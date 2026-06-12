

taskset -c 1 python3 weakly_generator.py 2 50 & 
taskset -c 2 python3 weakly_generator.py 2 75 &
taskset -c 3 python3 weakly_generator.py 2 100 
