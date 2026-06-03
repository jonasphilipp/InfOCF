

taskset -c 0 python3 weakly_generator.py 1 | taskset -c 1 python3 weakly_generator.py 2 | taskset -c 2 python3 weakly_generator.py 3 
