

#taskset -c 0 python3 lex_exp_new.py 1  & 
#taskset -c 1 python3 lex_exp_new.py 2  
#taskset -c 1 python3 cinf_encoding_new_exp.py 1 &
#taskset -c 2 python3 cinf_encoding_new_exp.py 2  &
#taskset -c 3 python3 cinf_encoding_new_exp.py 3 &
#taskset -c 4 python3 cinf_encoding_new_exp.py 4 &
#taskset -c 5 python3 cinf_encoding_new_exp.py 5 &
#taskset -c 6 python3 cinf_encoding_new_exp.py 6 

taskset -c 1 python3 cinf_encoding_new_exp.py 7 
taskset -c 2 python3 cinf_encoding_new_exp.py 8 
taskset -c 3 python3 cinf_encoding_new_exp.py 9
taskset -c 4 python3 cinf_encoding_new_exp.py 10 
taskset -c 5 python3 cinf_encoding_new_exp.py 11
taskset -c 6 python3 cinf_encoding_new_exp.py 12
