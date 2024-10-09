from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator
import pandas as pd


# Adjust the display options to show all columns and rows
pd.set_option('display.max_columns', None)
pd.set_option('display.max_rows', None)
pd.set_option('display.width', 0)  

timeout = 300

# z3, yices, msat, cvc5, ...
solver = 'z3'
alt_solver = 'cvc5'

optimizer = 'rc2 g3'

# parallel query inference
multi_inference = False

all_results = pd.DataFrame()  
for j in [60]:
    for i in [80]:
        for l in range(13, 14):
            belief_base_string = f'./sum_bench/randomTest_{i}_{j}_{l}.cl'
            querystring = f'./sum_bench/randomQueries_{i}_{j}_{l}.cl'

            belief_base = parse_belief_base(belief_base_string)
            queries = parse_queries(querystring)
              
            pent = InferenceOperator(belief_base, inference_system='p-entailment', solver=solver)
            print(f'p-entailment on {i} {j} {l}')
            results0 = pent.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)          
            
            sysz = InferenceOperator(belief_base, inference_system='system-z', solver=solver)
            print(f'system-z inf on {i} {j} {l}')
            results1 = sysz.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)
                        
            sysz = InferenceOperator(belief_base, inference_system='system-z', solver=alt_solver)
            print(f'system-z inf on {i} {j} {l}')
            results2 = sysz.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)
           
            sysw = InferenceOperator(belief_base, inference_system='system-w', solver=solver, optimizer='z3')
            print(f'system-w inf on {i} {j} {l}')
            results3 = sysw.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)
 
            sysw = InferenceOperator(belief_base, inference_system='system-w', solver=solver, optimizer=optimizer)
            print(f'system-w inf on {i} {j} {l}')
            results4 = sysw.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)                       
             
            cinf = InferenceOperator(belief_base, inference_system='c-inference', solver=solver, optimizer=optimizer)
            print(f'c-inference  on {i} {j} {l}')
            results5 = cinf.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)           
            
            cinf = InferenceOperator(belief_base, inference_system='c-inference', solver=alt_solver, optimizer=optimizer)
            print(f'c-inference  on {i} {j} {l}')
            results6 = cinf.inference(queries, preprocessing_timeout=timeout, inference_timeout=timeout, multi_inference=multi_inference)
            
            current_results = pd.concat([results0, results1, results2, results3, results4, results5, results6], ignore_index=True)
            all_results = pd.concat([all_results, current_results], ignore_index=True)

# print without verbose query column for space reasons

print(f"\nmulti_inference {multi_inference}\n")
print(all_results.drop(columns=['query']))

# Optionally, save to a CSV file

#filename = 'output/show_results.csv'
#all_results.to_csv(filename, index=False)

