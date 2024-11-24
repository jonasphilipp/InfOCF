import os
import pandas as pd
from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator
from pathlib import Path

# These setting are only to adjust the display options to show all columns and rows
pd.set_option('display.max_columns', None)
pd.set_option('display.max_rows', None)
pd.set_option('display.width', 0)  


# Here we can choose to select a timeout for inference, preprocessing or the totality of 
# preprocessing + timeout, 0 means no timeout is selected, stricted timeout for computational step
# is always chosen internally by our implementation
total_timeout = 300
preprocessing_timeout = 0
inference_timeout = 0


# Here we can select any smt solver that is currently wrapped by pysmt and installed on the system
# In the provided nix flake induced environment this includes:
# z3, yices, msat, cvc5, ...
smt_solver = 'z3'


# We can also select an partial maxsat solver. Currently only only z3 and rc2 are implemented. Other
# partial maxsat solver using the wcnf format can be implemented rather easily. If rc2 is selected, 
# the internal sat solver can also be chosen by providing sat solver name as string suffix delimited
# by a space from prefix rc2. 
# Names can be found here https://pysathq.github.io/docs/html/api/solvers.html#pysat.solvers.SolverNames
pmaxsat_solver = 'rc2'


# parallel inference for multiple queries is possible. 
multi_inference = False

# read csv file with belief base, query pairs
examples = os.path.join('unittests', 'example_testing.csv')
df = pd.read_csv(examples, header=None)
# we instanciate a DataFrame to store results
all_results = pd.DataFrame()  


for index, row in df.iterrows():
    # set belief_base/queries location
    print(index)
    print(row[0], row[1])
    belief_base_filepath = str(row[0])
    queries_filepath = str(row[1])
    current_dir = os.getcwd()
    belief_base_filepath_full = os.path.join(current_dir, belief_base_filepath)
    queries_filepath_full = os.path.join(current_dir, queries_filepath)
    # parse belief_base/queries
    assert os.path.isfile(belief_base_filepath_full), f"{belief_base_filepath} is not a valid file"
    assert os.path.isfile(queries_filepath_full), f"{queries_filepath} is not a valid file"
    if 'inconsistent' in belief_base_filepath:
        continue
    
    if 'empty' in belief_base_filepath:
        continue

    belief_base = parse_belief_base(belief_base_filepath_full)
    queries = parse_queries(queries_filepath_full)


    # Below we will perform multiple inferenes according to different inference systems and parameter combinations
    #
    # Inference is performed by instanciating InferenceOperator object and calling inference() method

    pent = InferenceOperator(belief_base, inference_system='p-entailment', smt_solver=smt_solver)
    print(f'p-entailment on {belief_base_filepath}, {queries_filepath}')
    results0 = pent.inference(queries, total_timeout=total_timeout, preprocessing_timeout=preprocessing_timeout, inference_timeout=inference_timeout, multi_inference=multi_inference)          
    
    sysz = InferenceOperator(belief_base, inference_system='system-z', smt_solver=smt_solver)
    print(f'system-z inf on {belief_base_filepath}, {queries_filepath}')
    results1 = sysz.inference(queries, total_timeout=total_timeout, preprocessing_timeout=preprocessing_timeout, inference_timeout=inference_timeout, multi_inference=multi_inference)
                
   
    sysw = InferenceOperator(belief_base, inference_system='system-w', smt_solver=smt_solver, pmaxsat_solver=pmaxsat_solver)
    print(f'system-w inf on {belief_base_filepath}, {queries_filepath}')
    results2 = sysw.inference(queries, total_timeout=total_timeout, preprocessing_timeout=preprocessing_timeout, inference_timeout=inference_timeout, multi_inference=multi_inference)

     
    lexinf = InferenceOperator(belief_base, inference_system='lex_inf', smt_solver=smt_solver, pmaxsat_solver=pmaxsat_solver)
    print(f'lex inf  on {belief_base_filepath}, {queries_filepath}')
    results3 = lexinf.inference(queries, total_timeout=total_timeout, preprocessing_timeout=preprocessing_timeout, inference_timeout=inference_timeout, multi_inference=multi_inference)           
    

    cinf = InferenceOperator(belief_base, inference_system='c-inference', smt_solver=smt_solver, pmaxsat_solver=pmaxsat_solver)
    print(f'c-inference  on {belief_base_filepath}, {queries_filepath}')
    results4 = cinf.inference(queries, total_timeout=total_timeout, preprocessing_timeout=preprocessing_timeout, inference_timeout=inference_timeout, multi_inference=multi_inference)           
    
    # concat all results for current loop iteration
    current_results = pd.concat([results0, results1, results2, results3, results4], ignore_index=True)
    current_results['belief_base_filepath'] = belief_base_filepath
    current_results['queries_filepath'] = queries_filepath

    # update result data frame with results from current iteration
    all_results = pd.concat([all_results, current_results], ignore_index=True)

# print without verbose query, belief_base, and queries columns for visibility/display space reasons
print(f"\nmulti_inference {multi_inference}\n")
#print(all_results.drop(columns=['query', 'belief_base', 'queries']))
print(all_results)

# Optionally, save to a CSV file
# uncomment lines below to do so

filename = os.path.join('unittests', 'example_testing_results.csv')
all_results.to_csv(filename, index=False)

