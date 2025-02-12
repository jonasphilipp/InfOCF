import os
import sys


# Define base directory relative to this test file's location
BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(BASE_DIR)

import pandas as pd
from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator

# These setting are only to adjust the display options to show all columns and rows
pd.set_option('display.max_columns', None)
pd.set_option('display.max_rows', None)
pd.set_option('display.width', 0)

# inference systems to be tested
inference_systems = ['p-entailment', 'system-z', 'system-w', 'lex_inf', 'c-inference']

# Put any inference system that should be excluded from testing here
excluded_systems = []

test_sets = ['example_testing_results.csv']

# Skip test cases:
# - 'inconsistent' files: These contain intentionally inconsistent belief bases
# - 'empty' files: These contain empty belief bases
SKIP_CONDITIONS = ['inconsistent', 'empty']


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

for test_set in test_sets:
    # read csv file with belief base, query pairs - make path relative to test file location
    examples = os.path.join(os.path.dirname(__file__), test_set)
    df = pd.read_csv(examples)
    # we instanciate a DataFrame to store results
    collected_results = pd.DataFrame()  
    belief_base_filepath = ''
    queries_filepath = ''
    last_index = -1

    for index, row in df.iterrows():

        if row['belief_base_filepath'] != belief_base_filepath or row['queries_filepath'] != queries_filepath:
            collected_results = pd.DataFrame()  
            belief_base_filepath = str(row['belief_base_filepath'])
            queries_filepath = str(row['queries_filepath'])
            
            belief_base_filepath_full = os.path.join(BASE_DIR, belief_base_filepath)
            queries_filepath_full = os.path.join(BASE_DIR, queries_filepath)
            # parse belief_base/queries
            assert os.path.isfile(belief_base_filepath_full), f"{belief_base_filepath} is not a valid file"
            assert os.path.isfile(queries_filepath_full), f"{queries_filepath} is not a valid file"
            if 'inconsistent' in belief_base_filepath:
                continue
            
            if 'empty' in belief_base_filepath:
                continue

            # Skip files based on defined conditions
            if any(condition in belief_base_filepath for condition in SKIP_CONDITIONS):
                continue

            belief_base = parse_belief_base(belief_base_filepath_full)
            queries = parse_queries(queries_filepath_full)


            # Below we will perform multiple inferenes according to different inference systems and parameter combinations
            #
            # Inference is performed by instanciating InferenceOperator object and calling inference() method

            for inference_system in inference_systems:
                if inference_system == 'lex_inf':
                    inference_operator = InferenceOperator(belief_base, inference_system=inference_system, smt_solver=smt_solver, pmaxsat_solver='z3')
                else:
                    inference_operator = InferenceOperator(belief_base, inference_system=inference_system, smt_solver=smt_solver, pmaxsat_solver=pmaxsat_solver)
                print(f'{inference_system:<20} on {belief_base_filepath}, {queries_filepath}')
                results = inference_operator.inference(queries, total_timeout=total_timeout, preprocessing_timeout=preprocessing_timeout, inference_timeout=inference_timeout, multi_inference=multi_inference)          
                    

                # update result data frame with results from current iteration
                collected_results = pd.concat([collected_results, results], ignore_index=True)
        
        # Fix: Filter collected_results instead of df
        current_result = collected_results[
            (collected_results['belief_base'] == row['belief_base']) & 
            (collected_results['query'] == row['query'])
        ]
        assert not current_result.empty, f"No result found for belief_base: {row['belief_base']} and query: {row['query']}"

            
        for inference_system in inference_systems:
            system_results = current_result[current_result['inference_system'] == inference_system]
            # Check that we have results for this inference system
            assert not system_results.empty, f"No result found for inference_system: {inference_system}"
            
            # If this is the inference system we're comparing against, verify the result
            if inference_system == row['inference_system']:
                assert index == last_index + 1, f"Index mismatch: {index} != {last_index + 1}"
                if inference_system in excluded_systems:
                    print('result not compared, inference system excluded')
                else:
                    assert system_results.iloc[0]['result'] == row['result'], (
                        f"Result mismatch for belief_base: {row['belief_base']}, "
                        f"query: {row['query']}, inference_system: {inference_system}. "
                        f"Expected: {row['result']}, Got: {system_results.iloc[0]['result']}"
                        f"row of test set: {row}"
                        f"system_results: {system_results}"
                    )
                last_index = index

print(f'All tests passed for inference systems {inference_systems} on test sets implied by {test_sets}')
if excluded_systems:
    print(f'results not compared for excluded_systems {excluded_systems}')
