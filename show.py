# In this file we demonstrate the use of the InfOCF library to perform multiple inferences according
# to a variety of inference systems with differing solvers while setting other optional parameters
# iterating over belief base and query files and concatenating the results.
#
# This represented a common usecase while evaluating and comparing the different inference systems
# and solvers. For a more minimalistic presentation please refer to show_minimal.py


import os

import pandas as pd

from inference.inference_operator import InferenceOperator
from parser.Wrappers import parse_belief_base, parse_queries

# These setting are only to adjust the display options to show all columns and rows
pd.set_option("display.max_columns", None)
pd.set_option("display.max_rows", None)
pd.set_option("display.width", 0)


# Here we can choose to select a timeout for inference, preprocessing or the totality of
# preprocessing + timeout, 0 means no timeout is selected, stricted timeout for computational step
# is always chosen internally by our implementation
total_timeout = 300
preprocessing_timeout = 0
inference_timeout = 0


# Here we can select any smt solver that is currently wrapped by pysmt and installed on the system
# In the provided nix flake induced environment this includes:
# z3, yices, msat, cvc5, ...
smt_solver = "z3"
alt_smt_solver = "cvc5"


# We can also select an partial maxsat solver. Currently only only z3 and rc2 are implemented. Other
# partial maxsat solver using the wcnf format can be implemented rather easily. If rc2 is selected,
# the internal sat solver can also be chosen by providing sat solver name as string suffix delimited
# by a space from prefix rc2.
# Names can be found here https://pysathq.github.io/docs/html/api/solvers.html#pysat.solvers.SolverNames
pmaxsat_solver = "rc2"
alt_pmaxsat_solver = "rc2 g4"


# parallel inference for multiple queries is possible.
multi_inference = False

# we instanciate a DataFrame to store results
all_results = pd.DataFrame()

# itration over signature sizes and number conditionals and belief base/ query index
# dependend on actual naming of belief bases and queries
for j in [60]:
    for i in [60]:
        for l in range(13, 16):
            # set belief_base/queries location
            belief_base_filename = os.path.join(
                "examples", "random_large", f"randomTest_{i}_{j}_{l}.cl"
            )
            queries_filename = os.path.join(
                "examples", "random_large", f"randomQueries_{i}_{j}_{l}.clq"
            )
            # assert that belief_base_filename and queries_filename exist
            assert os.path.exists(
                belief_base_filename
            ), f"belief_base_filename {belief_base_filename} does not exist"
            assert os.path.exists(
                queries_filename
            ), f"queries_filename {queries_filename} does not exist"
            # parse belief_base/queries
            belief_base = parse_belief_base(belief_base_filename)
            queries = parse_queries(queries_filename)

            # Below we will perform multiple inferenes according to different inference systems and parameter combinations
            #
            # Inference is performed by instanciating InferenceOperator object and calling inference() method

            pent = InferenceOperator(
                belief_base, inference_system="p-entailment", smt_solver=smt_solver
            )
            print(f"p-entailment on {i} {j} {l}")
            results0 = pent.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            sysz = InferenceOperator(
                belief_base, inference_system="system-z", smt_solver=smt_solver
            )
            print(f"system-z inf on {i} {j} {l}")
            results1 = sysz.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            sysz = InferenceOperator(
                belief_base, inference_system="system-z", smt_solver=alt_smt_solver
            )
            print(f"system-z inf on {i} {j} {l}")
            results2 = sysz.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            sysw = InferenceOperator(
                belief_base,
                inference_system="system-w",
                smt_solver=smt_solver,
                pmaxsat_solver="z3",
            )
            print(f"system-w inf on {i} {j} {l}")
            results3 = sysw.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            sysw = InferenceOperator(
                belief_base,
                inference_system="system-w",
                smt_solver=smt_solver,
                pmaxsat_solver=pmaxsat_solver,
            )
            print(f"system-w inf on {i} {j} {l}")
            results4 = sysw.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            lexinf = InferenceOperator(
                belief_base,
                inference_system="lex_inf",
                smt_solver=smt_solver,
                pmaxsat_solver=pmaxsat_solver,
            )
            print(f"lex inf  on {i} {j} {l}")
            results5 = lexinf.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            lexinf = InferenceOperator(
                belief_base,
                inference_system="lex_inf",
                smt_solver=alt_smt_solver,
                pmaxsat_solver=alt_pmaxsat_solver,
            )
            print(f"lex inf  on {i} {j} {l}")
            results6 = lexinf.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            cinf = InferenceOperator(
                belief_base,
                inference_system="c-inference",
                smt_solver=smt_solver,
                pmaxsat_solver=pmaxsat_solver,
            )
            print(f"c-inference  on {i} {j} {l}")
            results7 = cinf.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            cinf = InferenceOperator(
                belief_base,
                inference_system="c-inference",
                smt_solver=alt_smt_solver,
                pmaxsat_solver=alt_pmaxsat_solver,
            )
            print(f"c-inference  on {i} {j} {l}")
            results8 = cinf.inference(
                queries,
                total_timeout=total_timeout,
                preprocessing_timeout=preprocessing_timeout,
                inference_timeout=inference_timeout,
                multi_inference=multi_inference,
            )

            # concat all results for current loop iteration
            current_results = pd.concat(
                [
                    results0,
                    results1,
                    results2,
                    results3,
                    results4,
                    results5,
                    results6,
                    results7,
                    results8,
                ],
                ignore_index=True,
            )
            # update result data frame with results from current iteration
            all_results = pd.concat([all_results, current_results], ignore_index=True)

# print without verbose query, belief_base, and queries columns for visibility/display space reasons
print(f"\nmulti_inference {multi_inference}\n")
print(all_results.drop(columns=["query", "belief_base", "queries"]))

# Optionally, save to a CSV file
# uncomment lines below to do so

# filename = os.path.join('output', 'show_results.csv')
# all_results.to_csv(filename, index=False)
