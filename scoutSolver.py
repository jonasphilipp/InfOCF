from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator, create_inference_instance
from strong_generator import sampleSeededCKB
from time import perf_counter



# parse the belief base and the queries
S=10
R=10
l=4
u=8
seed=1
belief_base =sampleSeededCKB(S,R,l,u,seed)
inference_system = 'c-inference'
inference_operator = InferenceOperator(belief_base, inference_system)
inference_instance = create_inference_instance(inference_operator.epistemic_state)
t1 = perf_counter()
print('preprocessing')
inference_instance.preprocess_belief_base()
t2 = perf_counter()
print(t2-t1)







# results can be saved as csv
# uncomment lines below to do so

#import os
#filename = os.path.join('output', 'show_minimal_results.csv')
#results.to_csv(filename)
