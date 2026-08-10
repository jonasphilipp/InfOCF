from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator, create_epistemic_state
from inference.c_inference import CInference
from time import perf_counter

for i in range(1,10):
    bbf = f'../Cinference/examples/random_large/randomTest_120_120_{i}.cl'
    with open(bbf) as f:
        belief_base_string = f.read()
    bb = parse_belief_base(belief_base_string)
    inference_system = 'c-inference'
    es = create_epistemic_state(bb, "c-inference", "z3", "rc2")
    c_inf = CInference(es)
    t1=perf_counter()
    c_inf.preprocess_belief_base(0)
    t2=perf_counter()
    print(t2-t1)

