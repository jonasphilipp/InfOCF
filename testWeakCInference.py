from parser.Wrappers import parse_belief_base, parse_queries
from inference.inference_operator import InferenceOperator, create_inference_instance
from strong_generator import sampleSeededCKB, createVariables, sampleConditional
from interim_generator import sampleSeededWeakCKB
from time import perf_counter
from extinf.weakcz3_imp import WeakCz3IMP
from extinf.weaklexinf import LexInf
from extinf.weak_p_entailment import ExtendedPEntailment

class Dummy:
    def __init__(self, conditionals):
        self.conditionals=conditionals
        self.name = ''


def runTests(S,R,l,u,seed):
    strong_bb =sampleSeededCKB(S,R,l,u,seed)
    weak_bb =sampleSeededCKB(S,R,l,u,seed)
    VARS = createVariables(S)
    queries = {i:parse_queries(sampleConditional(VARS,l,u))[1] for i in range(1,51)}
    queries = Dummy(queries)

    inference_system = 'c-inference'
    old_cinf = InferenceOperator(strong_bb, inference_system)
    legacy_results = old_cinf.inference(queries)
    new_cinf_S = WeakCz3IMP(strong_bb)
    #check Direct Inference when BB is strongly consistent
    for i,c in strong_bb.conditionals.items():
        assert new_cinf_S.inference(c), 'direct inference violated for strong BB'
    #check that new c inference implementation yields same result as
    #old c inference implementation when BB is strongly consistent
    for i,q in queries.conditionals.items():
        new_result = (new_cinf_S.inference(q))
        T = legacy_results['index'] == i
        LR = legacy_results[T]['result']
        assert new_result == LR[i-1], 'results mismatched'
        ##TODO match that panda inerface

    new_cinf_W = WeakCz3IMP(weak_bb)
    lexinf = LexInf(weak_bb)
    sysp = ExtendedPEntailment(weak_bb)
    #check Direct Inference when BB is weakly consistent
    for i,c in weak_bb.conditionals.items():
        assert new_cinf_W.inference(c), 'direct inference violated for weak BB'
    #Check that P implies C
    #Check that Not Lex implies Not C
    for i,q in queries.conditionals.items():
        c_result = (new_cinf_S.inference(q))
        p_result = sysp.inference(q)
        lex_result = lexinf.inference(q)
        if not lex_result:
            assert not c_result, "lex does not hold but c does"
            assert not p_result, "lex does not hold but p does"
        if p_result:
            assert c_result, "p holds but c does not"
            assert lex_result, "p holds but lex does not"
        if not c_result:
            assert not p_result, "c does not hold but p does"
        if  c_result:
            assert lex_result, "c does hold but lex does not"
        print(p_result,c_result,lex_result)


for S in [10,15,20,25,30]:
    R = S
    l=1
    u=8
    for i in range(10):
        print(S,R,i)
        runTests(S,R,l,u,i)


