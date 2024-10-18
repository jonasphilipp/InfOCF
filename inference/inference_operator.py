import pandas as pd
from pysmt.environment import get_env
from inference.belief_base import BeliefBase
from inference.system_w import  SystemW
from inference.system_w_z3 import SystemWZ3
from inference.system_z import SystemZ
from inference.p_entailment import PEntailment
from inference.c_inference import CInference
from inference.queries import Queries


def create_epistemic_state(belief_base: BeliefBase, inference_system: str, solver: str, optimizer: str) -> dict:
    epistemic_state = dict()

    epistemic_state['belief_base'] = belief_base
    epistemic_state['inference_system'] = inference_system
    epistemic_state['solver'] = solver
    epistemic_state['optimizer'] = optimizer
    epistemic_state['result_dict'] = dict()
    epistemic_state['preprocessing_done'] = False
    epistemic_state['preprocessing_timed_out'] = False
    epistemic_state['preprocessing_time'] = 0
    epistemic_state['kill_time'] = 0

    return epistemic_state

def create_inference_instance(epistemic_state):
    if epistemic_state['inference_system'] == 'p-entailment':
        epistemic_state['preprocessing_done'] = True
        inference_instance = PEntailment(epistemic_state)
    elif epistemic_state['inference_system'] == 'system-z':
        inference_instance = SystemZ(epistemic_state)
    elif epistemic_state['inference_system'] == 'system-w':
        # this optimizer selection method is a placeholed and will be replaced
        if epistemic_state['optimizer'] == 'z3':
            inference_instance = SystemWZ3(epistemic_state)
        else:
            inference_instance = SystemW(epistemic_state)
    elif epistemic_state['inference_system'] == 'c-inference':
        inference_instance = CInference(epistemic_state)
    else:
        Exception('no correct inference system provideid')
    return inference_instance #type: ignore



class InferenceOperator:
    epistemic_state: dict

    def __init__(self, belief_base: BeliefBase, inference_system: str='system-w',  solver: str='z3', optimizer: str = 'rc2') -> None:
        inference_system = inference_system.lower()
        solver = solver.lower()
        optimizer = optimizer.lower()
        available_solvers = get_env().factory.all_solvers().keys()
        assert solver in available_solvers, f'only {available_solvers} are available as solver'
        self.epistemic_state = create_epistemic_state(belief_base, inference_system, solver, optimizer)
            



    def inference(self, queries: Queries, total_timeout=0, inference_timeout=0, preprocessing_timeout=0, queries_name=None, multi_inference=False, decimals=1) -> pd.DataFrame:
        if queries_name:
            queries.name = queries_name
        
        columns = ['index', 'result', 'signature_size', 'number_conditionals' ,'preprocessing_time',\
                   'inference_time', 'preprocessing_timeout', 'inference_timeout', 'belief_base',\
                   'queries', 'query', 'inference_system', 'solver', 'optimizer']

        df = pd.DataFrame(columns=columns) # type: ignore
        
        inference_instance = create_inference_instance(self.epistemic_state)
        
        if total_timeout and preprocessing_timeout:
            preprocessing_timeout = min(total_timeout, preprocessing_timeout)
        elif total_timeout:
            preprocessing_timeout = total_timeout

        inference_instance.preprocess_belief_base(preprocessing_timeout)

        if total_timeout and inference_timeout:
            inference_timeout = min(total_timeout - self.epistemic_state['preprocessing_time'] / 1000, inference_timeout)
        elif total_timeout:
            inference_timeout = total_timeout - self.epistemic_state['preprocessing_time'] / 1000

        inference_instance.inference(queries.conditionals, inference_timeout, multi_inference)
        results = self.epistemic_state['result_dict']

        for index, query in enumerate(queries.conditionals.values()):
            query = str(query)
            df.at[index, 'index'] = results[query][0] 
            df.at[index, 'result'] = results[query][1]
            df.at[index, 'preprocessing_timed_out'] = self.epistemic_state['preprocessing_timed_out']
            df.at[index, 'preprocessing_time'] = round(self.epistemic_state['preprocessing_time'], decimals)
            df.at[index, 'inference_timed_out'] = results[query][2]
            df.at[index, 'inference_time'] = round(results[query][3], decimals)
            df.at[index, 'inference_system'] = self.epistemic_state['inference_system']
            df.at[index, 'solver'] = self.epistemic_state['solver']
            df.at[index, 'optimizer'] = self.epistemic_state['optimizer']
            df.at[index, 'belief_base'] = self.epistemic_state['belief_base'].name
            df.at[index, 'queries'] = queries.name
            df.at[index, 'query'] = query
            df.at[index, 'signature_size'] = len(self.epistemic_state['belief_base'].signature)
            df.at[index, 'number_conditionals'] = len(self.epistemic_state['belief_base'].conditionals)
        
        return df

