import multiprocessing as mp
from abc import ABC, abstractmethod
from time import process_time_ns, process_time
from inference.conditional import Conditional
from inference.consistency_sat import consistency
from pysmt.shortcuts import is_unsat, And, Not

class Inference(ABC):
    """
    Context:
        Abstract class intitialization inherited by implementing classes

    Parameters:
        Initialized epistemic_state
    """
    def __init__(self, epistemic_state: dict) -> None:
        self.epistemic_state = epistemic_state
    


    """
    Preprocessing wrapper method. Handles timeout and measures time.

    Context:
        Wraps abstract _preprocess_belief_base method.

    Parameters: 
        Timeout in seconds.

    Side Effects:
        kill_time, preprocessing_time and preprocessing_timed_out in epistemic_state
    """
    def preprocess_belief_base(self, preprocessing_timeout: int) -> None: 
        #self._epistemic_state._preprocessing_timeout = preprocessing_timeout
        cons, _ = consistency(self.epistemic_state['belief_base'], self.epistemic_state['smt_solver'])
        assert cons != False, "belief base inconsistent"
        if preprocessing_timeout:    
            self.epistemic_state['kill_time'] = preprocessing_timeout + process_time()
        else:
            self.epistemic_state['kill_time'] = 0
        try:
            preprocessing_start_time = process_time_ns() / 1e+6
            self._preprocess_belief_base()
            self.epistemic_state['preprocessing_time'] += (process_time_ns() / 1e+6 - preprocessing_start_time)
            self.epistemic_state['preprocessing_done'] = True
        except TimeoutError:
            self.epistemic_state['preprocessing_time'] = preprocessing_timeout * 1000
            self.epistemic_state['preprocessing_timed_out'] = True
        except Exception as e:
            raise e


    """
    General inference wrapper method. Selects kind (single/multi) of inference to perform.

    Context:
        Wraps single/multi inference methods.

    Parameters: 
        Conditional dictionay, timeout in s and boolen indication if parallel inferences are to be performed.

    Side Effects:
        result_dict in epistemic_state
    """
    def inference(self, queries: dict, timeout: int, multi_inference: bool) -> None:
        if not self.epistemic_state['preprocessing_done'] and not self.epistemic_state['preprocessing_timed_out']:
            Exception("preprocess belief_base before running inference")
        if self.epistemic_state['preprocessing_timed_out']:
            self.epistemic_state['result_dict'].update({str(q): (i, False, False, 0)  for i, q in queries.items()})
        elif multi_inference:
            self.epistemic_state['result_dict'].update(self.multi_inference(queries, timeout))
        else:
            self.epistemic_state['result_dict'].update(self.single_inference(queries, timeout))
    
    
    """
    Singular inference wrapper method. Handles timeout and measures time.


    Context:
        Wraps abstract _inference() method in a way that multiple inferences are performed sequentially only.
        Called by inferene().

    Parameters: 
        Conditional dictionay, timeout in seconds.

    Returns:
        result dictionay
    """ 
    def single_inference(self, queries: dict, timeout: int) -> dict:
        result_dict = dict()
        for index, query in queries.items():
            if timeout:
                self.epistemic_state['kill_time'] = timeout + process_time()
            else:
                self.epistemic_state['kill_time'] = 0
            try:
                start_time = process_time_ns() / 1e+6
                result = self.general_inference(query)
                time = (process_time_ns() / 1e+6 - start_time)
                result_dict[str(query)] = (index, result, False, time)
            except TimeoutError:
                result_dict[str(query)] = (index, False, True, timeout * 1000)
            except Exception as e:
                raise e
        return result_dict


    """
    Parallel inference wrapper method.

    Context:
        Wraps _multi_inference_worker() method in a way that multiple inferences are performed in parallel
        if possible and sequentially only in parallel capacity exhausted. Called by inference().

    Parameters: 
        Conditional dictionay, timeout in seconds.

    Returns:
        result dictionay
    """ 
    def multi_inference(self, queries: dict, timeout: int) -> dict:
        
        indices = queries.keys()

        with mp.Manager() as manager:
            mp_return_dict = manager.dict()
            processes = []

            for i in indices:
                query = queries[i]
                p = mp.Process(target=self._multi_inference_worker, args=(i, query, mp_return_dict, timeout))
                processes.append((p, i, query))
                p.start()

            for p, i, query in processes:
                p.join(timeout+10)
                if p.is_alive():
                    p.terminate()
                    p.join()  # Ensure the process has terminated
                    mp_return_dict[processes.index((p, i, query))] = (query, (i, False, True, 0))

            #results = [mp_return_dict[i] if i in return_dict else (str(q), (i, False, True, 0))  for i, q in queries.items()]
            result_dict = {str(q): mp_return_dict[i] if i in mp_return_dict else (i, False, True, timeout)  for i, q in queries.items()}
            return result_dict

    """
    Inference wrapper method. Handles timeout and measures time.


    Context:
        Wraps abstract _inference() method. Called by multi_inference().

    Parameters: 
        Conditional dictionay, timeout in seconds.

    Side Effects:
        result dictionay
    """ 
    def _multi_inference_worker(self, index: int, query: Conditional, mp_return_dict: dict, timeout: int) -> None:
        if timeout:
            self.epistemic_state['kill_time'] = timeout + process_time()
        else:
            self.epistemic_state['kill_time'] = 0
        try:
            start_time = process_time_ns() / 1e+6
            result = self.general_inference(query)
            time = (process_time_ns() / 1e+6 - start_time)
            mp_return_dict[index] = (index, result, False, time)
        except TimeoutError:
            mp_return_dict[index] = (index, False, True, timeout * 1000)
        except Exception as e:
            raise e

    def general_inference(self, query: Conditional):
        if is_unsat(query.antecedence) or is_unsat(And(query.antecedence, Not(query.consequence))):
            print('general_inference query selffullfilling')
            return True
        elif is_unsat(And(query.antecedence, query.consequence)): 
            print("general_inference query inconsistent")
            return False
        else:
            return self._inference(query)


    @abstractmethod
    def _inference(self, query: Conditional) -> bool:
        pass

    @abstractmethod
    def _preprocess_belief_base(self) -> None:
        pass



