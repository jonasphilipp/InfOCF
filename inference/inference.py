import multiprocessing as mp
from abc import ABC, abstractmethod
from time import process_time_ns, process_time

class Inference(ABC):
    def __init__(self, epistemic_state) -> None:
        self.epistemic_state = epistemic_state

    def preprocess_belief_base(self, preprocessing_timeout): 
        #self._epistemic_state._preprocessing_timeout = preprocessing_timeout
        self.epistemic_state._kill_time = preprocessing_timeout + process_time()
        try:
            preprocessing_start_time = process_time_ns() / 1e+6
            self._preprocess_belief_base()
            self.epistemic_state.preprocessing_time += (process_time_ns() / 1e+6 - preprocessing_start_time)
            self.epistemic_state.preprocessing_done = True
        except TimeoutError:
            self.epistemic_state.preprocessing_time = preprocessing_timeout * 1000
            self.epistemic_state.preprocessing_timed_out = True
        except Exception as e:
            raise e


    def inference(self, queries, timeout, multi_inference):
        if not self.epistemic_state.preprocessing_done and not self.epistemic_state.preprocessing_timed_out:
            Exception("preprocess belief_base before running inference")
        if self.epistemic_state.preprocessing_timed_out:
            self.epistemic_state.result_dict.update({str(q): (i, False, False, 0)  for i, q in queries.items()})
        elif multi_inference:
            self.epistemic_state.result_dict.update(self.multi_inference(queries, timeout))
        else:
            self.epistemic_state.result_dict.update(self.single_inference(queries, timeout))
    
    def single_inference(self,  queries, timeout):
        result_dict = dict()
        for index, query in queries.items():
            self.epistemic_state._kill_time = timeout + process_time()
            try:
                start_time = process_time_ns() / 1e+6
                result = self._inference(query)
                time = (process_time_ns() / 1e+6 - start_time)
                result_dict[str(query)] = (index, result, False, time)
            except TimeoutError:
                result_dict[str(query)] = (index, False, True, timeout * 1000)
            except Exception as e:
                raise e
        return result_dict

    def multi_inference(self, queries, timeout):
        
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
                p.join(timeout+1)
                if p.is_alive():
                    p.terminate()
                    p.join()  # Ensure the process has terminated
                    mp_return_dict[processes.index((p, i, query))] = (query, (i, False, True, 0))

            #results = [mp_return_dict[i] if i in return_dict else (str(q), (i, False, True, 0))  for i, q in queries.items()]
            result_dict = {str(q): mp_return_dict[i] if i in mp_return_dict else (i, False, True, timeout)  for i, q in queries.items()}
            return result_dict


    def _multi_inference_worker(self, index, query, mp_return_dict, timeout):
        self.epistemic_state._kill_time = timeout + process_time()
        try:
            start_time = process_time_ns() / 1e+6
            result = self._inference(query)
            time = (process_time_ns() / 1e+6 - start_time)
            mp_return_dict[index] = (index, result, False, time)
        except TimeoutError:
            mp_return_dict[index] = (index, False, True, timeout * 1000)
        except Exception as e:
            raise e

    @abstractmethod
    def _inference(self, query) -> bool:
        pass

    @abstractmethod
    def _preprocess_belief_base(self):
        pass



