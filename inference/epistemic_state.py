from pysat.formula import IDPool
from abc import ABC
from inference.belief_base import BeliefBase


class EpistemicState(ABC):
    preprocessing_done: bool
    preprocessing_timed_out: bool
    preprocessing_time: float
    solver: str
    optimizer: str
    result_dict: dict
    _belief_base: BeliefBase
    _inference_system: str
    _kill_time: float

    def __init__(self, belief_base: BeliefBase, solver: str, optimizer: str) -> None:
        self._belief_base = belief_base
        self._kill_time = 0
        self.solver = solver
        self.optimizer = optimizer
        self.preprocessing_done = False
        self.preprocessing_timed_out = False
        self.preprocessing_time = 0
        self.result_dict = dict()
        
    @property
    def belief_base_name(self):
        return self._belief_base.name

    @property
    def signature_size(self):
        return len(self._belief_base.signature)

    @property
    def number_conditionals(self):
        return len(self._belief_base.conditionals)

    @property
    def inference_system(self):
        return self._inference_system


class EpistemicStateP(EpistemicState):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._inference_system = 'p-entailment'
        self._preprocessing_done = True


class EpistemicStateZ(EpistemicState):
    _partition: list
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._inference_system = 'system-z'


class EpistemicStateWCNF(EpistemicState):
    _pool: IDPool
    _notAorBs: dict

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)    
        self._pool = IDPool()
        self._ABs = dict()
        self._AnotBs = dict()
        self._notAorBs = dict()


class EpistemicStateW(EpistemicStateZ, EpistemicStateWCNF):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._inference_system = 'system-w'


class EpistemicStateC(EpistemicStateWCNF):
    _eta: dict
    _vMin: dict
    _fMin: dict
    _base_csp: dict
    _conditionals: dict

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)    
        self._eta = dict()
        self._vMin = dict()
        self._fMin = dict()
        self._base_csp = dict()
        self._conditionals = dict()
        self._inference_system = 'c-inference'


