import pytest
from pysat.formula import WCNF

import inference.system_w as sw


class _DummyTseitin:
    def __init__(self, epistemic_state):
        self.epistemic_state = epistemic_state

    def query_to_cnf(self, _query):
        # return (verification_clauses, falsification_clauses)
        return ([[1]], [[-1]])


class _DummyOptimizer:
    def __init__(self, seq):
        self._it = iter(seq)

    def minimal_correction_subsets(self, *_a, **_k):
        return next(self._it)


def test_system_w_inference_not_weakly_calls_rec_inference(monkeypatch):
    import inference.system_w as sw

    # minimal epistemic state
    state = {
        "belief_base": object(),
        "smt_solver": "z3",
        "weakly": False,
        "partition": [[1], [2]],          # len(partition)-1 == 1
        "v_cnf_dict": {},
        "f_cnf_dict": {},
        "nf_cnf_dict": {1: [[10]], 2: [[20]]},
    }
    sysw = sw.SystemW(state)

    class _DummyTseitin:
        def __init__(self, epistemic_state):
            self.epistemic_state = epistemic_state

        def query_to_cnf(self, _query):
            return ([[1]], [[-1]])

    monkeypatch.setattr(sw, "TseitinTransformation", _DummyTseitin)

    called = {"n": 0}

    def _rec_stub(self, _wcnf, _partition_index, _deadline):
        called["n"] += 1
        return True

    monkeypatch.setattr(sw.SystemW, "_rec_inference", _rec_stub)

    assert sysw._inference(query=object(), weakly=False, deadline=None) is True
    assert called["n"] == 1

def test_system_w_rec_inference_appends_f_cnf_dict_for_xi_i(monkeypatch):
    # Build an instance with a 2-layer partition so partition_index can be 1 (and recursion goes to 0)
    state = {
        "belief_base": object(),
        "smt_solver": "z3",
        "weakly": False,
        "partition": [[99], [1, 2]],   # we call _rec_inference at partition_index=1, then it recurses to 0
        "v_cnf_dict": {0: []},         # used by _rec_inference
        "f_cnf_dict": {
            0: [],                     # used by _rec_inference
            1: [[-11]],                # <-- MUST exist for line 136
            2: [[-22]],
        },
        "nf_cnf_dict": {
            1: [[111]],
            2: [[222]],
            99: [[999]],
        },
    }
    sysw = sw.SystemW(state)

    # Optimizer returns MCS lists such that:
    # xi_i_set = {{1}}, xi_i_prime_set = {{1}} => intersection contains {1}
    optimizer = _DummyOptimizer(seq=[[[1]], [[1]]])
    monkeypatch.setattr(sw, "create_optimizer", lambda _st: optimizer)

    # Patch recursion so top-level runs original logic, but recursive call returns True immediately
    call_count = {"n": 0}
    original = sw.SystemW._rec_inference

    def _rec_wrapper(self, hard_constraints, partition_index, deadline=None):
        call_count["n"] += 1
        if call_count["n"] == 1:
            # run real logic at partition_index=1 => will execute line 136
            return original(self, hard_constraints, partition_index, deadline)
        # recursive call (partition_index=0) short-circuited
        return True

    monkeypatch.setattr(sw.SystemW, "_rec_inference", _rec_wrapper)

    # Run. If line 136 is reached, it will access f_cnf_dict[1] successfully and append its clauses.
    assert sysw._rec_inference(WCNF(), partition_index=1, deadline=None) is True
