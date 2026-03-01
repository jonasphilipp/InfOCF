import pytest
import types

import inference.optimizer as opt_mod


class _DummyDeadline:
    def __init__(self, expired: bool):
        self._expired = expired

    def expired(self) -> bool:
        return self._expired


def test_optimizer_init_creates_missing_state_entries():
    class _O(opt_mod.Optimizer):
        def minimal_correction_subsets(self, wcnf, ignore=[], deadline=None):
            return []

    state = {}
    _ = _O(state)
    assert "pool" in state
    assert "v_cnf_dict" in state
    assert "f_cnf_dict" in state
    assert "nf_cnf_dict" in state


def test_remove_supersets_filters_superset_branch():
    # remove_supersets Zeilen ~171-172 (subset found)
    inp = [{1}, {1, 2}, {3}]
    out = opt_mod.remove_supersets(inp)
    assert [1, 2] not in out  # {1,2} ist superset von {1}


def test_create_optimizer_rc2_and_invalid_branch():
    # return branch + ValueError branch
    st = {"pmaxsat_solver": "rc2g3"}
    o = opt_mod.create_optimizer(st)
    assert o is not None

    with pytest.raises(ValueError):
        opt_mod.create_optimizer({"pmaxsat_solver": "unknown"})


def test_optimizer_rc2_deadline_timeout(monkeypatch):
    # deadline expired => TimeoutError
    class _FakeRC2:
        def __init__(self, *_a, **_k): pass
        def __enter__(self): return self
        def __exit__(self, *_a): return False
        def compute(self): return [1]  # würde sonst weiterlaufen
        @property
        def cost(self): return 0
        def add_clause(self, *_a, **_k): return None

    monkeypatch.setattr(opt_mod, "RC2", _FakeRC2)

    state = {"pmaxsat_solver": "rc2g3", "pool": object(), "nf_cnf_dict": {}}
    o = opt_mod.OptimizerRC2(state)
    with pytest.raises(TimeoutError):
        o.minimal_correction_subsets(wcnf=types.SimpleNamespace(), deadline=_DummyDeadline(True))  # type: ignore[arg-type]


def test_optimizer_rc2_debug_models_found(monkeypatch):
    # debug("models found")
    logs = {"debug": []}

    class _L:
        def isEnabledFor(self, *_a, **_k): return True
        def debug(self, msg, *args): logs["debug"].append((msg, args))

    monkeypatch.setattr(opt_mod, "logger", _L())

    class _FakeRC2:
        def __init__(self, *_a, **_k): pass
        def __enter__(self): return self
        def __exit__(self, *_a): return False
        def compute(self): return None  # sofort None => debug("models found") und break
        @property
        def cost(self): return 0
        def add_clause(self, *_a, **_k): return None

    monkeypatch.setattr(opt_mod, "RC2", _FakeRC2)

    state = {"pmaxsat_solver": "rc2g3", "pool": object(), "nf_cnf_dict": {}}
    o = opt_mod.OptimizerRC2(state)
    out = o.minimal_correction_subsets(wcnf=types.SimpleNamespace())  # type: ignore[arg-type]
    assert isinstance(out, list)
    assert any("models found" in m for m, _ in logs["debug"])

def test_optimizer_base_minimal_correction_subsets_hits_default_return():
    import inference.optimizer as opt
    from pysat.formula import WCNF

    class _Concrete(opt.Optimizer):
        # make it concrete but still execute the base-class line 75
        def minimal_correction_subsets(self, wcnf, ignore=[], deadline=None):
            return super().minimal_correction_subsets(
                wcnf, ignore=ignore, deadline=deadline
            )

    o = _Concrete({})
    out = o.minimal_correction_subsets(WCNF())
    assert out == []
