from __future__ import annotations

import types

import inference.inference as inf_mod


class _DummyBeliefBase:
    def __init__(self, name: str = "bb", conditionals: list | None = None) -> None:
        self.name = name
        self.conditionals = list(conditionals or [])


class _DummyConditional:
    def __init__(self, antecedence="A", consequence="B", label: str = "q") -> None:
        self.antecedence = antecedence
        self.consequence = consequence
        self._label = label

    def __str__(self) -> str:
        return self._label


class _DummyLogger:
    def __init__(self) -> None:
        self.infos: list[tuple[str, dict | None]] = []
        self.debugs: list[str] = []

    def info(self, msg: str, extra=None) -> None:
        self.infos.append((msg, extra))

    def debug(self, msg: str) -> None:
        self.debugs.append(msg)


class _DummyInference(inf_mod.Inference):
    def __init__(self, epistemic_state: dict) -> None:
        super().__init__(epistemic_state)
        self.preprocess_calls: list[tuple[bool, object]] = []
        self.inference_calls: list[tuple[object, bool, object]] = []
        self.preprocess_raises: Exception | None = None
        self.inference_raises: Exception | None = None
        self.inference_return: bool = False

    def _preprocess_belief_base(self, weakly: bool, deadline) -> None:
        self.preprocess_calls.append((weakly, deadline))
        if self.preprocess_raises is not None:
            raise self.preprocess_raises

    def _inference(self, query, weakly: bool, deadline) -> bool:
        self.inference_calls.append((query, weakly, deadline))
        if self.inference_raises is not None:
            raise self.inference_raises
        return self.inference_return


def _make_state(
    *,
    preprocessing_done: bool = False,
    preprocessing_timed_out: bool = False,
    preprocessing_time: float = 0.0,
    weakly: bool = False,
    belief_base: _DummyBeliefBase | None = None,
) -> dict:
    return {
        "belief_base": belief_base or _DummyBeliefBase(conditionals=[object()]),
        "smt_solver": "dummy",
        "inference_system": "dummy_system",
        "weakly": weakly,
        "preprocessing_done": preprocessing_done,
        "preprocessing_timed_out": preprocessing_timed_out,
        "preprocessing_time": preprocessing_time,
    }


def test_preprocess_belief_base_skips_if_already_done(monkeypatch):
    dummy_logger = _DummyLogger()
    monkeypatch.setattr(inf_mod, "logger", dummy_logger)

    state = _make_state(preprocessing_done=True, preprocessing_time=123.0)
    inf = _DummyInference(state)

    inf.preprocess_belief_base(preprocessing_timeout=5)

    assert inf.preprocess_calls == []
    assert any("skipping" in msg.lower() for msg, _ in dummy_logger.infos)


def test_preprocess_belief_base_asserts_on_empty_belief_base(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())
    state = _make_state(belief_base=_DummyBeliefBase(conditionals=[]))
    inf = _DummyInference(state)

    try:
        inf.preprocess_belief_base(preprocessing_timeout=5)
        assert False, "expected AssertionError"
    except AssertionError as e:
        assert "belief base empty" in str(e)


def test_preprocess_belief_base_asserts_on_inconsistent_belief_base(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())

    def _fake_consistency(*args, **kwargs):
        return False, None

    monkeypatch.setattr(inf_mod, "consistency", _fake_consistency)

    state = _make_state()
    inf = _DummyInference(state)

    try:
        inf.preprocess_belief_base(preprocessing_timeout=5)
        assert False, "expected AssertionError"
    except AssertionError as e:
        assert "belief base inconsistent" in str(e)


def test_preprocess_belief_base_success_sets_flags_and_time(monkeypatch):
    dummy_logger = _DummyLogger()
    monkeypatch.setattr(inf_mod, "logger", dummy_logger)

    # consistency passes
    monkeypatch.setattr(inf_mod, "consistency", lambda *a, **k: (True, None))

    # deterministic timing (ms)
    # start: 1000ms, end: 1250ms -> delta 250ms
    times = iter([1_000_000_000, 1_250_000_000])  # ns
    monkeypatch.setattr(inf_mod, "perf_counter_ns", lambda: next(times))

    # Deadline.from_duration should be called when timeout != 0
    class _D:
        @staticmethod
        def from_duration(_t):
            return "deadline"

    monkeypatch.setattr(inf_mod, "Deadline", _D)

    state = _make_state(preprocessing_time=10.0, weakly=True)
    inf = _DummyInference(state)

    inf.preprocess_belief_base(preprocessing_timeout=7)

    assert state["preprocessing_done"] is True
    assert state["preprocessing_timed_out"] is False
    assert state["preprocessing_time"] == 10.0 + 250.0
    assert inf.preprocess_calls == [(True, "deadline")]
    assert any("completed successfully" in msg.lower() for msg, _ in dummy_logger.infos)


def test_preprocess_belief_base_timeout_sets_timed_out_and_time(monkeypatch):
    dummy_logger = _DummyLogger()
    monkeypatch.setattr(inf_mod, "logger", dummy_logger)
    monkeypatch.setattr(inf_mod, "consistency", lambda *a, **k: (True, None))

    state = _make_state()
    inf = _DummyInference(state)
    inf.preprocess_raises = TimeoutError()

    inf.preprocess_belief_base(preprocessing_timeout=3)

    assert state["preprocessing_timed_out"] is True
    assert state["preprocessing_time"] == 3000
    assert any("timed out" in msg.lower() for msg, _ in dummy_logger.infos)


def test_inference_requires_preprocessing_done_or_timed_out(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())
    state = _make_state(preprocessing_done=False, preprocessing_timed_out=False)
    inf = _DummyInference(state)

    try:
        inf.inference({0: _DummyConditional(label="q0")}, timeout=1, multi_inference=False)
        assert False, "expected Exception"
    except Exception as e:
        assert "preprocess belief_base" in str(e)


def test_inference_returns_all_false_if_preprocessing_timed_out(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())
    state = _make_state(preprocessing_done=False, preprocessing_timed_out=True)
    inf = _DummyInference(state)

    q0 = _DummyConditional(label="q0")
    q1 = _DummyConditional(label="q1")
    res = inf.inference({5: q0, 6: q1}, timeout=1, multi_inference=False)

    assert res == {"q0": (5, False, False, 0.0), "q1": (6, False, False, 0.0)}


def test_inference_dispatches_to_single_or_multi(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())
    state = _make_state(preprocessing_done=True)
    inf = _DummyInference(state)

    q0 = _DummyConditional(label="q0")

    inf.single_inference = lambda queries, timeout: {"q0": (0, True, False, 1.0)}
    inf.multi_inference = lambda queries, timeout: {"q0": (0, False, False, 2.0)}

    res_single = inf.inference({0: q0}, timeout=1, multi_inference=False)
    assert res_single["q0"][1] is True
    assert res_single["q0"][3] == 1.0

    res_multi = inf.inference({0: q0}, timeout=1, multi_inference=True)
    assert res_multi["q0"][1] is False
    assert res_multi["q0"][3] == 2.0


def test_single_inference_success_and_timeout(monkeypatch):
    state = _make_state(preprocessing_done=True)
    inf = _DummyInference(state)

    # perf_counter_ns is called:
    # - q0 success: 2x (start, end)
    # - q1 timeout: 1x (start only, then TimeoutError)
    times = iter([1_000_000_000, 1_200_000_000, 2_000_000_000])  # ns
    monkeypatch.setattr(inf_mod, "perf_counter_ns", lambda: next(times))

    class _D:
        @staticmethod
        def from_duration(_t):
            return "deadline"

    monkeypatch.setattr(inf_mod, "Deadline", _D)

    q0 = _DummyConditional(label="q0")
    q1 = _DummyConditional(label="q1")

    def _general_inference(query, deadline=None):
        if str(query) == "q1":
            raise TimeoutError()
        return True

    inf.general_inference = _general_inference

    res = inf.single_inference({0: q0, 1: q1}, timeout=7)

    assert res["q0"][0] == 0
    assert res["q0"][1] is True
    assert res["q0"][2] is False
    assert res["q0"][3] == 200.0

    assert res["q1"] == (1, False, True, 7000.0)


def test_multi_inference_worker_success_and_timeout(monkeypatch):
    state = _make_state(preprocessing_done=True)
    inf = _DummyInference(state)

    # perf_counter_ns is called:
    # - success: 2x
    # - timeout: 1x
    times = iter([1_000_000_000, 1_150_000_000, 2_000_000_000])  # ns
    monkeypatch.setattr(inf_mod, "perf_counter_ns", lambda: next(times))

    class _D:
        @staticmethod
        def from_duration(_t):
            return "deadline"

    monkeypatch.setattr(inf_mod, "Deadline", _D)

    q0 = _DummyConditional(label="q0")

    # success
    out: dict[int, tuple[int, bool, bool, float]] = {}
    inf.general_inference = lambda *_a, **_k: True
    inf._multi_inference_worker(0, q0, out, timeout=5)
    assert out[0] == (0, True, False, 150.0)

    # timeout
    out2: dict[int, tuple[int, bool, bool, float]] = {}
    inf.general_inference = lambda *_a, **_k: (_ for _ in ()).throw(TimeoutError())
    inf._multi_inference_worker(0, q0, out2, timeout=9)
    assert out2[0] == (0, False, True, 9000.0)


def test_multi_inference_uses_processes_and_marks_timeouts(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())
    state = _make_state(preprocessing_done=True)
    inf = _DummyInference(state)

    # We simulate mp.Manager() and mp.Process so no real processes are spawned.
    class _FakeProcess:
        def __init__(self, *, target, args, run_target: bool) -> None:
            self._target = target
            self._args = args
            self._alive = True
            self._run_target = run_target

        def start(self) -> None:
            if self._run_target:
                self._target(*self._args)
                self._alive = False

        def join(self, *_a, **_k) -> None:
            return

        def is_alive(self) -> bool:
            return self._alive

        def terminate(self) -> None:
            self._alive = False

    class _FakeManager:
        def __enter__(self):
            return self

        def __exit__(self, exc_type, exc, tb):
            return False

        def dict(self):
            return {}

    # return first process runs, second stays alive -> triggers terminate branch
    call_no = {"n": 0}

    def _fake_process_ctor(*, target, args):
        call_no["n"] += 1
        return _FakeProcess(target=target, args=args, run_target=(call_no["n"] == 1))

    fake_mp = types.SimpleNamespace(Manager=lambda: _FakeManager(), Process=_fake_process_ctor)
    monkeypatch.setattr(inf_mod, "mp", fake_mp)

    # keep inference deterministic
    inf.general_inference = lambda *_a, **_k: True
    monkeypatch.setattr(inf_mod, "perf_counter_ns", lambda: 1_000_000_000)

    q0 = _DummyConditional(label="q0")
    q1 = _DummyConditional(label="q1")

    # IMPORTANT: use non-sequential indices so the terminate-branch writes a key
    # that does NOT match the query index -> forces the comprehension fallback path.
    res = inf.multi_inference({5: q0, 6: q1}, timeout=2)

    assert res["q0"][0] == 5
    assert res["q0"][2] is False  # not timed out

    assert res["q1"][0] == 6
    assert res["q1"][2] is True   # timed out (fallback path)
    assert res["q1"][3] == 2000.0


def test_general_inference_self_fulfilling_shortcut(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())

    # Make first is_unsat(query.antecedence) True -> shortcut True
    monkeypatch.setattr(inf_mod, "is_unsat", lambda x: x == "UNSAT_ANTE")
    monkeypatch.setattr(inf_mod, "And", lambda a, b: ("AND", a, b))
    monkeypatch.setattr(inf_mod, "Not", lambda a: ("NOT", a))

    state = _make_state(preprocessing_done=True, weakly=False)
    inf = _DummyInference(state)

    q = _DummyConditional(antecedence="UNSAT_ANTE", consequence="C", label="q")
    assert inf.general_inference(q) is True
    assert inf.inference_calls == []  # _inference must not run


def test_general_inference_calls_concrete_inference(monkeypatch):
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())

    monkeypatch.setattr(inf_mod, "is_unsat", lambda _x: False)
    monkeypatch.setattr(inf_mod, "And", lambda a, b: ("AND", a, b))
    monkeypatch.setattr(inf_mod, "Not", lambda a: ("NOT", a))

    state = _make_state(preprocessing_done=True, weakly=True)
    inf = _DummyInference(state)
    inf.inference_return = True

    q = _DummyConditional(antecedence="A", consequence="B", label="q")
    assert inf.general_inference(q, weakly=None, deadline="dl") is True

    assert len(inf.inference_calls) == 1
    called_query, called_weakly, called_deadline = inf.inference_calls[0]
    assert called_query is q
    assert called_weakly is True
    assert called_deadline == "dl"

import pytest


def test_preprocess_belief_base_reraises_generic_exception(monkeypatch):
    """
    Covers inference.py lines 165-166: except Exception as e: raise e
    """
    monkeypatch.setattr(inf_mod, "logger", _DummyLogger())
    monkeypatch.setattr(inf_mod, "consistency", lambda *a, **k: (True, None))

    # Deadline is used only when timeout != 0
    class _D:
        @staticmethod
        def from_duration(_t):
            return "deadline"

    monkeypatch.setattr(inf_mod, "Deadline", _D)

    state = _make_state(preprocessing_done=False, preprocessing_timed_out=False)
    inf = _DummyInference(state)
    inf.preprocess_raises = RuntimeError("boom")

    with pytest.raises(RuntimeError, match="boom"):
        inf.preprocess_belief_base(preprocessing_timeout=1)


def test_single_inference_reraises_generic_exception(monkeypatch):
    """
    Covers inference.py lines 301-302: except Exception as e: raise e
    """
    state = _make_state(preprocessing_done=True)
    inf = _DummyInference(state)

    # perf_counter_ns is called once before general_inference, which then raises
    monkeypatch.setattr(inf_mod, "perf_counter_ns", lambda: 1_000_000_000)

    class _D:
        @staticmethod
        def from_duration(_t):
            return "deadline"

    monkeypatch.setattr(inf_mod, "Deadline", _D)

    def _raise(_query, deadline=None):
        raise ValueError("nope")

    inf.general_inference = _raise

    q0 = _DummyConditional(label="q0")
    with pytest.raises(ValueError, match="nope"):
        inf.single_inference({0: q0}, timeout=3)


def test_multi_inference_worker_reraises_generic_exception(monkeypatch):
    """
    Covers inference.py lines 420-421: except Exception as e: raise e
    """
    state = _make_state(preprocessing_done=True)
    inf = _DummyInference(state)

    monkeypatch.setattr(inf_mod, "perf_counter_ns", lambda: 1_000_000_000)

    class _D:
        @staticmethod
        def from_duration(_t):
            return "deadline"

    monkeypatch.setattr(inf_mod, "Deadline", _D)

    inf.general_inference = lambda *_a, **_k: (_ for _ in ()).throw(ValueError("worker-fail"))

    q0 = _DummyConditional(label="q0")
    out: dict[int, tuple[int, bool, bool, float]] = {}

    with pytest.raises(ValueError, match="worker-fail"):
        inf._multi_inference_worker(0, q0, out, timeout=2)
