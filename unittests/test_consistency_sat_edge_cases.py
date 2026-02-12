from pysmt.shortcuts import FALSE, Not, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
import inference.consistency_sat as cs


def test_checkTautologies_detects_impossible_antecedent():
    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    cond = Conditional(consequence=b, antecedence=FALSE(), textRepresentation="(b|Bottom)")
    assert cs.checkTautologies({0: cond}) is True


def test_consistency_debug_and_empty_kb_branch(monkeypatch):
    # Hit debug-lines + "no conditionals remain" return branch
    monkeypatch.setattr(cs.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(cs.logger, "debug", lambda *a, **k: None)

    bb = BeliefBase(signature=["a"], conditionals={}, name="empty")
    part, stats = cs.consistency(bb, solver="z3", weakly=True)
    assert part == [[]]  # weakly=True appends empty last layer


def test_consistency_no_tolerated_rules_debug_branch(monkeypatch):
    # Construct a KB where R == [] but knowledge is SAT -> weakly path returns partition.append(C)
    monkeypatch.setattr(cs.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(cs.logger, "debug", lambda *a, **k: None)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c1 = Conditional(b, a, "(b|a)")
    c2 = Conditional(Not(b), a, "(!b|a)")
    bb = BeliefBase(["a", "b"], {0: c1, 1: c2}, "contrad")

    part, stats = cs.consistency(bb, solver="z3", weakly=True)
    assert part is not False
    assert len(part) >= 1


def test_consistency_indices_debug_and_no_tolerated_rules_strict(monkeypatch):
    monkeypatch.setattr(cs.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(cs.logger, "debug", lambda *a, **k: None)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c1 = Conditional(b, a, "(b|a)")
    c2 = Conditional(Not(b), a, "(!b|a)")
    bb = BeliefBase(["a", "b"], {0: c1, 1: c2}, "contrad")

    out, stats = cs.consistency_indices(bb, solver="z3", weakly=False)
    assert out is False


def test_set_core_minimize_sets_flag():
    class DummySolver:
        def __init__(self):
            self.calls = []
        def set(self, k, v):
            self.calls.append((k, v))

    s = DummySolver()
    cs.set_core_minimize(s)
    assert ("sat.core.minimize", True) in s.calls

def test_consistency_indices_hits_consistent_debug_line_120(monkeypatch):
    import logging
    import inference.consistency_sat as cs

    # Fake logger to force debug branch and record calls
    class _FakeLogger:
        def __init__(self):
            self.debug_calls = []

        def isEnabledFor(self, level):
            return level == logging.DEBUG

        def debug(self, msg, *args):
            self.debug_calls.append((msg, args))

    # Fake belief base with empty conditionals -> immediate "consistent" branch
    class _FakeBeliefBase:
        def __init__(self):
            self.conditionals = {}

    # Dummy Solver context manager
    class _DummySolver:
        def __enter__(self): return self
        def __exit__(self, exc_type, exc, tb): return False

    monkeypatch.setattr(cs, "logger", _FakeLogger())
    monkeypatch.setattr(cs, "Solver", lambda *a, **k: _DummySolver())

    ckb = _FakeBeliefBase()
    partition, diag = cs.consistency_indices(ckb, solver="z3", weakly=False)

    assert len(cs.logger.debug_calls) >= 1
