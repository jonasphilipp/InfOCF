"""
C-revision incremental tests.

Purpose
-------
Validate incremental update behavior for the C-revision operator, checking that
successive modifications yield consistent results and preserve expected
properties.

Run
---
uv run pytest -q unittests/test_c_revision_incremental.py
"""

import unittest

from pysmt.shortcuts import Not, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.c_revision import c_revision
from inference.c_revision_model import CRevisionModel
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF


class TestCRevisionIncremental(unittest.TestCase):
    def setUp(self):
        self.sig = ["a", "b", "c"]
        # All-zero ranks
        self.all_zero_ranks = {
            format(i, f"0{len(self.sig)}b"): 0 for i in range(2 ** len(self.sig))
        }

        a = Symbol("a", BOOL)
        b = Symbol("b", BOOL)
        c = Symbol("c", BOOL)

        # Base conditionals
        cond1 = Conditional(b, a, "(b|a)")
        cond1.index = 1
        cond2 = Conditional(Not(b), a, "(!b|a)")
        cond2.index = 2

        self.base_conditionals = [cond1, cond2]

        # PreOCF
        self.preocf = CustomPreOCF(self.all_zero_ranks, signature=self.sig)
        self.bb = BeliefBase(
            self.sig, {c.index: c for c in self.base_conditionals}, "inc"
        )

    def test_model_vs_legacy_equivalence(self):
        # Build model from base
        model = CRevisionModel.from_preocf_and_conditionals(
            self.preocf, self.base_conditionals
        )

        # Legacy path
        legacy = c_revision(self.preocf, self.base_conditionals, gamma_plus_zero=True)
        if legacy is None:
            self.skipTest(
                "No feasible gamma vector for legacy path; skipping equivalence test"
            )

        # Model path (should be identical)
        via_model = c_revision(
            self.preocf,
            self.base_conditionals,
            gamma_plus_zero=True,
            model=model,
        )
        if via_model is None:
            self.skipTest(
                "No feasible gamma vector for model path; skipping equivalence test"
            )

        # Compare gamma- vector across both results
        for i in range(1, len(self.base_conditionals) + 1):
            self.assertEqual(legacy.get(f"gamma-_{i}"), via_model.get(f"gamma-_{i}"))

    def test_incremental_add_conditional_matches_full_recompute(self):
        a = Symbol("a", BOOL)
        c = Symbol("c", BOOL)
        # New conditional with unique index
        cond3 = Conditional(c, a, "(c|a)")
        cond3.index = 3

        # Build model and add incrementally
        model = CRevisionModel.from_preocf_and_conditionals(
            self.preocf, self.base_conditionals
        )
        model.add_conditional(cond3)

        # Legacy full recompute with extended list
        extended = self.base_conditionals + [cond3]
        legacy = c_revision(self.preocf, extended, gamma_plus_zero=True)
        if legacy is None:
            self.skipTest(
                "No feasible gamma vector for extended legacy path; skipping incremental test"
            )
        via_model = c_revision(self.preocf, extended, gamma_plus_zero=True, model=model)
        if via_model is None:
            self.skipTest(
                "No feasible gamma vector for extended model path; skipping incremental test"
            )

        for i in range(1, len(extended) + 1):
            self.assertEqual(legacy.get(f"gamma-_{i}"), via_model.get(f"gamma-_{i}"))

# ---------------------------------------------------------------------------
# Additional edge-case tests for CRevisionModel coverage gaps
# ---------------------------------------------------------------------------

import pytest
from pysmt.shortcuts import Symbol
from pysmt.typing import BOOL

from inference.c_revision_model import CRevisionModel, _extract_cond_masks
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF


def test_extract_cond_masks_unknown_signature_var_returns_none():
    sig_index = {"a": 0}
    a = Symbol("a", BOOL)
    x = Symbol("x", BOOL)  # not in sig_index
    cond = Conditional(consequence=a, antecedence=x, textRepresentation="(a|x)")
    assert _extract_cond_masks(cond, sig_index) is None


def test_add_conditional_requires_index_attr():
    # minimal PreOCF
    sig = ["a"]
    ranks = {"0": 0, "1": 0}
    pre = CustomPreOCF(ranks, signature=sig)
    model = CRevisionModel.from_preocf_and_conditionals(pre, [])

    class NoIndex:
        pass

    with pytest.raises(ValueError, match="unique 'index'"):
        model.add_conditional(NoIndex())  # type: ignore[arg-type]


def test_add_conditional_duplicate_index_raises():
    sig = ["a", "b"]
    ranks = {format(i, "02b"): 0 for i in range(4)}
    pre = CustomPreOCF(ranks, signature=sig)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c1 = Conditional(b, a, "(b|a)")
    c1.index = 1
    c2 = Conditional(b, a, "(b|a)")
    c2.index = 1

    model = CRevisionModel.from_preocf_and_conditionals(pre, [c1])
    with pytest.raises(ValueError, match="already present"):
        model.add_conditional(c2)


def test_remove_conditional_updates_caches():
    sig = ["a", "b"]
    ranks = {format(i, "02b"): 0 for i in range(4)}
    pre = CustomPreOCF(ranks, signature=sig)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c1 = Conditional(b, a, "(b|a)")
    c1.index = 1
    model = CRevisionModel.from_preocf_and_conditionals(pre, [c1])

    # removing non-existing should be no-op
    model.remove_conditional(999)

    model.remove_conditional(1)
    assert 1 not in model.conds
    for w in model.worlds:
        assert 1 not in model.world_acc[w]
        assert 1 not in model.world_rej[w]


def test_to_compilation_hits_continue_and_rank_cache():
    # Worlds with a=0 should hit "continue" (no acc/rej for (b|a)).
    sig = ["a", "b"]
    ranks = {format(i, "02b"): 0 for i in range(4)}  # 00,01,10,11
    pre = CustomPreOCF(ranks, signature=sig)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c1 = Conditional(b, a, "(b|a)")
    c1.index = 1
    model = CRevisionModel.from_preocf_and_conditionals(pre, [c1])

    v1, f1 = model.to_compilation()
    # second call should use _rank_cache branch
    v2, f2 = model.to_compilation()
    assert isinstance(v2, dict)


def test_to_csp_uses_translate_to_csp(monkeypatch):
    sig = ["a", "b"]
    ranks = {format(i, "02b"): 0 for i in range(4)}
    pre = CustomPreOCF(ranks, signature=sig)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c1 = Conditional(b, a, "(b|a)")
    c1.index = 1
    model = CRevisionModel.from_preocf_and_conditionals(pre, [c1])

    import inference.c_revision as cr

    called = {"ok": False}
    def fake_translate(compilation, gamma_plus_zero, fixed_gamma_plus=None, fixed_gamma_minus=None):
        called["ok"] = True
        return []

    monkeypatch.setattr(cr, "translate_to_csp", fake_translate)
    out = model.to_csp(gamma_plus_zero=True)
    assert called["ok"] is True
    assert out == []

import pytest

from pysmt.shortcuts import Symbol
from inference.conditional import Conditional
from inference.c_revision_model import CRevisionModel


class _TinyRanking:
    signature = ["A", "B"]
    ranks = {"00": 0, "10": 0, "11": 0}

    def rank_world(self, w: str) -> int:
        return 0

    def world_satisfies_conditionalization(self, _w: str, _expr) -> bool:
        return False


def test_c_revision_model_add_conditional_requires_index():
    r = _TinyRanking()
    m = CRevisionModel(r, [])
    c = Conditional(Symbol("A"), Symbol("B"), "(A|B)")  # kein index gesetzt

    with pytest.raises((TypeError, ValueError)):
        m.add_conditional(c)


def test_c_revision_model_add_conditional_rejects_duplicate_index():
    r = _TinyRanking()
    c1 = Conditional(Symbol("A"), Symbol("B"), "(A|B)")  
    c1.index = 1
    c2 = Conditional(Symbol("A"), Symbol("B"), "(A|B)")  
    c2.index = 1

    m = CRevisionModel(r, [c1])
    with pytest.raises(ValueError):
        m.add_conditional(c2)


def test_c_revision_model_remove_conditional_updates_caches():
    r = _TinyRanking()
    c = Conditional(Symbol("A"), Symbol("B"), "(A|B)")
    c.index = 7

    m = CRevisionModel(r, [c])
    # sicherstellen: cond registriert
    assert 7 in m.conds

    m.remove_conditional(7)
    assert 7 not in m.conds
    assert 7 not in m.masks
    for w in m.worlds:
        assert 7 not in m.world_acc[w]
        assert 7 not in m.world_rej[w]


def test_c_revision_model_to_compilation_skips_worlds_with_no_acc_rej():
    r = _TinyRanking()
    # keine conditionals -> alle acc/rej leer -> continue-branch
    m = CRevisionModel(r, [])
    vmin, fmin = m.to_compilation()
    assert vmin == {}
    assert fmin == {}


def test_c_revision_model_to_csp_calls_translate(monkeypatch):
    # to_csp Pfad + lokale Import-Route
    r = _TinyRanking()
    c = Conditional(Symbol("A"), Symbol("B"), "(A|B)")
    c.index = 1
    m = CRevisionModel(r, [c])

    import inference.c_revision as cr

    monkeypatch.setattr(cr, "translate_to_csp", lambda *_a, **_k: ["ok"])
    out = m.to_csp()
    assert out == ["ok"]

