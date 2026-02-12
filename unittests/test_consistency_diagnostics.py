"""
Consistency diagnostics tests.

Purpose
-------
Exercise `consistency_diagnostics` and `format_diagnostics` for both standard
and extended (weakly) modes, with and without facts, ensuring keys and types are
present and values are sensible for basic scenarios.

Run
---
uv run pytest -q unittests/test_consistency_diagnostics.py
"""

import pytest

from inference.consistency_diagnostics import (
    consistency_diagnostics,
    format_diagnostics,
)
from parser.Wrappers import parse_belief_base


def _birds_bb():
    kb = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
    return parse_belief_base(kb)


def test_case1_standard_no_facts():
    bb = _birds_bb()
    diag = consistency_diagnostics(bb, extended=False, uses_facts=False)
    assert "bb_consistent" in diag
    assert diag["bb_consistent"] is True
    # No facts/combined fields expected
    assert "f_consistent" not in diag
    assert "c_consistent" not in diag
    assert "bb_w_consistent" not in diag


def test_case2_standard_with_facts():
    bb = _birds_bb()
    diag = consistency_diagnostics(
        bb, extended=False, uses_facts=True, facts=["b", "!p"]
    )
    assert diag["f_consistent"] is True
    assert diag["bb_consistent"] is True
    # Combined may or may not be consistent under standard for given facts; only check presence and type
    assert "c_consistent" in diag
    assert isinstance(diag["c_consistent"], bool)
    # Weak result not requested in standard mode
    assert "bb_w_consistent" not in diag


def test_case3_extended_no_facts():
    bb = _birds_bb()
    diag = consistency_diagnostics(bb, extended=True, uses_facts=False)
    assert diag["bb_w_consistent"] is True
    # Birds base is standard-consistent as well
    assert diag["bb_consistent"] is True
    # No combined in this case
    assert "c_consistent" not in diag


def test_case4_extended_with_facts():
    bb = _birds_bb()
    # Use a complex fact; expected to be consistent with signature
    diag = consistency_diagnostics(bb, extended=True, uses_facts=True, facts=["!(p;f)"])
    assert diag["f_consistent"] is True
    assert diag["bb_w_consistent"] is True
    assert diag["bb_consistent"] in (True, False)
    assert diag["c_consistent"] in (True, False)
    # c_infinity_increase appears only when both base and combined extended partitions exist
    if diag.get("c_consistent") is True and diag.get("bb_w_consistent") is True:
        # It can appear with True/False depending on whether ∞-layer grows
        if "c_infinity_increase" in diag:
            assert isinstance(diag["c_infinity_increase"], bool)


def test_uses_facts_requires_facts():
    bb = _birds_bb()
    with pytest.raises(ValueError):
        _ = consistency_diagnostics(bb, extended=False, uses_facts=True, facts=None)


def test_unknown_fact_variable_raises():
    bb = _birds_bb()
    with pytest.raises(ValueError):
        _ = consistency_diagnostics(
            bb, extended=True, uses_facts=True, facts=["x"]
        )  # x not in signature


def test_formatter_runs():
    bb = _birds_bb()
    diag = consistency_diagnostics(
        bb, extended=True, uses_facts=True, facts=["b"]
    )  # simple fact
    s = format_diagnostics(diag)
    assert isinstance(s, str)
    # Should contain key names
    for key in ["facts=", "bb=", "bb_w=", "combined=", "inf_inc="]:
        assert key in s

# ---------------------------------------------------------------------------
# Additional edge-case tests for consistency_diagnostics coverage gaps
# ---------------------------------------------------------------------------

import inference.consistency_diagnostics as cd
from pysmt.shortcuts import Symbol
from pysmt.typing import BOOL


def test_facts_jointly_satisfiable_empty_list_true():
    bb = _birds_bb()
    assert cd.facts_jointly_satisfiable(bb.signature, []) is True


def test_parse_fact_accepts_fnode():
    bb = _birds_bb()
    p = Symbol("p", BOOL)
    assert cd.facts_jointly_satisfiable(bb.signature, [p]) in (True, False)


def test_parse_fact_invalid_type_raises_typeerror():
    bb = _birds_bb()
    try:
        cd.facts_jointly_satisfiable(bb.signature, [object()])  # type: ignore[list-item]
        assert False, "expected TypeError"
    except TypeError:
        pass


def test_augment_belief_base_with_empty_facts_returns_same_object():
    bb = _birds_bb()
    out = cd.augment_belief_base_with_facts(bb, [])
    assert out is bb


def test_inconsistent_facts_warn_path(monkeypatch):
    bb = _birds_bb()
    warned = {"called": False}

    monkeypatch.setattr(cd.logger, "warning", lambda *a, **k: warned.__setitem__("called", True))

    diag = cd.consistency_diagnostics(
        bb,
        extended=False,
        uses_facts=True,
        facts=["p", "!p"],  # inconsistent
        on_inconsistent="warn",
    )
    assert diag["f_consistent"] is False
    assert warned["called"] is True


def test_inconsistent_facts_raise_path():
    bb = _birds_bb()
    import pytest

    with pytest.raises(ValueError, match="Facts are mutually inconsistent"):
        cd.consistency_diagnostics(
            bb,
            extended=False,
            uses_facts=True,
            facts=["p", "!p"],
            on_inconsistent="raise",
        )


def test_precomputed_base_extended_is_used():
    bb = _birds_bb()
    # force the "precomputed" branch
    precomputed = {"base_extended": ([[]], ([0], 0, 0))}
    diag = cd.consistency_diagnostics(
        bb,
        extended=True,
        uses_facts=False,
        precomputed=precomputed,
    )
    assert "bb_w_consistent" in diag


def test_precomputed_base_extended_false_sets_both_false():
    bb = _birds_bb()
    precomputed = {"base_extended": (False, ([0], 0, 0))}
    diag = cd.consistency_diagnostics(
        bb,
        extended=True,
        uses_facts=False,
        precomputed=precomputed,
    )
    assert diag["bb_w_consistent"] is False
    assert diag["bb_consistent"] is False


def test_precomputed_combined_extended_is_used():
    bb = _birds_bb()
    precomputed = {
        "base_extended": ([[]], ([0], 0, 0)),
        "combined_extended": ([[]], ([0], 0, 0)),
    }
    diag = cd.consistency_diagnostics(
        bb,
        extended=True,
        uses_facts=True,
        facts=["b"],
        precomputed=precomputed,
    )
    assert "c_consistent" in diag


def test_precomputed_combined_standard_is_used():
    bb = _birds_bb()
    precomputed = {"combined_standard": ([[]], ([0], 0, 0))}
    diag = cd.consistency_diagnostics(
        bb,
        extended=False,
        uses_facts=True,
        facts=["b"],
        precomputed=precomputed,
    )
    assert "c_consistent" in diag


def test_format_diagnostics_verbose_runs():
    bb = _birds_bb()
    diag = cd.consistency_diagnostics(bb, extended=True, uses_facts=True, facts=["b"])
    s = cd.format_diagnostics_verbose(diag)
    assert isinstance(s, str)
    assert "facts_consistent=" in s
    assert "belief_base_consistent=" in s
