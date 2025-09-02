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
