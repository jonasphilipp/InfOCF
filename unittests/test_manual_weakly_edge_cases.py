"""
Manual weakly-semantics edge-case tests.

Purpose
-------
Exercise specific corner cases for weakly/extended semantics to ensure
logical properties (e.g. vacuity with last layer, partition interaction) hold.

How to add cases
----------------
Use the helper `run_case(bb, qs, expected, systems=None)`:
- bb: inline belief base (string)
- qs: inline queries (string)
- expected: list[bool] corresponding to queries order
- systems: target systems; defaults to ["p-entailment","system-z","system-w","lex_inf"].
  z3 variants are exercised for supported systems.

Semantics
---------
weakly=True (extended). SMT solver is z3. The test `test_default_mode_remains_strict`
also asserts the strict mode raises where appropriate.

Run
---
uv run pytest -q unittests/test_manual_weakly_edge_cases.py
"""

import unittest

from inference.inference_manager import InferenceManager
from parser.Wrappers import parse_belief_base, parse_queries


def run_case(bb: str, qs: str, expected: list[bool], systems=None):
    if systems is None:
        systems = ["p-entailment", "system-z", "system-w", "lex_inf"]
    belief_base = parse_belief_base(bb)
    queries = parse_queries(qs)
    for sys in systems:
        # default variant
        manager = InferenceManager(belief_base, sys, smt_solver="z3", weakly=True)
        res = manager.inference(queries)
        actual = res["result"].tolist()
        assert actual == expected, (
            f"System {sys} mismatch. Expected {expected} but got {actual}.\n"
            f"BB: {bb}\nQ: {qs}"
        )
        # z3 pmaxsat variant for systems that support it
        if sys in ["system-w", "lex_inf"]:
            manager_z3 = InferenceManager(
                belief_base, sys, smt_solver="z3", pmaxsat_solver="z3", weakly=True
            )
            res_z3 = manager_z3.inference(queries)
            actual_z3 = res_z3["result"].tolist()
            assert actual_z3 == expected, (
                f"System {sys} (z3 variant) mismatch. Expected {expected} but got {actual_z3}.\n"
                f"BB: {bb}\nQ: {qs}"
            )


class TestWeaklyEdgeCases(unittest.TestCase):
    def test_vacuity_impossible_antecedent(self):
        # a is forbidden by last layer → (b|a) must be True
        bb = "signature\na,b\n\nconditionals\nkb{\n(Bottom|a)\n}"
        qs = "(b|a)"
        run_case(bb, qs, [True])

    def test_last_layer_implies_consequence(self):
        # Last layer excludes p & ¬j, together with (f|b),(b|p) should entail (!j|p,f,b)
        bb = (
            "signature\n"
            "b,p,f,j\n\n"
            "conditionals\n"
            "kb{\n"
            "(b|p),\n"
            "(f|b),\n"
            "(!f|p),\n"
            "(f|p,j),\n"
            "(Bottom|p,!j)\n"
            "}"
        )
        qs = "(!j|p,f,b)"
        run_case(bb, qs, [True])

    def test_partition_contradiction_vs_knowledge(self):
        # Two contradictory rules on a placed in last layer should still allow unrelated (d|c)
        bb = "signature\na,b,c,d\n\nconditionals\nkb{\n(b|a),\n(!b|a),\n(d|c)\n}"
        qs = "(d|c),(d|a,c),(!d|a,c),(!d|c)"
        run_case(bb, qs, [True, True, True, False])

    def test_default_mode_remains_strict(self):
        # Same as first case but in strict mode should treat as inconsistency for inference
        bb = "signature\na,b\n\nconditionals\nkb{\n(Bottom|a)\n}"
        qs = parse_queries("(b|a),(a|Top),(Bottom|a)")
        belief_base = parse_belief_base(bb)
        for sys in ["system-z", "system-w", "lex_inf"]:
            with self.assertRaises(AssertionError):
                manager = InferenceManager(
                    belief_base, sys, smt_solver="z3", weakly=False
                )
                _ = manager.inference(qs)

# ---------------------------------------------------------------------------
# Additional edge-case tests for inference.inference_manager
# ---------------------------------------------------------------------------

import pytest

from pysmt.shortcuts import Symbol, TRUE
from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.queries import Queries
import inference.inference_manager as im


def _patch_env(monkeypatch, solvers=("z3",)):
    class Factory:
        def all_solvers(self):
            return {s: object() for s in solvers}

    class Env:
        factory = Factory()

    monkeypatch.setattr(im, "get_env", lambda: Env())


def _dummy_bb(name="bb"):
    return BeliefBase(signature=["a"], conditionals={}, name=name)


def _dummy_query(text="(b|a)"):
    a = Symbol("a")
    b = Symbol("b")
    return Conditional(consequence=b, antecedence=a, textRepresentation=text)


def test_inference_manager_init_clears_pmaxsat_for_p_entailment(monkeypatch):
    _patch_env(monkeypatch, solvers=("z3",))

    mgr = im.InferenceManager(
        belief_base=_dummy_bb(),
        inference_system="P-ENTAILMENT",  # mixed case to test .lower()
        smt_solver="Z3",
        pmaxsat_solver="rc2",
    )

    assert mgr.epistemic_state["inference_system"] == "p-entailment"
    assert mgr.epistemic_state["smt_solver"] == "z3"
    # For p-entailment, pmaxsat is intentionally disabled
    assert mgr.epistemic_state["pmaxsat_solver"] == ""


def test_inference_manager_init_raises_for_unavailable_solver(monkeypatch):
    _patch_env(monkeypatch, solvers=("z3",))

    with pytest.raises(AssertionError):
        im.InferenceManager(
            belief_base=_dummy_bb(),
            inference_system="system-w",
            smt_solver="cvc5",  # not advertised by our patched env
        )


def test_create_inference_instance_invalid_system_raises():
    state = im.create_epistemic_state(
        belief_base=_dummy_bb("bb1"),
        inference_system="nope",
        smt_solver="z3",
        pmaxsat_solver="",
        weakly=False,
    )
    with pytest.raises(Exception, match="no correct inference system"):
        im.create_inference_instance(state)


def test_inference_timeout_math_handles_overrun_preprocessing(monkeypatch):
    _patch_env(monkeypatch, solvers=("z3",))

    q = _dummy_query("(b|a)")
    queries = Queries({0: q})

    mgr = im.InferenceManager(_dummy_bb("bbx"), "system-z", smt_solver="z3")

    seen = {}

    class DummyInference:
        def __init__(self, epistemic_state):
            self.epistemic_state = epistemic_state

        def preprocess_belief_base(self, timeout):
            seen["preprocess_timeout"] = timeout
            # 15s (in ms) preprocessing, intentionally larger than total_timeout=10s
            self.epistemic_state["preprocessing_time"] = 15000
            self.epistemic_state["preprocessing_done"] = True
            self.epistemic_state["preprocessing_timed_out"] = False

        def inference(self, conds, timeout, multi_inference):
            seen["inference_timeout"] = timeout
            seen["multi_inference"] = multi_inference
            # keys must be str(q) for InferenceManager's bookkeeping
            return {str(c): (i, True, False, 123.456) for i, c in conds.items()}

    monkeypatch.setattr(im, "create_inference_instance", lambda state: DummyInference(state))

    df = mgr.inference(
        queries,
        total_timeout=10,
        preprocessing_timeout=20,  # => min(10,20)=10
        inference_timeout=9,       # => min(10-15, 9) = -5
        queries_name="my_queries",
        multi_inference=True,
        decimals=1,
    )

    assert seen["preprocess_timeout"] == 10
    assert seen["inference_timeout"] == -5.0
    assert seen["multi_inference"] is True

    assert len(df) == 1
    assert df.at[0, "queries"] == "my_queries"
    assert df.at[0, "belief_base"] == "bbx"
    assert df.at[0, "query"] == str(q)
    assert df.at[0, "result"] is True
    assert df.at[0, "preprocessing_time"] == 15000.0
    assert df.at[0, "inference_time"] == 123.5  # rounded to 1 decimal


def test_inference_with_empty_queries_returns_empty_df(monkeypatch):
    _patch_env(monkeypatch, solvers=("z3",))

    mgr = im.InferenceManager(_dummy_bb("bb_empty"), "system-z", smt_solver="z3")
    empty_queries = Queries({})

    class DummyInference:
        def __init__(self, epistemic_state):
            self.epistemic_state = epistemic_state

        def preprocess_belief_base(self, timeout):
            self.epistemic_state["preprocessing_time"] = 0
            self.epistemic_state["preprocessing_done"] = True
            self.epistemic_state["preprocessing_timed_out"] = False

        def inference(self, conds, timeout, multi_inference):
            return {}

    monkeypatch.setattr(im, "create_inference_instance", lambda state: DummyInference(state))

    df = mgr.inference(empty_queries)
    assert df.empty
    # still has the expected report columns
    assert "inference_system" in df.columns
    assert "query" in df.columns

# ---------------------------------------------------------------------------
# Additional edge-case tests for inference_manager debug-only branches
# ---------------------------------------------------------------------------

import inference.inference_manager as im
from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol
from pysmt.typing import BOOL


def test_create_inference_instance_debug_branches(monkeypatch):
    # Patch debug enabled
    monkeypatch.setattr(im.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(im.logger, "debug", lambda *a, **k: None)

    # Patch implementations to avoid heavy init
    class Dummy:  # noqa: D401
        def __init__(self, state): self.state = state

    monkeypatch.setattr(im, "SystemWZ3", Dummy)
    monkeypatch.setattr(im, "SystemW", Dummy)
    monkeypatch.setattr(im, "LexInfZ3", Dummy)
    monkeypatch.setattr(im, "LexInf", Dummy)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    bb = BeliefBase(["a", "b"], {0: Conditional(b, a, "(b|a)")}, "bb")

    # system-w z3 branch
    s = im.create_epistemic_state(bb, "system-w", "z3", pmaxsat_solver="z3", weakly=False)
    assert isinstance(im.create_inference_instance(s), Dummy)

    # system-w non-z3 branch
    s = im.create_epistemic_state(bb, "system-w", "z3", pmaxsat_solver="rc2", weakly=False)
    assert isinstance(im.create_inference_instance(s), Dummy)

    # lex_inf z3 branch
    s = im.create_epistemic_state(bb, "lex_inf", "z3", pmaxsat_solver="z3", weakly=False)
    assert isinstance(im.create_inference_instance(s), Dummy)

    # lex_inf non-z3 branch
    s = im.create_epistemic_state(bb, "lex_inf", "z3", pmaxsat_solver="rc2", weakly=False)
    assert isinstance(im.create_inference_instance(s), Dummy)


def test_inference_manager_results_debug_summary(monkeypatch):
    monkeypatch.setattr(im.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(im.logger, "debug", lambda *a, **k: None)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    bb = BeliefBase(["a", "b"], {0: Conditional(b, a, "(b|a)")}, "bb")

    mgr = im.InferenceManager(bb, "system-z", smt_solver="z3", weakly=False)

    class DummyInference:
        def __init__(self, state): self.epistemic_state = state
        def preprocess_belief_base(self, timeout):
            self.epistemic_state["preprocessing_time"] = 0
            self.epistemic_state["preprocessing_done"] = True
            self.epistemic_state["preprocessing_timed_out"] = False
        def inference(self, conds, timeout, multi_inference):
            # one ok, one timeout-like
            items = list(conds.items())
            out = {}
            for i, c in items:
                out[str(c)] = (i, True, False, 1.0)
            return out

    monkeypatch.setattr(im, "create_inference_instance", lambda state: DummyInference(state))

    from inference.queries import Queries
    q = Conditional(b, a, "(b|a)")
    df = mgr.inference(Queries({0: q}))
    assert df.at[0, "result"] in (True, False)

def test_ci_preprocess_belief_base_calls_tseitin_compile_translate(monkeypatch):
    import inference.c_inference as ci

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)

    bb = BeliefBase(["a", "b"], {0: Conditional(b, a, "(b|a)")}, "bb")
    state = {"belief_base": bb, "smt_solver": "z3"}
    inf = ci.CInference(state)

    called = {"tseitin": False, "compile": False, "translate": False}

    class DummyTseitin:
        def __init__(self, state): self.state = state
        def belief_base_to_cnf(self, *args):
            called["tseitin"] = True

    monkeypatch.setattr(ci, "TseitinTransformation", DummyTseitin)

    def fake_compile(deadline=None):
        called["compile"] = True
        return 0.0

    def fake_translate():
        called["translate"] = True
        return ["CSP"]

    monkeypatch.setattr(inf, "compile_constraint", fake_compile)
    monkeypatch.setattr(inf, "translate", fake_translate)

    inf._preprocess_belief_base(weakly=False, deadline=None)

    assert called["tseitin"] is True
    assert called["compile"] is True
    assert called["translate"] is True
    assert inf.base_csp == ["CSP"]  

import inference.c_inference as ci
from pysmt.shortcuts import Int, LE

def test_c_inference_debug_branches_makeSummation_freshVars_minima_encoding(monkeypatch):
    # Force debug branches in c_inference.py to execute
    monkeypatch.setattr(ci.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(ci.logger, "debug", lambda *a, **k: None)

    # makeSummation debug lines (summ/subsum/result)
    minima = {0: [[1, 2], []]}
    sums = ci.makeSummation(minima)
    assert 0 in sums and isinstance(sums[0], list)

    # freshVars debug line
    mv, mf = ci.freshVars(0)
    assert mv is not None and mf is not None

    # minima_encoding debug line
    enc = ci.minima_encoding(mv, sums[0])
    assert isinstance(enc, list)


def test_c_inference_debug_branches_encoding_and_translate(monkeypatch):
    # Force debug branches in encoding()/translate() to execute
    monkeypatch.setattr(ci.logger, "isEnabledFor", lambda *_: True)
    monkeypatch.setattr(ci.logger, "debug", lambda *a, **k: None)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)

    # BeliefBase with one conditional; translate() enumerates starting at 1
    bb = BeliefBase(signature=["a", "b"], conditionals={0: Conditional(b, a, "(b|a)")}, name="bb")

    state = {
        "belief_base": bb,
        "smt_solver": "z3",
        # keys must match translate()’s enumeration start=1
        "vMin": {1: [[1]]},
        "fMin": {1: [[1]]},
    }
    inf = ci.CInference(state)

    csp = inf.translate()
    assert isinstance(csp, list) and len(csp) > 0


def test_compile_and_encode_query_edge_case_verification_only_returns_impossible(monkeypatch):
    # Covers: if not fMin and vMin -> return [LE(Int(1), Int(0))]
    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    bb = BeliefBase(signature=["a", "b"], conditionals={}, name="bb")

    inf = ci.CInference({"belief_base": bb, "smt_solver": "z3", "nf_cnf_dict": {}})

    # Patch TseitinTransformation so we fully control the returned CNFs
    class DummyTseitin:
        def __init__(self, _state): ...
        def query_to_cnf(self, _query):
            return ([[1]], [[1]])  # two parts: verification CNF, falsification CNF

    monkeypatch.setattr(ci, "TseitinTransformation", DummyTseitin)

    # Patch optimizer: first call -> non-empty (vMin), second call -> empty (fMin)
    calls = {"n": 0}

    class DummyOpt:
        def minimal_correction_subsets(self, _wcnf, deadline=None):
            calls["n"] += 1
            return [[1]] if calls["n"] == 1 else []

    monkeypatch.setattr(ci, "create_optimizer", lambda _st: DummyOpt())

    q = Conditional(consequence=b, antecedence=a, textRepresentation="(b|a)")
    csp, _t = inf.compile_and_encode_query(q)
    assert csp == [LE(Int(1), Int(0))]


def test_compile_and_encode_query_edge_case_both_empty_returns_empty(monkeypatch):
    # Covers: if not vMin and not fMin -> return []
    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    bb = BeliefBase(signature=["a", "b"], conditionals={}, name="bb")

    inf = ci.CInference({"belief_base": bb, "smt_solver": "z3", "nf_cnf_dict": {}})

    class DummyTseitin:
        def __init__(self, _state): ...
        def query_to_cnf(self, _query):
            return ([[1]], [[1]])

    monkeypatch.setattr(ci, "TseitinTransformation", DummyTseitin)

    class DummyOpt:
        def minimal_correction_subsets(self, _wcnf, deadline=None):
            return []

    monkeypatch.setattr(ci, "create_optimizer", lambda _st: DummyOpt())

    q = Conditional(consequence=b, antecedence=a, textRepresentation="(b|a)")
    csp, _t = inf.compile_and_encode_query(q)
    assert csp == []

import warnings
import pytest
import types

import inference.system_z as sysz
import inference.system_w as sysw
import inference.system_w_z3 as syswz3
import inference.lex_inf as lex
import inference.consistency_sat as cs


def test_system_z_warns_on_inconsistent_partition(monkeypatch):
    # triggert system_z.py warn branch
    monkeypatch.setattr(sysz, "consistency", lambda *_a, **_k: (False, None))
    s = sysz.SystemZ({"belief_base": object(), "smt_solver": "z3", "weakly": False})
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        s._preprocess_belief_base(False, None)
        assert any("inconsistent" in str(x.message) for x in w)


def test_system_w_warns_on_inconsistent_partition(monkeypatch):
    # triggert system_w.py 
    monkeypatch.setattr(sysw, "consistency_indices", lambda *_a, **_k: ([], None))

    # vermeide echte Tseitin-Logik
    class _TT:
        def __init__(self, *_a, **_k): pass
        def belief_base_to_cnf(self, *_a, **_k): return None

    monkeypatch.setattr(sysw, "TseitinTransformation", _TT)

    s = sysw.SystemW(
        {
            "belief_base": object(),
            "smt_solver": "z3",
            "weakly": False,
            "partition": [],
            "v_cnf_dict": {},
            "f_cnf_dict": {},
            "nf_cnf_dict": {},
        }
    )

    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        s._preprocess_belief_base(False, None)
        assert any("inconsistent" in str(x.message) for x in w)


def test_system_w_z3_inconsistent_partition_returns_empty(monkeypatch):
    # triggert system_w_z3.py 
    monkeypatch.setattr(syswz3, "consistency", lambda *_a, **_k: (False, None))
    s = syswz3.SystemWZ3({"belief_base": object(), "smt_solver": "z3", "weakly": False})
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        s._preprocess_belief_base(False, None)
        assert s.epistemic_state["partition"] == []
        assert any("inconsistent" in str(x.message) for x in w)


def test_system_w_z3_not_weakly_calls_rec_inference(monkeypatch):
    # triggert system_w_z3.py 
    s = syswz3.SystemWZ3({"belief_base": object(), "smt_solver": "z3", "weakly": False})
    s.epistemic_state["partition"] = [[object()]]

    called = {"n": 0}
    monkeypatch.setattr(
        syswz3.SystemWZ3,
        "_rec_inference",
        lambda *_a, **_k: called.__setitem__("n", called["n"] + 1) or True,
    )

    from inference.conditional import Conditional
    from pysmt.shortcuts import Symbol
    q = Conditional(Symbol("A"), Symbol("B"), "(A|B)")

    assert s._inference(q, weakly=False, deadline=None) is True
    assert called["n"] == 1


def test_lexinf_warns_on_inconsistent_partition(monkeypatch):
    # triggert lex_inf.py 
    monkeypatch.setattr(lex, "consistency_indices", lambda *_a, **_k: ([], None))

    class _TT:
        def __init__(self, *_a, **_k): pass
        def belief_base_to_cnf(self, *_a, **_k): return None

    monkeypatch.setattr(lex, "TseitinTransformation", _TT)

    s = lex.LexInf(
        {
            "belief_base": object(),
            "smt_solver": "z3",
            "weakly": False,
            "partition": [],
            "v_cnf_dict": {},
            "f_cnf_dict": {},
            "nf_cnf_dict": {},
        }
    )
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter("always")
        s._preprocess_belief_base(False, None)
        assert any("inconsistent" in str(x.message) for x in w)


def test_lexinf_vacuity_shortcuts_true_false(monkeypatch):
    import inference.lex_inf as lex
    from inference.conditional import Conditional
    from pysmt.shortcuts import Symbol

    A = Symbol("A")
    B = Symbol("B")
    q = Conditional(A, B, "(A|B)")

    s = lex.LexInf(
        {
            "belief_base": object(),
            "smt_solver": "z3",
            "weakly": False,
            "partition": [[0]],  # only needs to exist / be non-empty for strict shortcuts
            "v_cnf_dict": {},
            "f_cnf_dict": {},
            "nf_cnf_dict": {},
        }
    )

    # -----------------------
    # Case 1: antecedence UNSAT => True
    # -----------------------
    monkeypatch.setattr(lex, "is_unsat", lambda x: x is q.antecedence)
    assert s._inference(q, weakly=False, deadline=None) is True

    # -----------------------
    # Case 2: A SAT, (A ∧ ¬B) SAT, but (A ∧ B) UNSAT => False
    # -----------------------
    sent = {"not_b": object(), "and_a_not_b": object(), "and_a_b": object()}

    def Not_stub(x):
        # Only Not(query.consequence) is used in the shortcut logic
        if x is q.consequence:
            return sent["not_b"]
        return object()

    def And_stub(x, y):
        # Distinguish And(A, Not(B)) vs And(A, B)
        if x is q.antecedence and y is sent["not_b"]:
            return sent["and_a_not_b"]
        if x is q.antecedence and y is q.consequence:
            return sent["and_a_b"]
        return object()

    monkeypatch.setattr(lex, "Not", Not_stub)
    monkeypatch.setattr(lex, "And", And_stub)

    def is_unsat_case2(x):
        # A is SAT
        if x is q.antecedence:
            return False
        # (A ∧ ¬B) is SAT (so first shortcut does NOT return True)
        if x is sent["and_a_not_b"]:
            return False
        # (A ∧ B) is UNSAT => should return False
        if x is sent["and_a_b"]:
            return True
        return False

    monkeypatch.setattr(lex, "is_unsat", is_unsat_case2)
    assert s._inference(q, weakly=False, deadline=None) is False

def test_consistency_sat_checkTautologies_branch(monkeypatch):
    # triggert consistency_sat.py 
    called = {"n": 0}

    # is_sat so faken, dass case1 False wird
    monkeypatch.setattr(cs, "is_sat", lambda *_a, **_k: (called.__setitem__("n", called["n"] + 1) or False))

    # Dummy-Conditional mit benötigten Methoden
    class _C:
        def make_A_then_B(self): return object()
        def make_A_then_not_B(self): return object()

    assert cs.checkTautologies({0: _C()}) is True
    assert called["n"] >= 1

if __name__ == "__main__":
    unittest.main()
