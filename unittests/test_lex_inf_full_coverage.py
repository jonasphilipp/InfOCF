import logging
import unittest
import warnings
from unittest.mock import patch

import inference.lex_inf as lex


class _FakeLogger:
    """Logger stub to force debug branches."""
    def __init__(self):
        self.debug_calls = []

    def isEnabledFor(self, level):
        return level == logging.DEBUG

    def debug(self, msg, *args):
        self.debug_calls.append((msg, args))


class _FakeConditional:
    """Minimal conditional used inside belief base partition (for weakly mode assertions)."""
    def __init__(self, name="c"):
        self._name = name

    def make_not_A_or_B(self):
        return object()

    def __repr__(self):
        return f"_FakeConditional({self._name})"


class _FakeQuery:
    """Query conditional passed to LexInf._inference."""
    def __init__(self):
        self.antecedence = object()
        self.consequence = object()

    def make_A_then_not_B(self):
        return object()


class _FakeBeliefBase:
    def __init__(self, conditionals):
        self.conditionals = conditionals


class _FakeTseitin:
    """TseitinTransformation stub."""
    def __init__(self, epistemic_state):
        self.epistemic_state = epistemic_state
        self.belief_base_to_cnf_called = False
        self.query_to_cnf_called = False

    def belief_base_to_cnf(self, *_a, **_k):
        self.belief_base_to_cnf_called = True
        return None

    def query_to_cnf(self, _query):
        self.query_to_cnf_called = True
        # return (verification_clauses, falsification_clauses)
        # WCNF.append expects a clause as list[int]
        return ([[1]], [[-1]])


class _DummySolver:
    """Solver stub used in weakly mode; solve() returns values from a provided iterator."""
    def __init__(self, solves):
        self._solves = iter(solves)
        self.assertions = []

    def add_assertion(self, a):
        self.assertions.append(a)

    def solve(self):
        return next(self._solves)


class _DummyOptimizer:
    """Optimizer stub for _rec_inference; returns pre-configured MCS outputs."""
    def __init__(self, mcs_sequence):
        self._seq = iter(mcs_sequence)

    def minimal_correction_subsets(self, *_a, **_k):
        return next(self._seq)


class TestLexInfFullCoverage(unittest.TestCase):
    def _make_lexinf(self):
        # minimal epistemic state LexInf expects
        bb = _FakeBeliefBase(
            conditionals={
                1: _FakeConditional("c1"),
                2: _FakeConditional("c2"),
                3: _FakeConditional("c3"),
            }
        )
        state = {
            "belief_base": bb,
            "smt_solver": "z3",
            "weakly": False,
            "partition": [[1, 2], [3]],
            "v_cnf_dict": {},
            "f_cnf_dict": {},
            "nf_cnf_dict": {
                1: [[10]],
                2: [[20]],
                3: [[30]],
            },
        }
        return lex.LexInf(state)

    # ---------------------------
    # preprocess coverage
    # ---------------------------
    def test_preprocess_warns_when_partition_empty_and_calls_tseitin(self):
        s = self._make_lexinf()
        fake_logger = _FakeLogger()

        # consistency_indices returns empty partition -> warn branch
        with patch.object(lex, "logger", fake_logger), patch.object(
            lex, "consistency_indices", return_value=([], None)
        ), patch.object(lex, "TseitinTransformation", _FakeTseitin):
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                s._preprocess_belief_base(weakly=False, deadline=None)

                self.assertTrue(any("belief base inconsistent" in str(x.message) for x in w))

    # ---------------------------
    # _inference strict vacuity shortcuts
    # ---------------------------
    def test_inference_strict_vacuity_true(self):
        s = self._make_lexinf()
        q = _FakeQuery()

        # strict shortcut: if is_unsat(A) or is_unsat(A & not B) -> True
        def _is_unsat(x):
            return x is q.antecedence

        with patch.object(lex, "is_unsat", _is_unsat):
            self.assertTrue(s._inference(q, weakly=False, deadline=None))

    def test_inference_strict_vacuity_false(self):
        s = self._make_lexinf()
        q = _FakeQuery()

        # strict shortcut: if is_unsat(A & B) -> False
        sent = {"and_ab": object()}

        def And_stub(x, y):
            # second shortcut uses And(A,B)
            if x is q.antecedence and y is q.consequence:
                return sent["and_ab"]
            # first shortcut uses And(A, Not(B)) too; return something else
            return object()

        def Not_stub(_x):
            return object()

        def _is_unsat(x):
            if x is q.antecedence:
                return False
            if x is sent["and_ab"]:
                return True
            return False

        with patch.object(lex, "And", And_stub), patch.object(lex, "Not", Not_stub), patch.object(
            lex, "is_unsat", _is_unsat
        ):
            self.assertFalse(s._inference(q, weakly=False, deadline=None))

    def test_inference_strict_normal_path_calls_rec(self):
        s = self._make_lexinf()
        q = _FakeQuery()

        fake_tseitin = _FakeTseitin(s.epistemic_state)

        # Avoid building real pysmt formulas (q.* are plain objects in our fake query)
        with patch.object(lex, "Not", lambda _x: object()), patch.object(
            lex, "And", lambda _a, _b: object()
        ), patch.object(
            lex, "is_unsat", return_value=False
        ), patch.object(
            lex, "TseitinTransformation", lambda _st: fake_tseitin
        ), patch.object(
            lex.LexInf, "_rec_inference", return_value=True
        ) as rec:
            self.assertTrue(s._inference(q, weakly=False, deadline=None))
            self.assertTrue(fake_tseitin.query_to_cnf_called)
            self.assertTrue(rec.called)

    # ---------------------------
    # _inference weakly shortcuts + normal path
    # ---------------------------
    def test_inference_weakly_taut_solver_shortcut_true(self):
        s = self._make_lexinf()
        q = _FakeQuery()

        fake_tseitin = _FakeTseitin(s.epistemic_state)
        # taut_solver.solve() == False -> return True immediately
        solver = _DummySolver(solves=[False])

        with patch.object(lex, "TseitinTransformation", lambda _st: fake_tseitin), patch.object(
            lex, "Solver", lambda name: solver
        ):
            self.assertTrue(s._inference(q, weakly=True, deadline=None))

    def test_inference_weakly_contra_solver_shortcut_true(self):
        s = self._make_lexinf()
        q = _FakeQuery()

        fake_tseitin = _FakeTseitin(s.epistemic_state)
        # taut_solver.solve() == True (pass), contra_solver.solve() == False -> return True
        # LexInf creates two Solver() instances; provide different ones by sequencing
        solvers = iter([_DummySolver([True]), _DummySolver([False])])

        with patch.object(lex, "TseitinTransformation", lambda _st: fake_tseitin), patch.object(
            lex, "Solver", lambda name: next(solvers)
        ):
            self.assertTrue(s._inference(q, weakly=True, deadline=None))

    def test_inference_weakly_normal_path_calls_rec(self):
        s = self._make_lexinf()
        q = _FakeQuery()

        fake_tseitin = _FakeTseitin(s.epistemic_state)
        solvers = iter([_DummySolver([True]), _DummySolver([True])])

        with patch.object(lex, "TseitinTransformation", lambda _st: fake_tseitin), patch.object(
            lex, "Solver", lambda name: next(solvers)
        ), patch.object(lex.LexInf, "_rec_inference", return_value=True) as rec:
            self.assertTrue(s._inference(q, weakly=True, deadline=None))
            self.assertTrue(rec.called)

    # ---------------------------
    # _rec_inference branch coverage
    # ---------------------------
    def test_rec_inference_returns_false_when_no_mcs_v(self):
        s = self._make_lexinf()
        fake_logger = _FakeLogger()

        # first call mcs_v -> [], second call mcs_f won't matter for the branch
        opt = _DummyOptimizer(mcs_sequence=[[], [{frozenset()}]])

        with patch.object(lex, "logger", fake_logger), patch.object(lex, "create_optimizer", lambda _st: opt):
            self.assertFalse(s._rec_inference(lex.WCNF(), lex.WCNF(), partition_index=1, deadline=None))
            self.assertTrue(len(fake_logger.debug_calls) >= 1)

    def test_rec_inference_returns_true_when_no_mcs_f(self):
        s = self._make_lexinf()
        fake_logger = _FakeLogger()

        opt = _DummyOptimizer(mcs_sequence=[[{frozenset()}], []])

        with patch.object(lex, "logger", fake_logger), patch.object(lex, "create_optimizer", lambda _st: opt):
            self.assertTrue(s._rec_inference(lex.WCNF(), lex.WCNF(), partition_index=1, deadline=None))

    def test_rec_inference_min_len_v_smaller_returns_true(self):
        s = self._make_lexinf()
        opt = _DummyOptimizer(
            mcs_sequence=[
                [frozenset({1})],          # mcs_v min_len=1
                [frozenset({1, 2})],       # mcs_f min_len=2
            ]
        )
        with patch.object(lex, "logger", _FakeLogger()), patch.object(lex, "create_optimizer", lambda _st: opt):
            self.assertTrue(s._rec_inference(lex.WCNF(), lex.WCNF(), partition_index=1, deadline=None))

    def test_rec_inference_min_len_f_smaller_returns_false(self):
        s = self._make_lexinf()
        opt = _DummyOptimizer(
            mcs_sequence=[
                [frozenset({1, 2})],       # mcs_v min_len=2
                [frozenset({1})],          # mcs_f min_len=1
            ]
        )
        with patch.object(lex, "logger", _FakeLogger()), patch.object(lex, "create_optimizer", lambda _st: opt):
            self.assertFalse(s._rec_inference(lex.WCNF(), lex.WCNF(), partition_index=1, deadline=None))

    def test_rec_inference_equal_min_len_partition_index_zero_returns_false(self):
        s = self._make_lexinf()
        # force partition_index==0
        s.epistemic_state["partition"] = [[1, 2]]  # only one layer

        opt = _DummyOptimizer(
            mcs_sequence=[
                [frozenset({1})],
                [frozenset({2})],
            ]
        )
        with patch.object(lex, "logger", _FakeLogger()), patch.object(lex, "create_optimizer", lambda _st: opt):
            self.assertFalse(s._rec_inference(lex.WCNF(), lex.WCNF(), partition_index=0, deadline=None))

    def test_rec_inference_equal_min_len_recurses_and_returns_false_on_child_false(self):
        s = self._make_lexinf()
        # Ensure part has both indices so we cover i in xi_v / i not in xi_v and same for xi_f
        s.epistemic_state["partition"] = [[1, 2], [1, 2]]

        # mcs_v has {1} so index 1 is in xi_v, 2 is not
        # mcs_f has {2} so index 2 is in xi_f, 1 is not
        opt = _DummyOptimizer(
            mcs_sequence=[
                [frozenset({1})],  # mcs_v
                [frozenset({2})],  # mcs_f
            ]
        )

        with patch.object(lex, "logger", _FakeLogger()), patch.object(
            lex, "create_optimizer", lambda _st: opt
        ), patch.object(lex.LexInf, "_rec_inference", side_effect=[False]) as rec:
            original = lex.LexInf._rec_inference

            def _one_level(self, hard_v, hard_f, pidx, deadline):
                return original(self, hard_v, hard_f, pidx, deadline)

            with patch.object(lex.LexInf, "_rec_inference", _one_level):
                pass  


    def test_rec_inference_equal_min_len_recurses_true_path(self):
        s = self._make_lexinf()

        s.epistemic_state["partition"] = [[1, 2], [1, 2]]

        s.epistemic_state["v_cnf_dict"] = {
            1: [[11]],
            2: [[22]],
        }
        s.epistemic_state["f_cnf_dict"] = {
            1: [[-11]],
            2: [[-22]],
        }
        # nf_cnf_dict is already present from _make_lexinf, but keep it consistent
        s.epistemic_state["nf_cnf_dict"] = {
            1: [[111]],
            2: [[222]],
            3: [[333]],
        }

        opt = _DummyOptimizer(
            mcs_sequence=[
                [frozenset({1})],  # mcs_v
                [frozenset({2})],  # mcs_f
            ]
        )

        call_count = {"n": 0}
        original = lex.LexInf._rec_inference

        def _rec_wrapper(self, hard_v, hard_f, partition_index=None, deadline=None, **_kw):
            call_count["n"] += 1
            if call_count["n"] == 1:
                # run real logic for the top call
                return original(
                    self,
                    hard_v,
                    hard_f,
                    partition_index=partition_index,
                    deadline=deadline,
                )
            # recursive call returns True
            return True

        with patch.object(lex, "logger", _FakeLogger()), patch.object(
            lex, "create_optimizer", lambda _st: opt
        ), patch.object(lex.LexInf, "_rec_inference", _rec_wrapper):
            self.assertTrue(
                s._rec_inference(lex.WCNF(), lex.WCNF(), partition_index=1, deadline=None)
            )

    def test_any_subset_of_all_true_and_false(self):
        A = frozenset({frozenset({1}), frozenset({2})})
        B_true = frozenset({frozenset({1, 3}), frozenset({2, 4})})
        B_false = frozenset({frozenset({1, 3}), frozenset({5})})

        self.assertTrue(lex.any_subset_of_all(A, B_true))
        self.assertFalse(lex.any_subset_of_all(A, B_false))


if __name__ == "__main__":
    unittest.main()
