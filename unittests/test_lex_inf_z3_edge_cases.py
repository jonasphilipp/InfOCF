import logging
import unittest
import warnings
from unittest.mock import patch

import inference.lex_inf_z3 as lz3


class _FakeLogger:
    def __init__(self):
        self.debug_calls = []

    def isEnabledFor(self, level):
        return level == logging.DEBUG

    def debug(self, msg, *args):
        self.debug_calls.append((msg, args))


class _DummyOpt:
    def push(self):
        return None

    def pop(self):
        return None

    def add(self, _a):
        return None


class _DummyQueryZ3:
    def make_A_then_B(self):
        return object()

    def make_A_then_not_B(self):
        return object()


class _DummyConditionalZ3:
    def __init__(self, name="c"):
        self._name = name

    def make_A_then_not_B(self):
        return object()

    def make_not_A_or_B(self):
        return object()

    def __repr__(self):
        return f"_DummyConditionalZ3({self._name})"


class _DummyBeliefBase:
    def __init__(self):
        # content irrelevant for these patched tests
        self.conditionals = {}


class TestLexInfZ3EdgeCases(unittest.TestCase):
    def _make_system(self):
        # minimal epistemic_state for LexInfZ3
        state = {
            "belief_base": _DummyBeliefBase(),
            "smt_solver": "z3",
            "weakly": False,
            "partition": [[_DummyConditionalZ3("p1")]],
        }
        return lz3.LexInfZ3(state)

    def test_preprocess_inconsistent_warns_and_sets_empty_partition(self):
        """
        Covers lex_inf_z3.py lines 43-45:
          warn("belief base inconsistent"); partition=[]; return
        """
        s = self._make_system()

        with patch.object(lz3, "consistency", return_value=([], None)):
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                s._preprocess_belief_base(weakly=False, deadline=None)

                self.assertEqual(s.epistemic_state["partition"], [])
                self.assertTrue(any("belief base inconsistent" in str(x.message) for x in w))

    def test_inference_not_weakly_calls_rec_inference(self):
        """
        Covers lex_inf_z3.py line 84: result = self._rec_inference(...)
        """
        s = self._make_system()

        # ensure there is at least one layer so len(partition)-1 is valid
        s.epistemic_state["partition"] = [[_DummyConditionalZ3("p1")]]

        # patch translation to avoid constructing real z3 conditionals
        with patch.object(lz3.Conditional_z3, "translate_from_existing", return_value=_DummyQueryZ3()), patch.object(
            lz3, "makeOptimizer", return_value=_DummyOpt()
        ), patch.object(lz3.LexInfZ3, "_rec_inference", return_value=True) as rec:
            # query argument can be anything; translate_from_existing is patched
            res = s._inference(query=object(), weakly=False, deadline=None)
            self.assertTrue(res)
            self.assertTrue(rec.called)

    def test_rec_inference_debug_logs_xi_sets(self):
        """
        Covers lex_inf_z3.py lines 136-137 (debug logs):
          logger.debug("xi_i_set %s", xi_i_set)
          logger.debug("xi_i_prime_set %s", xi_i_prime_set)
        """
        s = self._make_system()
        fake_logger = _FakeLogger()

        # prepare a partition layer
        part = [_DummyConditionalZ3("c1"), _DummyConditionalZ3("c2")]
        s.epistemic_state["partition"] = [part]

        # make get_all_xi_i return non-empty sets so logs show meaningful values
        xi_i_set = {frozenset({part[0]})}
        xi_i_prime_set = {frozenset({part[1]})}

        call_no = {"n": 0}

        def _get_all_xi_i(_opt, _part):
            call_no["n"] += 1
            return xi_i_set if call_no["n"] == 1 else xi_i_prime_set

        with patch.object(lz3, "logger", fake_logger), patch.object(
            lz3.LexInfZ3, "get_all_xi_i", side_effect=_get_all_xi_i
        ):
            # choose partition_index=0 so part exists; query/opts are dummies
            res = s._rec_inference(_DummyOpt(), _DummyOpt(), partition_index=0, query=_DummyQueryZ3())
            self.assertIsInstance(res, bool)

        # verify both debug statements executed
        msgs = [m for (m, _a) in fake_logger.debug_calls]
        self.assertTrue(any(str(m).startswith("xi_i_set") for m in msgs))
        self.assertTrue(any(str(m).startswith("xi_i_prime_set") for m in msgs))

    def test_rec_inference_no_verification_mcs_returns_true(self):
        """
        Covers lex_inf_z3.py lines 142-143:
          logger.debug("no verification mcs"); return True
        """
        s = self._make_system()
        fake_logger = _FakeLogger()

        part = [_DummyConditionalZ3("c1")]
        s.epistemic_state["partition"] = [part]

        # xi_i_set non-empty -> avoid early "no falsification mcs" return False
        xi_i_set = {frozenset({part[0]})}
        xi_i_prime_set = set()  # triggers lines 142-143

        call_no = {"n": 0}

        def _get_all_xi_i(_opt, _part):
            call_no["n"] += 1
            return xi_i_set if call_no["n"] == 1 else xi_i_prime_set

        with patch.object(lz3, "logger", fake_logger), patch.object(
            lz3.LexInfZ3, "get_all_xi_i", side_effect=_get_all_xi_i
        ):
            res = s._rec_inference(_DummyOpt(), _DummyOpt(), partition_index=0, query=_DummyQueryZ3())
            self.assertTrue(res)

        self.assertTrue(any("no verification mcs" in str(m) for (m, _a) in fake_logger.debug_calls))

    def test_any_subset_of_all_line_228(self):
        """
        Covers lex_inf_z3.py line 228: any_subset_of_all return statement.
        """
        A = {frozenset({1}), frozenset({2})}
        B_true = {frozenset({1, 9}), frozenset({2, 8})}
        B_false = {frozenset({1, 9}), frozenset({5})}

        self.assertTrue(lz3.any_subset_of_all(A, B_true))
        self.assertFalse(lz3.any_subset_of_all(A, B_false))


if __name__ == "__main__":
    unittest.main()
