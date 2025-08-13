import unittest

from pysmt.shortcuts import Not, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.c_revision import c_revision
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF


class TestCRevisionFixedGamma(unittest.TestCase):
    def setUp(self):
        # Simple signature and all-zero ranks
        self.sig = ["a", "b"]
        self.all_zero_ranks = {
            format(i, f"0{len(self.sig)}b"): 0 for i in range(2 ** len(self.sig))
        }

        # Build a small belief base for completeness (not strictly required by c_revision)
        # Two simple conditionals over existing signature
        a = Symbol("a", BOOL)
        b = Symbol("b", BOOL)

        self.cond1 = Conditional(a, b, "(a|b)")
        self.cond1.index = 1
        self.cond2 = Conditional(Not(a), b, "(!a|b)")
        self.cond2.index = 2

        self.revision_conditionals = [self.cond1, self.cond2]

        # Ranking function with constant zero rank
        # Provide signature explicitly so world satisfaction works
        self.preocf = CustomPreOCF(self.all_zero_ranks, signature=self.sig)

        # Belief base (unused directly by c_revision, but kept for parity)
        self.bb = BeliefBase(self.sig, {1: self.cond1, 2: self.cond2}, "toy")

    def test_fixed_gamma_minus_single_index(self):
        fixed = {1: 2}
        model = c_revision(
            self.preocf,
            self.revision_conditionals,
            gamma_plus_zero=True,
            fixed_gamma_minus=fixed,
        )

        # The model should include the fixed gamma- value for index 1
        self.assertIn("gamma-_1", model)
        self.assertEqual(model["gamma-_1"], 2)

        # The other gamma- should still be present and non-negative
        self.assertIn("gamma-_2", model)
        self.assertGreaterEqual(model["gamma-_2"], 0)

    def test_fixed_gamma_minus_multiple_indices(self):
        # Extend with a third conditional
        a = Symbol("a", BOOL)
        b = Symbol("b", BOOL)
        cond3 = Conditional(b, Not(a), "(b|!a)")
        cond3.index = 3
        conds = [self.cond1, self.cond2, cond3]

        fixed = {1: 1, 3: 4}
        model = c_revision(
            self.preocf,
            conds,
            gamma_plus_zero=True,
            fixed_gamma_minus=fixed,
        )

        # Fixed entries must be present with exact values
        self.assertIn("gamma-_1", model)
        self.assertIn("gamma-_3", model)
        self.assertEqual(model["gamma-_1"], 1)
        self.assertEqual(model["gamma-_3"], 4)

        # Unfixed entries must still exist and be non-negative
        self.assertIn("gamma-_2", model)
        self.assertGreaterEqual(model["gamma-_2"], 0)


if __name__ == "__main__":
    unittest.main()
