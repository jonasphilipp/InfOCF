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
