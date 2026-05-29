"""Unit tests for ``inference.extended_c_rep``.

Covers

- Example 49 of Haldimann/Beierle/Kern-Isberner, KER 2024
  (= Example 3 of the NMR 2023 paper), which is the canonical sanity
  check for the ``J_Δ`` construction.
- The penguin belief base with a strict "penguins are birds"
  conditional (``static/kb_examples/kb_penguins_weakly.cl``),
  exercising the single-``Δ^∞``-conditional case with no triggered
  propagation.
- A strongly consistent belief base, where the extended construction
  must collapse to the classical one (``J_Δ = all indices``) without
  any solver calls.
- Detection of not-weakly-consistent belief bases.

Run:
    cd infocfweb2.0/InfOCF
    ../../venv/bin/python -m pytest -q unittests/test_extended_c_rep.py
"""

from __future__ import annotations

import os
import sys
import unittest

BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, BASE_DIR)

from inference.consistency_sat import consistency  # noqa: E402
from inference.extended_c_rep import (  # noqa: E402
    INFINITY,
    compute_j_delta,
    delta_infinity_indices,
    extended_c_inference_pareto_front,
    extended_c_revision_pareto_front,
)
from inference.preocf import RandomMinCRepPreOCF  # noqa: E402
from parser.Wrappers import parseCKB  # noqa: E402

EXAMPLE_49_CKB = """
signature
    a, b, c
conditionals
ex49{
    (Bottom | a),
    (!a | b),
    (b | c)
}
"""

PENGUINS_WEAKLY_CKB = """
signature
    b, f, p, w
conditionals
birds_weakly{
    (f | b),
    (!f | p),
    (Bottom | p, !b),
    (w | b)
}
"""

STRONGLY_CONSISTENT_CKB = """
signature
    b, f, p
conditionals
pf{
    (f | b),
    (!f | p),
    (b | p)
}
"""

NOT_WEAKLY_CONSISTENT_CKB = """
signature
    a
conditionals
bad{
    (Bottom | Top)
}
"""

# Δ = {(⊥|a)}: weakly consistent (the world a=F satisfies the material
# counterpart ¬a), but Δ^∞ = Δ so J_Δ = ∅ and every impact is ∞.
DELTA_INFINITY_EQUALS_DELTA_CKB = """
signature
    a
conditionals
strict_only{
    (Bottom | a)
}
"""


class ExampleFortyNineTest(unittest.TestCase):
    """Example 49 from KER 2024 / Example 3 from NMR 2023.

    ``Δ = {(⊥|a), (¬a|b), (b|c)}``; EZP(Δ) = ({(¬a|b), (b|c)}, {(⊥|a)}).
    The paper states:

        J_Δ = {3},  and for (¬a|b) "cannot be falsified without
        falsifying (⊥|a)".

    So index 1 is ``"strict"`` and index 2 is ``"triggered"``.
    """

    def setUp(self) -> None:
        self.bb = parseCKB(EXAMPLE_49_CKB)
        # Sanity-check the indexing convention the parser uses,
        # otherwise everything below is meaningless.
        self.assertEqual(list(self.bb.conditionals.keys()), [1, 2, 3])
        self.assertEqual(
            [c.textRepresentation for c in self.bb.conditionals.values()],
            ["(Bottom|a)", "(!a|b)", "(b|c)"],
        )
        self.partition, _ = consistency(self.bb, weakly=True)

    def test_delta_infinity_indices(self) -> None:
        self.assertEqual(
            delta_infinity_indices(self.bb, self.partition),
            {1},
            "Δ^∞ should be exactly the strict conditional (⊥|a) at index 1",
        )

    def test_j_delta_matches_paper(self) -> None:
        j_delta, infinity_set, reasons = compute_j_delta(self.bb, self.partition)
        self.assertEqual(j_delta, {3}, "only (b|c) keeps a finite η")
        self.assertEqual(infinity_set, {1, 2}, "both (⊥|a) and (¬a|b) are assigned η=∞")
        self.assertEqual(
            reasons,
            {1: "strict", 2: "triggered"},
            "index 1 is strict (in Δ^∞); "
            "index 2 is triggered (falsifying it forces Δ^∞)",
        )

    def test_coverage_and_disjointness(self) -> None:
        j_delta, infinity_set, _ = compute_j_delta(self.bb, self.partition)
        self.assertTrue(j_delta.isdisjoint(infinity_set))
        self.assertEqual(j_delta | infinity_set, set(self.bb.conditionals.keys()))


class PenguinsWeaklyTest(unittest.TestCase):
    """Weakly consistent penguin KB with a single strict conditional.

    Δ = {(f|b), (¬f|p), (⊥ | p∧¬b), (w|b)} over {b, f, p, w}.
    Expected EZP structure:
        Δ⁰ = {(f|b), (w|b)}
        Δ¹ = {(¬f|p)}
        Δ^∞ = {(⊥ | p∧¬b)}
    and no conditional outside Δ^∞ is "triggered": any of the
    non-strict ones can be falsified in a feasible world.
    """

    def setUp(self) -> None:
        self.bb = parseCKB(PENGUINS_WEAKLY_CKB)
        self.partition, _ = consistency(self.bb, weakly=True)

    def test_delta_infinity_is_strict_bird_rule(self) -> None:
        infty = delta_infinity_indices(self.bb, self.partition)
        self.assertEqual(len(infty), 1)
        (strict_idx,) = tuple(infty)
        self.assertEqual(
            self.bb.conditionals[strict_idx].textRepresentation,
            "(Bottom|p,!b)",
            "the strict 'penguins are birds' conditional should be the only "
            "element of Δ^∞",
        )

    def test_no_triggered_propagation(self) -> None:
        j_delta, infinity_set, reasons = compute_j_delta(self.bb, self.partition)
        strict = {i for i, r in reasons.items() if r == "strict"}
        triggered = {i for i, r in reasons.items() if r == "triggered"}
        self.assertEqual(len(strict), 1, "exactly one strict conditional")
        self.assertEqual(
            triggered, set(), "no conditional should be transitively triggered"
        )
        self.assertEqual(len(j_delta), len(self.bb.conditionals) - 1)
        self.assertEqual(j_delta | infinity_set, set(self.bb.conditionals.keys()))


class StronglyConsistentFastPathTest(unittest.TestCase):
    """For a strongly consistent BB the extended construction must
    collapse to the classical c-rep CSP: ``J_Δ = all indices``, no
    ``∞`` assignments, and no solver calls are needed."""

    def setUp(self) -> None:
        self.bb = parseCKB(STRONGLY_CONSISTENT_CKB)
        self.partition, _ = consistency(self.bb, weakly=True)

    def test_strong_consistency_empty_delta_infinity(self) -> None:
        self.assertEqual(len(self.partition[-1]), 0)
        self.assertEqual(delta_infinity_indices(self.bb, self.partition), set())

    def test_j_delta_is_full_index_set(self) -> None:
        j_delta, infinity_set, reasons = compute_j_delta(self.bb, self.partition)
        self.assertEqual(j_delta, set(self.bb.conditionals.keys()))
        self.assertEqual(infinity_set, set())
        self.assertEqual(reasons, {})


class NotWeaklyConsistentTest(unittest.TestCase):
    """A not-weakly-consistent BB makes CRS^ex_Σ(Δ) undefined
    (Prop. 41 / KER 2024).  ``consistency(..., weakly=True)`` signals
    this by returning ``False``; both helpers must reject that."""

    def test_consistency_returns_false(self) -> None:
        bb = parseCKB(NOT_WEAKLY_CONSISTENT_CKB)
        partition, _ = consistency(bb, weakly=True)
        self.assertIs(
            partition,
            False,
            "sanity: (⊥|⊤) makes Δ not weakly consistent, and "
            "consistency(..., weakly=True) signals this by returning False",
        )

    def test_delta_infinity_indices_raises(self) -> None:
        bb = parseCKB(NOT_WEAKLY_CONSISTENT_CKB)
        partition, _ = consistency(bb, weakly=True)
        with self.assertRaises(ValueError):
            delta_infinity_indices(bb, partition)

    def test_compute_j_delta_raises(self) -> None:
        bb = parseCKB(NOT_WEAKLY_CONSISTENT_CKB)
        partition, _ = consistency(bb, weakly=True)
        with self.assertRaises(ValueError):
            compute_j_delta(bb, partition)


class DeltaInfinityEqualsDeltaTest(unittest.TestCase):
    """Subtle edge case: Δ = {(⊥|a)} is weakly consistent (a=F works),
    but every conditional is strict, so Δ^∞ = Δ, J_Δ = ∅, and every
    impact ends up at ∞.

    This is the case where Prop. 16(2) holds with ``A_1 ∨ ... ∨ A_n ≢ ⊤``
    (here ``a ≢ ⊤``) but ``Δ^∞ = Δ`` nonetheless.  Distinguishing it
    from the genuinely inconsistent case is exactly what weak
    consistency is about — and ``compute_j_delta`` must not raise here.
    """

    def setUp(self) -> None:
        self.bb = parseCKB(DELTA_INFINITY_EQUALS_DELTA_CKB)
        self.partition, _ = consistency(self.bb, weakly=True)

    def test_weakly_consistent_but_all_strict(self) -> None:
        # Must NOT be the False sentinel: the BB is weakly consistent.
        self.assertIsInstance(self.partition, list)
        # And the single conditional ends up in Δ^∞.
        self.assertEqual(
            delta_infinity_indices(self.bb, self.partition),
            set(self.bb.conditionals.keys()),
        )

    def test_j_delta_empty(self) -> None:
        j_delta, infinity_set, reasons = compute_j_delta(self.bb, self.partition)
        self.assertEqual(j_delta, set())
        self.assertEqual(infinity_set, set(self.bb.conditionals.keys()))
        self.assertEqual(reasons, dict.fromkeys(self.bb.conditionals, "strict"))


class ExtendedParetoFrontTest(unittest.TestCase):
    """End-to-end Pareto-front enumeration via both extended backends.

    Uses ``max_solutions=5`` as a belt-and-braces cap; for all test
    inputs the actual front has exactly one element, but the cap
    guarantees the test cannot hang if an upstream z3 Pareto quirk
    regresses.
    """

    MAX = 5

    def _both_backends(self, bb):
        inf = extended_c_inference_pareto_front(bb, max_solutions=self.MAX)
        rev = extended_c_revision_pareto_front(bb, max_solutions=self.MAX)
        return inf, rev

    def test_example_49_matches_paper(self) -> None:
        bb = parseCKB(EXAMPLE_49_CKB)
        inf, rev = self._both_backends(bb)
        # KER 2024 Example 49 states J_Δ = {3}, η_3 > 0, and η_1 = η_2 = ∞.
        # The Pareto-minimal finite impact for the single free variable is 1.
        expected = [(INFINITY, INFINITY, 1)]
        self.assertEqual(inf, expected)
        self.assertEqual(rev, expected)

    def test_strongly_consistent_regression(self) -> None:
        bb = parseCKB(STRONGLY_CONSISTENT_CKB)
        inf, rev = self._both_backends(bb)
        # A strongly consistent BB: no ∞ entries, and the two
        # backends must agree (they do in the classical path too).
        self.assertEqual(len(inf), 1)
        self.assertEqual(inf, rev)
        (vec,) = inf
        self.assertTrue(all(isinstance(x, int) for x in vec))
        self.assertTrue(all(x >= 0 for x in vec))

    def test_penguins_weakly(self) -> None:
        bb = parseCKB(PENGUINS_WEAKLY_CKB)
        inf, rev = self._both_backends(bb)
        self.assertEqual(inf, rev)
        self.assertEqual(len(inf), 1)
        (vec,) = inf
        # Indexing: 1=(f|b), 2=(!f|p), 3=(Bottom|p,!b), 4=(w|b).
        # The strict bird-from-penguin rule is (⊥|p,!b) at index 3.
        self.assertEqual(vec[2], INFINITY, "index 3 is strict → η=∞")
        self.assertTrue(isinstance(vec[0], int) and vec[0] > 0)
        self.assertTrue(isinstance(vec[1], int) and vec[1] > 0)
        self.assertTrue(isinstance(vec[3], int) and vec[3] > 0)

    def test_delta_infinity_equals_delta(self) -> None:
        bb = parseCKB(DELTA_INFINITY_EQUALS_DELTA_CKB)
        inf, rev = self._both_backends(bb)
        # J_Δ = ∅: the unique extended c-representation is η = (∞,...,∞).
        expected = [(INFINITY,)]
        self.assertEqual(inf, expected)
        self.assertEqual(rev, expected)

    def test_not_weakly_consistent_raises(self) -> None:
        bb = parseCKB(NOT_WEAKLY_CONSISTENT_CKB)
        with self.assertRaises(ValueError):
            extended_c_inference_pareto_front(bb)
        with self.assertRaises(ValueError):
            extended_c_revision_pareto_front(bb)


class InducedOcfInfinityPropagationTest(unittest.TestCase):
    """``RandomMinCRepPreOCF.c_vec2ocf`` must propagate ``INFINITY``
    whenever the world falsifies a conditional with infinite impact.

    This is the link between the extended impact vector and the
    induced ranking function ``κ_η`` (Def. 20 / Def. 6) — the piece
    that Phase 3 needs to render induced OCFs for weakly consistent
    belief bases in the web UI.
    """

    def test_penguins_weakly_infeasible_worlds(self) -> None:
        bb = parseCKB(PENGUINS_WEAKLY_CKB)
        (vec,) = extended_c_inference_pareto_front(bb, max_solutions=1)
        preocf = RandomMinCRepPreOCF.init_with_impacts_list(bb, list(vec))
        # Signature order as parsed: b, f, p, w
        self.assertEqual(bb.signature, ["b", "f", "p", "w"])
        # (⊥ | p∧¬b) is falsified iff p ∧ ¬b.  Worlds with p=T and b=F
        # must get rank ∞; all others must be finite (the c-rep exists).
        infinite_worlds: list[str] = []
        finite_worlds: list[str] = []
        for b in (0, 1):
            for f in (0, 1):
                for p in (0, 1):
                    for w in (0, 1):
                        world = f"{b}{f}{p}{w}"
                        r = preocf.rank_world(world, force_calculation=True)
                        falsifies_strict = p == 1 and b == 0
                        if falsifies_strict:
                            infinite_worlds.append(world)
                            self.assertEqual(
                                r,
                                INFINITY,
                                f"world {world} falsifies the strict "
                                f"rule but got rank {r}",
                            )
                        else:
                            finite_worlds.append(world)
                            self.assertNotEqual(
                                r,
                                INFINITY,
                                f"world {world} should be feasible but got rank ∞",
                            )
                            self.assertIsInstance(r, int)
        self.assertEqual(len(infinite_worlds), 4)
        self.assertEqual(len(finite_worlds), 12)

    def test_strict_only_everywhere_infinite(self) -> None:
        bb = parseCKB(DELTA_INFINITY_EQUALS_DELTA_CKB)
        (vec,) = extended_c_inference_pareto_front(bb, max_solutions=1)
        preocf = RandomMinCRepPreOCF.init_with_impacts_list(bb, list(vec))
        # Worlds with a=T falsify (⊥|a) and must be ∞; a=F does not
        # falsify any conditional so its rank is 0.
        self.assertEqual(preocf.rank_world("1", force_calculation=True), INFINITY)
        self.assertEqual(preocf.rank_world("0", force_calculation=True), 0)

    def test_load_impacts_accepts_infinity(self) -> None:
        bb = parseCKB(PENGUINS_WEAKLY_CKB)
        preocf = RandomMinCRepPreOCF.init_with_impacts_list(bb, [1, 2, INFINITY, 1])
        self.assertEqual(preocf.save_impacts(), [1, 2, INFINITY, 1])

    def test_load_impacts_rejects_negative_finite(self) -> None:
        bb = parseCKB(PENGUINS_WEAKLY_CKB)
        with self.assertRaises(ValueError):
            RandomMinCRepPreOCF.init_with_impacts_list(bb, [1, -1, INFINITY, 1])

    def test_load_impacts_rejects_non_numeric(self) -> None:
        bb = parseCKB(PENGUINS_WEAKLY_CKB)
        with self.assertRaises(TypeError):
            RandomMinCRepPreOCF.init_with_impacts_list(
                bb,
                [1, "oops", INFINITY, 1],  # type: ignore[list-item]
            )


class InfinitySentinelTest(unittest.TestCase):
    """Sanity checks for the ``INFINITY`` constant.  These are cheap
    but would fail loudly if someone ever replaced ``math.inf`` with
    a custom object that does not preserve arithmetic / comparison
    semantics."""

    def test_is_greater_than_any_int(self) -> None:
        self.assertTrue(INFINITY > 10**6)
        self.assertTrue(INFINITY > 0)
        self.assertFalse(INFINITY < INFINITY)
        self.assertTrue(INFINITY == INFINITY)

    def test_arithmetic_with_int_stays_infinite(self) -> None:
        # c_vec2ocf relies on ``sum([int, ..., INFINITY, ...])`` producing
        # INFINITY; make sure the sentinel has that property.
        self.assertEqual(1 + INFINITY, INFINITY)
        self.assertEqual(INFINITY + 1, INFINITY)
        self.assertEqual(sum([1, 2, INFINITY, 3]), INFINITY)


if __name__ == "__main__":
    unittest.main()
