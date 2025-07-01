import random
import unittest

import z3
from pysmt.shortcuts import Not, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.c_revision import c_revision
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF, PreOCF

# ---------------------------------------------------------------------------
# Helper – compute Pareto front of η vectors (adapted from the example script)
# ---------------------------------------------------------------------------


def compute_pareto_front(belief_base: BeliefBase):
    """Return the list of Pareto-optimal η-vectors for *belief_base*."""
    # RandomMinCRepPreOCF internally constructs the base CSP we need.
    preocf_c = PreOCF.init_random_min_c_rep(belief_base)

    eta_vars = [z3.Int(f"eta_{i}") for i in range(1, len(belief_base.conditionals) + 1)]

    opt = z3.Optimize()
    opt.set(priority="pareto")
    # Base constraints (already translated to native z3 expressions)
    opt.add(*preocf_c._csp)

    for v in eta_vars:
        opt.minimize(v)

    pareto_vectors = []
    while opt.check() == z3.sat:
        m = opt.model()
        vec = tuple(m[v].as_long() for v in eta_vars)
        pareto_vectors.append(vec)
        # Block current model strictly (improve at least one objective)
        opt.add(z3.Or(*[v < val for v, val in zip(eta_vars, vec, strict=False)]))

    return pareto_vectors


# ---------------------------------------------------------------------------
# Test case: γ⁻ (c-revision) must appear in η Pareto front (c-representation)
# ---------------------------------------------------------------------------


class TestCRevisionVsCRepresentation(unittest.TestCase):
    NUM_TRIALS = 100

    def _random_conditional(self, sig_vars: list[str], idx: int) -> Conditional:
        """Create a random Conditional over *sig_vars* with fixed index *idx*."""
        var_ante = random.choice(sig_vars)
        var_cons = random.choice([v for v in sig_vars if v != var_ante])
        ante = Symbol(var_ante, BOOL)
        cons = Symbol(var_cons, BOOL)
        # Randomly negate antecedence / consequence
        if random.random() < 0.5:
            ante = Not(ante)
        if random.random() < 0.5:
            cons = Not(cons)
        text_repr = f"({str(cons)}|{str(ante)})"
        cond = Conditional(cons, ante, text_repr)
        cond.index = idx
        return cond

    def test_gamma_minus_matches_eta(self):
        random.seed(42)
        sig_vars = ["a", "b", "c"]
        # Precompute all-zero ranking function for the signature once.
        all_zero_ranks = {
            format(i, f"0{len(sig_vars)}b"): 0 for i in range(2 ** len(sig_vars))
        }

        successes = 0
        attempts = 0
        max_attempts = self.NUM_TRIALS * 5  # give ourselves some slack

        while successes < self.NUM_TRIALS and attempts < max_attempts:
            attempts += 1

            # Generate 3 random conditionals
            conditionals = [self._random_conditional(sig_vars, i + 1) for i in range(3)]
            bb = BeliefBase(
                sig_vars, {c.index: c for c in conditionals}, f"rand_{attempts}"
            )

            # Custom PreOCF with all-zero ranks
            preocf = CustomPreOCF(all_zero_ranks, bb, sig_vars)

            # Run c-revision with γ⁺ fixed to 0
            model = c_revision(preocf, conditionals, gamma_plus_zero=True)
            if model is None:
                # No feasible γ vector – skip this KB instance
                continue

            gamma_minus_vec = tuple(model[f"gamma-_{i + 1}"] for i in range(3))

            # Compute Pareto front of η vectors (may raise if unsat)
            try:
                pareto_vecs = compute_pareto_front(bb)
            except ValueError:
                # No η vector – skip to next attempt
                continue

            if gamma_minus_vec in pareto_vecs:
                successes += 1
            else:
                self.fail(
                    f"Mismatch on attempt {attempts}: γ⁻ {gamma_minus_vec} not in η Pareto {pareto_vecs}"
                )

        self.assertEqual(
            successes,
            self.NUM_TRIALS,
            f"Only {successes} successful comparisons (expected {self.NUM_TRIALS}) after {attempts} attempts",
        )


if __name__ == "__main__":
    unittest.main()
