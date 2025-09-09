"""
PreOCF end-to-end tests.

Purpose
-------
Validate core functionality of the PreOCF implementation (System Z initialization,
rank computation, conditionalization, marginalization, TPO conversions, state
persistence, and solver integration) on both a large random belief base and a
small birds example.

Run
---
uv run --python 3.12 --extra testing pytest -q unittests/test_preocf.py
"""

import os
import random
import unittest

from pysmt.shortcuts import And, Not, Or, Solver, Symbol
from pysmt.typing import BOOL
from z3 import AstRef, Optimize

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.inference_operator import create_epistemic_state
from inference.preocf import PreOCF, ranks2tpo, tpo2ranks
from inference.system_z import SystemZ
from parser.Wrappers import parse_belief_base


class TestPreOCF(unittest.TestCase):
    """Tests for the PreOCF class and related functions."""

    @classmethod
    def setUpClass(cls):
        """Set up test environment with two belief bases - a large random one and a small birds one."""
        # Get the absolute path to the project root directory
        project_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        # Construct the path to the example file
        filepath = os.path.join(
            project_root, "examples", "random_large", "randomTest_10_10_0.cl"
        )

        # Verify the file exists before proceeding
        if not os.path.exists(filepath):
            raise FileNotFoundError(f"Test file not found at: {filepath}")

        # Load the large random belief base
        bb = parse_belief_base(filepath)

        # Create a small birds belief base for more targeted testing
        str_birds = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
        bb_birds = parse_belief_base(str_birds)

        # Configure solvers
        smt_solver = "z3"

        # Store belief bases for tests
        cls.belief_base = BeliefBase(
            bb.signature, bb.conditionals, "random_Test_10_10_0"
        )
        cls.belief_base_birds = BeliefBase(
            bb_birds.signature, bb_birds.conditionals, "birds"
        )

        # Create PreOCF instances
        cls.preocf_z = PreOCF.init_system_z(cls.belief_base)
        cls.preocf_z_birds = PreOCF.init_system_z(cls.belief_base_birds)

    def test_bitvec_world_ranks(self):
        """Test the creation of bitvector world dictionary and initial rank assignment."""
        ranks = self.preocf_z.ranks
        worlds = ranks.keys()
        # Verify we have the correct number of worlds (2^signature_size)
        assert len(worlds) == 2 ** len(self.preocf_z.signature)

        # Verify each world exists in the ranks and has None as initial rank
        for key in self.preocf_z.create_bitvec_world_dict(
            self.preocf_z.signature
        ).keys():
            assert key in worlds
            assert self.preocf_z.ranks[key] == None

    def test_signature_and_conditionals(self):
        """Test basic solver operations with signatures and conditionals."""
        signature = self.preocf_z.signature
        conditionals = self.preocf_z.conditionals

        # Test solver operations using push/pop
        solver = Solver(name="z3")
        sig_1 = Symbol(signature[0], BOOL)
        not_sig_1 = Not(sig_1)
        sig_7 = Symbol(signature[0], BOOL)

        # Add conditional and verify solvability
        solver.add_assertion(conditionals[1].make_A_then_B())
        solver.add_assertion(sig_7)
        assert solver.solve() == True

        # Test push/pop with additional constraint
        solver.push()
        solver.add_assertion(sig_1)
        assert solver.solve() == True
        solver.pop()

        # Test with negated constraint (should be unsatisfiable)
        solver.add_assertion(not_sig_1)
        assert solver.solve() == False

    def test_ranks_and_conditionalization(self):
        """Test conditionalization operations on the large random belief base."""
        # Test preocf_z with its own signature
        signature_symbols = [
            Symbol(s, BOOL) for s in self.preocf_z.signature[:8]
        ]  # Take first 8 symbols
        conditionalization_z = And(*signature_symbols)

        # Test specific worlds for preocf_z
        assert not self.preocf_z.world_satisfies_conditionalization(
            "1111111000", conditionalization_z
        )
        assert self.preocf_z.world_satisfies_conditionalization(
            "1111111100", conditionalization_z
        )
        assert self.preocf_z.is_ocf() == False
        assert len(self.preocf_z.ranks.keys()) == 1024

        # Test filtering worlds by conditionalization
        conditionalized_worlds = self.preocf_z.filter_worlds_by_conditionalization(
            conditionalization_z
        )
        assert len(conditionalized_worlds) == 4

        # Test computing ranks for conditionalized worlds
        self.preocf_z.compute_conditionalization(conditionalization_z)
        assert self.preocf_z.is_ocf() == False
        assert (
            len(
                {
                    key
                    for key in self.preocf_z.ranks.keys()
                    if self.preocf_z.ranks[key] != None
                }
            )
            == 4
        )

        # Test computing all ranks
        self.preocf_z.compute_all_ranks()
        assert self.preocf_z.is_ocf() == True

        # Test conditionalizing existing ranks
        conditionalized_dict = self.preocf_z.conditionalize_existing_ranks(
            conditionalization_z
        )
        assert len(conditionalized_dict.keys()) == 4
        assert list(conditionalized_dict.keys()) == conditionalized_worlds

    def test_birds_ranks_and_conditionalization(self):
        """Test conditionalization and rank operations on the birds belief base."""
        # Set up bird-specific symbols
        b = Symbol("b", BOOL)
        p = Symbol("p", BOOL)
        f = Symbol("f", BOOL)
        w = Symbol("w", BOOL)

        # Test world_satisfies_conditionalization for birds
        # Test simple cases
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", b
        )  # All true
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", b
        )  # All false
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", b
        )  # b and f true, p and w false

        # Test compound formulas
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", And(b, p)
        )  # Both true
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", And(b, p)
        )  # b true, p false
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "0101", And(b, p)
        )  # b false, p true

        # Test with negations
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", Not(And(b, p))
        )  # Both false
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", Not(And(b, p))
        )  # b true, p false
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "0101", Not(And(b, p))
        )  # b false, p true
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", Not(And(b, p))
        )  # Both true

        # Test with conjunction
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", And(b, p, f, w)
        )  # All true
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", And(b, p, f, w)
        )  # All false
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", And(b, p, f, w)
        )  # b and f true, p and w false

        # Test with OR operations
        # Simple OR
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", Or(b, p)
        )  # Both true
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", Or(b, p)
        )  # b true, p false
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "0101", Or(b, p)
        )  # b false, p true
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", Or(b, p)
        )  # Both false

        # OR with negation (De Morgan's law: !(b && p) = !b || !p)
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", Or(Not(b), Not(p))
        )  # Both true -> both negated false
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", Or(Not(b), Not(p))
        )  # b true, p false -> !p is true
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "0101", Or(Not(b), Not(p))
        )  # b false, p true -> !b is true
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", Or(Not(b), Not(p))
        )  # Both false -> both negated true

        # Complex OR with multiple symbols
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", Or(b, p, f, w)
        )  # All true
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", Or(b, p, f, w)
        )  # b and f true, p and w false
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "0101", Or(b, p, f, w)
        )  # b and f false, p and w true
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", Or(b, p, f, w)
        )  # All false

        # Mixed AND/OR
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1111", And(Or(b, p), Or(f, w))
        )  # All true
        assert self.preocf_z_birds.world_satisfies_conditionalization(
            "1010", And(Or(b, p), Or(f, w))
        )  # b and f true, p and w false
        assert not self.preocf_z_birds.world_satisfies_conditionalization(
            "0000", And(Or(b, p), Or(f, w))
        )  # All false

        # Test rank computations
        self.preocf_z_birds.compute_all_ranks()
        assert self.preocf_z_birds.ranks["1111"] == 2  # Verify specific world ranks
        assert self.preocf_z_birds.ranks["0000"] == 0
        assert self.preocf_z_birds.ranks["1011"] == 0
        assert self.preocf_z_birds.ranks["1001"] == 1

        # Test formula rank calculations
        assert (
            self.preocf_z_birds.formula_rank(And(Not(p), p)) == None
        )  # Contradictions should have no rank
        assert (
            self.preocf_z_birds.formula_rank(And(b, b)) == 0
        )  # Tautological with respect to b
        assert self.preocf_z_birds.formula_rank(And(p, p)) == 1  # Standard formula

        # Test conditional acceptance
        assert (
            self.preocf_z_birds.conditional_acceptance(Conditional(p, f, "(f|p)"))
            == False
        )

        # Test with specific conditional and verify ranks
        cond = Conditional(b, p, "(b|p)")
        verify = cond.make_A_then_B()
        falsify = cond.make_A_then_not_B()
        rv = self.preocf_z_birds.formula_rank(verify)
        rf = self.preocf_z_birds.formula_rank(falsify)
        assert rv == 1
        assert rf == 2
        assert (
            self.preocf_z_birds.conditional_acceptance(Conditional(b, w, "(w|b)"))
            == False
        )

        # Verify that PreOCF matches System Z on all possible conditionals

        # Create epistemic state dictionary for SystemZ
        epistemic_state = create_epistemic_state(
            self.belief_base_birds, "system-z", "z3", "", weakly=False
        )
        sys_z = SystemZ(epistemic_state)
        sys_z.preprocess_belief_base(0)  # Preprocess without timeout

        for antecedence in [b, p, f, w, Not(b), Not(p), Not(f), Not(w)]:
            for consequence in [b, p, f, w, Not(b), Not(p), Not(f), Not(w)]:
                conditional = Conditional(
                    consequence, antecedence, f"({consequence}|{antecedence})"
                )
                assert sys_z.general_inference(
                    conditional
                ) == self.preocf_z_birds.conditional_acceptance(conditional)

    def test_tpo(self):
        """Test total preorder conversions using the function-based tpo2ranks."""
        # First compute all ranks
        self.preocf_z_birds.compute_all_ranks()

        # Expected total preorder for the birds belief base
        tpo_in = [
            {"1011", "0011", "0010", "0001", "0000"},  # rank 0
            {"1101", "1100", "1010", "1001", "1000"},  # rank 1
            {"1111", "1110", "0111", "0110", "0101", "0100"},
        ]  # rank 2

        # Convert ranks to TPO and verify against expected
        tpo_out = ranks2tpo(self.preocf_z_birds.ranks)
        assert tpo_in == tpo_out

        # Test function-based ranking: complex calculation
        # Create layer differences and multiplier for testing
        layer_diffs = {i: random.randint(2, 20) for i in range(len(tpo_in))}
        multiplier = random.randint(2, 20)

        # Define a ranking function that reproduces the old behavior
        def rank_function(layer_num):
            if layer_num == 0:
                return 0
            else:
                return sum(layer_diffs[i] * multiplier for i in range(layer_num))

        # Test with function-based ranking
        ranks_new = tpo2ranks(tpo_in, rank_function)
        assert ranks_new != self.preocf_z_birds.ranks  # Different rank values
        assert tpo_in == tpo_out == ranks2tpo(ranks_new)  # Same TPO structure

        # Test with a simple linear function
        ranks_linear = tpo2ranks(tpo_in, lambda layer: layer * 10)
        assert tpo_in == ranks2tpo(ranks_linear)  # Structure preserved

    def test_ranks_verbose(self):
        """Test the ranks_verbose property which provides human-readable world descriptions."""
        # Compute all ranks first
        self.preocf_z_birds.compute_all_ranks()

        # Get the verbose ranks
        verbose_ranks = self.preocf_z_birds.ranks_verbose

        # Verify that the dictionary keys are properly formatted
        for world_desc in verbose_ranks.keys():
            # Each world description should be a tuple of strings representing variable assignments
            assert isinstance(world_desc, tuple)
            assert len(world_desc) == len(self.preocf_z_birds.signature)

            # Check format of each variable assignment
            for assignment in world_desc:
                # Each assignment should either be a variable name or its negation (!var)
                assert assignment in self.preocf_z_birds.signature or (
                    assignment.startswith("!")
                    and assignment[1:] in self.preocf_z_birds.signature
                )

        # Verify that values match the original ranks
        for bitvec_world, rank in self.preocf_z_birds.ranks.items():
            verbose_world = self.preocf_z_birds.bv2strtuple(bitvec_world)
            assert verbose_ranks[verbose_world] == rank

        # Test specific examples
        # For the birds KB, the signature is ['b', 'p', 'f', 'w']
        # Check a few specific worlds
        world_1111 = self.preocf_z_birds.bv2strtuple("1111")  # All variables true
        world_0000 = self.preocf_z_birds.bv2strtuple("0000")  # All variables false

        assert world_1111 == ("b", "p", "f", "w")
        assert world_0000 == ("!b", "!p", "!f", "!w")

        # Verify ranks match
        assert verbose_ranks[world_1111] == self.preocf_z_birds.ranks["1111"]
        assert verbose_ranks[world_0000] == self.preocf_z_birds.ranks["0000"]

    def test_init_random_min_c_rep_csp_z3_and_optimizer(self):
        """Test that init_random_min_c_rep converts CSP to z3 expressions and sets optimizer."""
        # Initialize with random_min_c_rep on birds belief base
        preocf_r = PreOCF.init_random_min_c_rep(self.belief_base_birds)
        # Optimizer should be present and of correct type
        assert hasattr(preocf_r, "_optimizer")
        assert isinstance(preocf_r._optimizer, Optimize)
        # CSP should be a non-empty list of Z3 ASTs
        assert isinstance(preocf_r._csp, list)
        assert len(preocf_r._csp) > 0
        for constraint in preocf_r._csp:
            assert isinstance(constraint, AstRef)
        # Verify optimizer assertions match the CSP constraints
        opt_assertions = preocf_r._optimizer.assertions()
        assert set(opt_assertions) == set(preocf_r._csp)

    def test_random_min_c_rep_ranking_and_acceptance(self):
        """Test compute_all_ranks and conditional_acceptance using c_rep."""
        # Initialize with random_min_c_rep on birds belief base
        preocf_c = PreOCF.init_random_min_c_rep(self.belief_base_birds)
        # Impacts list should be created and correct length
        assert hasattr(preocf_c, "_impacts")
        assert isinstance(preocf_c._impacts, list)
        assert len(preocf_c._impacts) == len(self.belief_base_birds.conditionals)
        for impact in preocf_c._impacts:
            assert isinstance(impact, int) and impact >= 0

        # Before computing ranks, is_ocf should be False
        assert not preocf_c.is_ocf()

        # Compute all ranks
        preocf_c.compute_all_ranks()

        # After computing, ranks should be non-negative ints and is_ocf True
        assert preocf_c.is_ocf()
        # Sample some world ranks
        assert isinstance(preocf_c.ranks["0000"], int)
        assert isinstance(preocf_c.ranks["1111"], int)

        # Test conditional acceptance for tautology
        b = Symbol("b", BOOL)
        cond_tauto = Conditional(b, b, "(b|b)")
        assert preocf_c.conditional_acceptance(cond_tauto)

        # Test conditional acceptance for contradiction
        p = Symbol("p", BOOL)
        cond_contra = Conditional(Not(p), p, "(!p|p)")
        assert not preocf_c.conditional_acceptance(cond_contra)


if __name__ == "__main__":
    unittest.main()
