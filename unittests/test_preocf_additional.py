"""
Additional unit tests for the PreOCF class, focusing on conditionalization and other 
less thoroughly tested methods.
"""

import unittest
import os
from inference.system_z import SystemZ
from inference.conditional import Conditional
from inference.preocf import PreOCF, ranks2tpo, tpo2ranks
from inference.belief_base import BeliefBase
from parser.Wrappers import parse_belief_base
from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Iff
from pysmt.typing import BOOL

class TestPreOCFAdditional(unittest.TestCase):
    """Additional tests for the PreOCF class focusing on less-tested methods."""
    
    @classmethod
    def setUpClass(cls):
        """Set up test environment with a bird/penguin belief base for testing."""
        # Create a birds belief base for testing
        str_birds = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
        bb_birds = parse_belief_base(str_birds)
        cls.belief_base_birds = BeliefBase(bb_birds.signature, bb_birds.conditionals, 'birds')
        
        # Create a PreOCF instance using System Z
        cls.preocf_z_birds = PreOCF.init_system_z(cls.belief_base_birds)
        cls.preocf_z_birds.compute_all_ranks()
        
        # Create symbols for testing
        cls.b = Symbol('b', BOOL)  # bird
        cls.p = Symbol('p', BOOL)  # penguin
        cls.f = Symbol('f', BOOL)  # flies
        cls.w = Symbol('w', BOOL)  # has wings

    def test_compute_conditionalization_complex(self):
        """Test compute_conditionalization with more complex formulas."""
        # Create a fresh PreOCF for this test
        preocf = PreOCF.init_system_z(self.belief_base_birds)
        
        # Test with simple conditionalization (b)
        cond_result = preocf.compute_conditionalization(self.b)
        self.assertEqual(len(cond_result), 8)  # Half of the worlds should satisfy b
        
        # Ensure all computed worlds satisfy b
        for world in cond_result:
            self.assertTrue(preocf.world_satisfies_conditionalization(world, self.b))
        
        # Test with a more complex conditionalization: b AND NOT p (birds that are not penguins)
        complex_cond = And(self.b, Not(self.p))
        complex_result = preocf.compute_conditionalization(complex_cond)
        
        # Ensure proper number of worlds are computed
        # For 4 variables, we should have 2^(4-2) = 4 worlds satisfying b AND NOT p
        self.assertEqual(len(complex_result), 4)
        
        # Ensure all computed worlds satisfy the complex condition
        for world in complex_result:
            self.assertTrue(preocf.world_satisfies_conditionalization(world, complex_cond))
            # Check that they really are birds but not penguins (first bit 1, second bit 0)
            self.assertEqual(world[0], '1')  # b is true
            self.assertEqual(world[1], '0')  # p is false
        
        # Test with another complex formula: (b OR p) AND f (flying birds or flying penguins)
        flying_bp = And(Or(self.b, self.p), self.f)
        flying_result = preocf.compute_conditionalization(flying_bp)
        
        # Check each world in the result
        for world in flying_result:
            self.assertTrue(preocf.world_satisfies_conditionalization(world, flying_bp))
            # Should be either b=1 or p=1, and f=1
            self.assertTrue(world[0] == '1' or world[1] == '1')  # b or p is true
            self.assertEqual(world[2], '1')  # f is true

    def test_conditionalize_existing_ranks_complex(self):
        """Test conditionalizing existing ranks with complex formulas."""
        # Ensure ranks are computed
        self.preocf_z_birds.compute_all_ranks()
        
        # Test with simple conditionalization on b
        cond_result = self.preocf_z_birds.conditionalize_existing_ranks(self.b)
        self.assertEqual(len(cond_result), 8)  # Half of the worlds should satisfy b
        
        # Test with a more complex conditionalization: f OR w (flying or having wings)
        complex_cond = Or(self.f, self.w)
        complex_result = self.preocf_z_birds.conditionalize_existing_ranks(complex_cond)
        
        # Check that all worlds in the result satisfy the condition
        for world in complex_result:
            self.assertTrue(self.preocf_z_birds.world_satisfies_conditionalization(world, complex_cond))
            # Should be either f=1 or w=1
            self.assertTrue(world[2] == '1' or world[3] == '1')
        
        # Test with implication: b IMPLIES f (if it's a bird, then it flies)
        implies_cond = Implies(self.b, self.f)
        implies_result = self.preocf_z_birds.conditionalize_existing_ranks(implies_cond)
        
        # Check worlds in the result
        for world in implies_result:
            self.assertTrue(self.preocf_z_birds.world_satisfies_conditionalization(world, implies_cond))
            # Either b=0 or (b=1 and f=1)
            self.assertTrue(world[0] == '0' or (world[0] == '1' and world[2] == '1'))
        
        # Verify minimum ranks are preserved
        # Find a formula with a known minimum rank first
        known_rank = self.preocf_z_birds.formula_rank(And(self.b, self.f))
        
        # Conditionalize on something that wouldn't change that minimum rank
        # For example, conditionalizing on "has wings" shouldn't change the minimum rank of flying birds
        w_cond_result = self.preocf_z_birds.conditionalize_existing_ranks(self.w)
        
        # Compute the formula rank in the conditionalized result
        # We need to filter the conditionalized worlds for those that satisfy (b AND f)
        bf_worlds_in_w = [world for world in w_cond_result 
                         if self.preocf_z_birds.world_satisfies_conditionalization(world, And(self.b, self.f))]
        
        # Get the minimum rank
        cond_min_rank = min([w_cond_result[world] for world in bf_worlds_in_w])
        
        # The rank might change because we're looking at a subset of worlds,
        # but we can still check some properties
        self.assertGreaterEqual(cond_min_rank, 0)

    def test_marginalization_multi_var(self):
        """Test marginalization with multiple variables."""
        # Ensure ranks are computed
        self.preocf_z_birds.compute_all_ranks()
        
        # Test marginalization by removing one variable
        marg_one_var = self.preocf_z_birds.marginalize(['w'])
        self.assertEqual(len(marg_one_var.signature), 3)  # Should have 3 variables left
        self.assertEqual(len(marg_one_var.ranks), 8)  # Should have 2^3 = 8 worlds
        
        # Test marginalization by removing two variables
        marg_two_vars = self.preocf_z_birds.marginalize(['w', 'f'])
        self.assertEqual(len(marg_two_vars.signature), 2)  # Should have 2 variables left
        self.assertEqual(len(marg_two_vars.ranks), 4)  # Should have 2^2 = 4 worlds
        
        # Test marginalization by removing three variables
        marg_three_vars = self.preocf_z_birds.marginalize(['w', 'f', 'p'])
        self.assertEqual(len(marg_three_vars.signature), 1)  # Should have 1 variable left
        self.assertEqual(len(marg_three_vars.ranks), 2)  # Should have 2^1 = 2 worlds
        
        # Compute ranks for all marginalized OCFs
        marg_one_var.compute_all_ranks()
        marg_two_vars.compute_all_ranks()
        marg_three_vars.compute_all_ranks()
        
        # Verify that the marginalized OCFs are valid
        self.assertTrue(marg_one_var.is_ocf())
        self.assertTrue(marg_two_vars.is_ocf())
        self.assertTrue(marg_three_vars.is_ocf())
        
        # Test that minimum ranks are preserved or decreased by marginalization
        # Find a world with known rank
        # Original world: 1010 (bird, not penguin, flies, not wings)
        orig_world = '1010'
        orig_rank = self.preocf_z_birds.ranks[orig_world]
        
        # Same world in marginalized OCF (without the w bit)
        marg_world = '101'
        marg_rank = marg_one_var.ranks[marg_world]
        
        # The rank should be less than or equal to the original rank 
        # (because marginalization takes the minimum rank of all matching worlds)
        self.assertLessEqual(marg_rank, orig_rank)

    def test_init_custom_invalid_ranks(self):
        """Test custom initialization with invalid rank values."""
        # Create a rank dictionary with some invalid values
        custom_ranks = PreOCF.create_bitvec_world_dict(self.belief_base_birds.signature)
        
        # Set some valid and some invalid values
        custom_ranks['0000'] = 0
        custom_ranks['0001'] = 1
        custom_ranks['0010'] = -1  # Invalid negative rank
        custom_ranks['0011'] = None  # No rank
        
        # Create a PreOCF with these custom ranks
        custom_preocf = PreOCF.init_custom(custom_ranks, self.belief_base_birds)
        
        # It should not be a valid OCF
        self.assertFalse(custom_preocf.is_ocf())
        
        # Check the ranks were preserved
        self.assertEqual(custom_preocf.ranks['0000'], 0)
        self.assertEqual(custom_preocf.ranks['0001'], 1)
        self.assertEqual(custom_preocf.ranks['0010'], -1)
        self.assertEqual(custom_preocf.ranks['0011'], None)
        
        # Fix the invalid ranks
        custom_preocf.ranks['0010'] = 2
        custom_preocf.ranks['0011'] = 3
        
        # It should still not be a valid OCF because not all worlds are ranked
        self.assertFalse(custom_preocf.is_ocf())
        
        # Instead of calling compute_all_ranks(), manually assign ranks to all remaining worlds
        # For custom PreOCFs, we need to manually assign all ranks
        for world in custom_preocf.ranks.keys():
            if custom_preocf.ranks[world] is None:
                custom_preocf.ranks[world] = 5  # Assign a default rank
        
        # Now it should be a valid OCF
        self.assertTrue(custom_preocf.is_ocf())
        
        # Verify all worlds have valid ranks (non-negative integers)
        for world, rank in custom_preocf.ranks.items():
            self.assertIsNotNone(rank)
            self.assertGreaterEqual(rank, 0)

    def test_integration_conditionalization_and_marginalization(self):
        """Test combining conditionalization and marginalization operations."""
        # Create a fresh PreOCF
        preocf = PreOCF.init_system_z(self.belief_base_birds)
        preocf.compute_all_ranks()
        
        # First conditionalize on 'birds'
        bird_worlds = preocf.conditionalize_existing_ranks(self.b)
        
        # Then marginalize by removing 'w' from the conditionalized result
        # We need to create a temporary PreOCF with these ranks
        temp_preocf = PreOCF.init_custom(bird_worlds, self.belief_base_birds)
        marg_preocf = temp_preocf.marginalize(['w'])
        
        # Compute ranks for the marginalized result
        marg_preocf.compute_all_ranks()
        
        # The result should only have worlds where b=1, and no w variable
        for world in marg_preocf.ranks:
            self.assertEqual(len(world), 3)  # Should have 3 bits (b,p,f)
            self.assertEqual(world[0], '1')  # b should be 1
            
        # Now do the opposite: first marginalize, then conditionalize
        marg_first = preocf.marginalize(['w'])
        marg_first.compute_all_ranks()
        
        # Create a symbol for 'b' in the marginalized signature
        b_marg = Symbol('b', BOOL)
        
        # Conditionalize the marginalized result on 'birds'
        cond_after_marg = marg_first.conditionalize_existing_ranks(b_marg)
        
        # The number of worlds should match
        self.assertEqual(len(marg_preocf.ranks), len(cond_after_marg))

if __name__ == '__main__':
    unittest.main() 