"""
Test file for the compile function in inference/preocf.py
"""

import unittest
import sys
import os

# Add the parent directory to the path so we can import the modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from inference.preocf import PreOCF
from inference.c_revision import compile
from inference.conditional import Conditional
from inference.belief_base import BeliefBase
from parser.Wrappers import parse_belief_base
from pysmt.shortcuts import Symbol, Not, And, Or
from pysmt.typing import BOOL


class TestCompileFunction(unittest.TestCase):
    """Test the compile function in preocf.py"""
    
    @classmethod
    def setUpClass(cls):
        """Set up test environment with a simple belief base."""
        # Create a simple birds belief base for testing
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
        
        # Create some revision conditionals for testing
        cls.revision_conditionals = [
            Conditional(cls.f, cls.p, '(f|p)'),  # penguins fly
            Conditional(Not(cls.w), cls.p, '(!w|p)')  # penguins don't have wings
        ]
        
        # Add index attributes to conditionals (required by compile function)
        for i, cond in enumerate(cls.revision_conditionals, 1):
            cond.index = i

    def test_compile_function_basic(self):
        """Test basic functionality of the compile function."""
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        
        # Check that result is a list
        self.assertIsInstance(result, list)
        
        # Check that we have one entry per revision conditional
        self.assertEqual(len(result), len(self.revision_conditionals))
        
        # Check structure: each entry should be a list with 2 dictionaries
        for entry in result:
            self.assertIsInstance(entry, list)
            self.assertEqual(len(entry), 2)
            self.assertIsInstance(entry[0], dict)
            self.assertIsInstance(entry[1], dict)

    def test_compile_function_world_coverage(self):
        """Test that relevant worlds are covered in the compile result."""
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        
        for i, rev_cond in enumerate(self.revision_conditionals):
            entry = result[i]
            
            # Collect all worlds from both dictionaries
            worlds_in_entry = set(entry[0].keys()) | set(entry[1].keys())
            
            # Check that each world in the entry satisfies either verification or falsification
            for world in worlds_in_entry:
                satisfies_verification = self.preocf_z_birds.world_satisfies_conditionalization(
                    world, rev_cond.make_A_then_B()
                )
                satisfies_falsification = self.preocf_z_birds.world_satisfies_conditionalization(
                    world, rev_cond.make_A_then_not_B()
                )
                # World should satisfy at least one condition
                self.assertTrue(satisfies_verification or satisfies_falsification)

    def test_compile_function_world_data_structure(self):
        """Test the data structure for each world in the compile result."""
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        
        for entry in result:
            for world_dict in entry:
                for world, data in world_dict.items():
                    # Each world should have a list with 3 elements
                    self.assertIsInstance(data, list)
                    self.assertEqual(len(data), 3)
                    
                    # First element should be an integer (rank)
                    self.assertIsInstance(data[0], int)
                    
                    # Second and third elements should be lists (accepted/rejected conditionals)
                    self.assertIsInstance(data[1], list)
                    self.assertIsInstance(data[2], list)

    def test_compile_function_conditional_indices(self):
        """Test that conditional indices are properly stored."""
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        
        # Get all conditional indices that should appear
        expected_indices = {cond.index for cond in self.revision_conditionals}
        
        for entry in result:
            for world_dict in entry:
                for world, data in world_dict.items():
                    accepted_indices = set(data[1])
                    rejected_indices = set(data[2])
                    
                    # All indices should be from our revision conditionals
                    self.assertTrue(accepted_indices.issubset(expected_indices))
                    self.assertTrue(rejected_indices.issubset(expected_indices))
                    
                    # No index should appear in both accepted and rejected
                    self.assertTrue(accepted_indices.isdisjoint(rejected_indices))

    def test_compile_function_empty_revision_conditionals(self):
        """Test compile function with empty revision conditionals list."""
        result = compile(self.preocf_z_birds, [])
        
        # Should return empty list
        self.assertEqual(result, [])

    def test_compile_function_single_conditional(self):
        """Test compile function with a single revision conditional."""
        single_conditional = [self.revision_conditionals[0]]
        result = compile(self.preocf_z_birds, single_conditional)
        
        # Should have one entry
        self.assertEqual(len(result), 1)
        
        # Check structure
        entry = result[0]
        self.assertEqual(len(entry), 2)
        
        # Check that worlds are properly categorized
        worlds_in_entry = set(entry[0].keys()) | set(entry[1].keys())
        rev_cond = single_conditional[0]
        
        for world in worlds_in_entry:
            satisfies_verification = self.preocf_z_birds.world_satisfies_conditionalization(
                world, rev_cond.make_A_then_B()
            )
            satisfies_falsification = self.preocf_z_birds.world_satisfies_conditionalization(
                world, rev_cond.make_A_then_not_B()
            )
            # World should satisfy at least one condition
            self.assertTrue(satisfies_verification or satisfies_falsification)

    def test_compile_function_world_satisfies_conditionalization(self):
        """Test that worlds are correctly categorized based on conditionalization."""
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        
        for i, rev_cond in enumerate(self.revision_conditionals):
            entry = result[i]
            
            # Check that worlds are correctly distributed between the two dictionaries
            for world in set(entry[0].keys()) | set(entry[1].keys()):
                satisfies_verification = self.preocf_z_birds.world_satisfies_conditionalization(
                    world, rev_cond.make_A_then_B()
                )
                satisfies_falsification = self.preocf_z_birds.world_satisfies_conditionalization(
                    world, rev_cond.make_A_then_not_B()
                )
                
                if satisfies_verification:
                    # World should be in verification dictionary (index 0)
                    self.assertIn(world, entry[0])
                if satisfies_falsification:
                    # World should be in falsification dictionary (index 1)  
                    self.assertIn(world, entry[1])

    def test_compile_function_ranks_consistency(self):
        """Test that ranks in compile result match the ranking function."""
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        
        for entry in result:
            for world_dict in entry:
                for world, data in world_dict.items():
                    expected_rank = self.preocf_z_birds.rank_world(world)
                    actual_rank = data[0]
                    self.assertEqual(actual_rank, expected_rank)

    def test_compile_function_with_custom_preocf(self):
        """Test compile function with a custom PreOCF."""
        # Create a simple custom ranking
        signature = ['a', 'b']
        custom_ranks = {
            '00': 0,
            '01': 1,
            '10': 2,
            '11': 0
        }
        
        custom_preocf = PreOCF.init_custom(custom_ranks, signature=signature)
        
        # Create simple revision conditionals
        a = Symbol('a', BOOL)
        b = Symbol('b', BOOL)
        rev_conds = [
            Conditional(a, b, '(a|b)'),
            Conditional(Not(a), b, '(!a|b)')
        ]
        
        # Add indices
        for i, cond in enumerate(rev_conds, 1):
            cond.index = i
        
        result = compile(custom_preocf, rev_conds)
        
        # Basic structure checks
        self.assertEqual(len(result), 2)
        for i, entry in enumerate(result):
            self.assertEqual(len(entry), 2)
            worlds_covered = set(entry[0].keys()) | set(entry[1].keys())
            
            # Check that covered worlds satisfy at least one condition for this revision conditional
            rev_cond = rev_conds[i]
            for world in worlds_covered:
                satisfies_verification = custom_preocf.world_satisfies_conditionalization(
                    world, rev_cond.make_A_then_B()
                )
                satisfies_falsification = custom_preocf.world_satisfies_conditionalization(
                    world, rev_cond.make_A_then_not_B()
                )
                self.assertTrue(satisfies_verification or satisfies_falsification)

    def test_compile_function_performance(self):
        """Test that compile function completes in reasonable time."""
        import time
        
        start_time = time.time()
        result = compile(self.preocf_z_birds, self.revision_conditionals)
        end_time = time.time()
        
        # Should complete in less than 5 seconds for this small example
        self.assertLess(end_time - start_time, 5.0)
        
        # Result should not be empty
        self.assertGreater(len(result), 0)

    def test_compile_function_deterministic(self):
        """Test that compile function produces deterministic results."""
        result1 = compile(self.preocf_z_birds, self.revision_conditionals)
        result2 = compile(self.preocf_z_birds, self.revision_conditionals)
        
        # Results should be identical
        self.assertEqual(len(result1), len(result2))
        
        for i in range(len(result1)):
            entry1 = result1[i]
            entry2 = result2[i]
            
            self.assertEqual(len(entry1), len(entry2))
            
            for j in range(len(entry1)):
                dict1 = entry1[j]
                dict2 = entry2[j]
                
                self.assertEqual(set(dict1.keys()), set(dict2.keys()))
                
                for world in dict1.keys():
                    self.assertEqual(dict1[world], dict2[world])


if __name__ == '__main__':
    unittest.main() 