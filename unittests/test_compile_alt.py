import unittest
from unittest.mock import Mock, MagicMock
from itertools import cycle
import sys
import os

# Add the project root to the path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from inference.preocf import compile_alt, PreOCF
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, And, Not, BOOL


class TestCompileAlt(unittest.TestCase):
    
    def setUp(self):
        """Set up test fixtures with mock PreOCF and Conditional objects."""
        # Create mock conditionals
        self.mock_conditional_1 = Mock(spec=Conditional)
        self.mock_conditional_1.index = 1
        self.mock_conditional_1.make_A_then_not_B.return_value = Mock()
        
        self.mock_conditional_2 = Mock(spec=Conditional)
        self.mock_conditional_2.index = 2
        self.mock_conditional_2.make_A_then_not_B.return_value = Mock()
        
        self.revision_conditionals = [self.mock_conditional_1, self.mock_conditional_2]
        
        # Create mock ranking function
        self.mock_ranking_function = Mock(spec=PreOCF)
        self.mock_ranking_function.ranks = {'00': 0, '01': 1, '10': 2, '11': 1}
        
    def test_compile_alt_basic_functionality(self):
        """Test basic functionality of compile_alt with simple inputs."""
        # Configure mock behavior - use cycle to provide infinite repetition
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Verify return types
        self.assertIsInstance(vMin, dict)
        self.assertIsInstance(fMin, dict)
        
        # Note: compile_alt stores only the last world for each conditional,
        # so the number of entries may be less than the number of conditionals
        self.assertLessEqual(len(vMin), len(self.revision_conditionals))
        self.assertLessEqual(len(fMin), len(self.revision_conditionals))
    
    def test_compile_alt_world_satisfaction_logic(self):
        """Test that worlds are correctly assigned to vMin or fMin based on satisfaction."""
        # Setup: world satisfaction pattern
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True])
        
        # Test with single conditional
        vMin, fMin = compile_alt(self.mock_ranking_function, [self.mock_conditional_1])
        
        # At least one should have an entry for index 0
        has_vmin_entry = 0 in vMin and vMin[0] is not None
        has_fmin_entry = 0 in fMin and fMin[0] is not None
        self.assertTrue(has_vmin_entry or has_fmin_entry)
    
    def test_compile_alt_conditional_acceptance_logic(self):
        """Test that conditional acceptance correctly populates triple[1] and triple[2]."""
        # Setup: alternating acceptance pattern
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True])
        self.mock_ranking_function.rank_world.side_effect = cycle([0])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Check that conditional_acceptance was called
        self.assertTrue(self.mock_ranking_function.conditional_acceptance.called)
        
        # Check structure of any result that exists
        for result_dict in [vMin, fMin]:
            for key, value in result_dict.items():
                if value is not None and isinstance(value, list) and len(value) == 3:
                    rank, accepted, rejected = value
                    self.assertIsInstance(rank, int)
                    self.assertIsInstance(accepted, list)
                    self.assertIsInstance(rejected, list)
    
    def test_compile_alt_empty_revision_conditionals(self):
        """Test behavior with empty revision conditionals list."""
        vMin, fMin = compile_alt(self.mock_ranking_function, [])
        
        self.assertEqual(len(vMin), 0)
        self.assertEqual(len(fMin), 0)
        self.assertIsInstance(vMin, dict)
        self.assertIsInstance(fMin, dict)
    
    def test_compile_alt_empty_worlds(self):
        """Test behavior when ranking function has no worlds."""
        
        # Setup mock with no worlds
        self.mock_ranking_function.ranks = {}
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = []
        self.mock_ranking_function.rank_world.side_effect = []
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # With the new implementation, entries are created for each conditional even with no worlds
        self.assertEqual(len(vMin), len(self.revision_conditionals))
        self.assertEqual(len(fMin), len(self.revision_conditionals))
        
        # But the lists should be empty since no worlds were processed
        for i in range(len(self.revision_conditionals)):
            self.assertIn(i, vMin)
            self.assertIn(i, fMin)
            self.assertEqual(len(vMin[i]), 0)  # Empty list
            self.assertEqual(len(fMin[i]), 0)  # Empty list
    
    def test_compile_alt_single_conditional(self):
        """Test with a single revision conditional."""
        single_conditional = [self.mock_conditional_1]
        
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, single_conditional)
        
        # Should have at most one entry (for index 0)
        self.assertLessEqual(len(vMin), 1)
        self.assertLessEqual(len(fMin), 1)
        
        # At least one should have an entry
        total_entries = len(vMin) + len(fMin)
        self.assertGreater(total_entries, 0)
    
    def test_compile_alt_multiple_conditionals(self):
        """Test with multiple revision conditionals."""
        # Add a third conditional
        mock_conditional_3 = Mock(spec=Conditional)
        mock_conditional_3.index = 3
        mock_conditional_3.make_A_then_not_B.return_value = Mock()
        
        multiple_conditionals = [self.mock_conditional_1, self.mock_conditional_2, mock_conditional_3]
        
        # Setup alternating pattern for world satisfaction
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False, True])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, multiple_conditionals)
        
        # Should have at most as many entries as conditionals
        self.assertLessEqual(len(vMin), 3)
        self.assertLessEqual(len(fMin), 3)
        
        # Should have some entries
        total_entries = len(vMin) + len(fMin)
        self.assertGreater(total_entries, 0)
    
    def test_compile_alt_triple_structure(self):
        """Test that the triple structure [rank, accepted_indices, rejected_indices] is correct."""
        # Setup predictable behavior
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True])
        self.mock_ranking_function.rank_world.side_effect = cycle([5])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Check structure of any stored data
        for result_dict in [vMin, fMin]:
            for key, value in result_dict.items():
                if value is not None and isinstance(value, list) and len(value) == 3:
                    rank, accepted, rejected = value
                    self.assertEqual(rank, 5)  # Expected rank
                    self.assertIsInstance(accepted, list)
                    self.assertIsInstance(rejected, list)
                    # Should have conditional indices based on acceptance pattern
                    self.assertTrue(len(accepted) > 0 or len(rejected) > 0)
    
    def test_compile_alt_deterministic_output(self):
        """Test that compile_alt produces deterministic output for same inputs."""
        # Setup consistent mock behavior using cycle for repeatability
        world_pattern = cycle([True, False])
        rank_pattern = cycle([0, 1, 2, 1])
        acceptance_pattern = cycle([True, False])
        
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = world_pattern
        self.mock_ranking_function.rank_world.side_effect = rank_pattern
        self.mock_ranking_function.conditional_acceptance.side_effect = acceptance_pattern
        
        # Run twice with same inputs
        vMin1, fMin1 = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Reset mock (cycles will continue from where they left off)
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        vMin2, fMin2 = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Results should have same structure (keys)
        self.assertEqual(set(vMin1.keys()), set(vMin2.keys()))
        self.assertEqual(set(fMin1.keys()), set(fMin2.keys()))
    
    def test_compile_alt_method_calls(self):
        """Test that all necessary methods are called with correct parameters."""
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True])
        self.mock_ranking_function.rank_world.side_effect = cycle([0])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Verify methods were called
        self.assertTrue(self.mock_ranking_function.world_satisfies_conditionalization.called)
        self.assertTrue(self.mock_ranking_function.rank_world.called)
        self.assertTrue(self.mock_ranking_function.conditional_acceptance.called)
        
        # Verify make_A_then_not_B was called on conditionals
        self.mock_conditional_1.make_A_then_not_B.assert_called()
        self.mock_conditional_2.make_A_then_not_B.assert_called()
    
    def test_compile_alt_single_world(self):
        """Test with a single world in the ranking function."""
        
        # Setup mock with single world
        self.mock_ranking_function.ranks = {'000': 5}
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True])
        self.mock_ranking_function.rank_world.side_effect = cycle([5])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Should have entries for each conditional
        self.assertEqual(len(vMin), len(self.revision_conditionals))
        self.assertEqual(len(fMin), len(self.revision_conditionals))
        
        # Count total entries across all conditionals
        total_entries = 0
        for i in range(len(self.revision_conditionals)):
            total_entries += len(vMin[i]) + len(fMin[i])
        
        # With new implementation: single world processed for each conditional
        # If world satisfies conditionalization (True), it goes to vMin
        # So each conditional should have 1 entry in vMin and 0 in fMin
        expected_total = len(self.revision_conditionals) * 1  # 1 world per conditional
        self.assertEqual(total_entries, expected_total)
        
        # Verify structure for each conditional
        for i in range(len(self.revision_conditionals)):
            self.assertIn(i, vMin)
            self.assertIn(i, fMin)
            # World satisfies conditionalization, so should be in vMin
            self.assertEqual(len(vMin[i]), 1)
            self.assertEqual(len(fMin[i]), 0)
            
            # Check the triple structure
            triple = vMin[i][0]
            self.assertIsInstance(triple, list)
            self.assertEqual(len(triple), 3)
            self.assertEqual(triple[0], 5)  # rank
            self.assertIsInstance(triple[1], list)  # accepted
            self.assertIsInstance(triple[2], list)  # rejected


class TestCompileAltIntegration(unittest.TestCase):
    """Integration tests using real objects where possible."""
    
    def test_compile_alt_with_real_conditionals(self):
        """Test compile_alt with real Conditional objects."""
        # Create real conditional objects
        a = Symbol('a', BOOL)
        b = Symbol('b', BOOL)
        
        conditional1 = Conditional(consequence=a, antecedence=b, textRepresentation="(a|b)")
        conditional1.index = 1
        
        conditional2 = Conditional(consequence=Not(a), antecedence=b, textRepresentation="(!a|b)")
        conditional2.index = 2
        
        # Create mock ranking function
        mock_ranking_function = Mock(spec=PreOCF)
        mock_ranking_function.ranks = {'00': 0, '01': 1, '10': 2, '11': 1}
        mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        mock_ranking_function.rank_world.side_effect = cycle([0])
        mock_ranking_function.conditional_acceptance.side_effect = cycle([True])
        
        # This should not raise any exceptions
        vMin, fMin = compile_alt(mock_ranking_function, [conditional1, conditional2])
        
        self.assertIsInstance(vMin, dict)
        self.assertIsInstance(fMin, dict)
        # Since each conditional gets an entry in both vMin and fMin based on the last world processed,
        # we expect 2 entries in each dict for 2 conditionals = 4 total entries
        total_entries = len(vMin) + len(fMin)
        self.assertEqual(total_entries, 4)  # 2 conditionals * 2 dicts
        self.assertGreater(total_entries, 0)  # Should have at least some entries


if __name__ == '__main__':
    unittest.main() 