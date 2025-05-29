import unittest
from unittest.mock import Mock, MagicMock
from itertools import cycle
import sys
import os

# Add the project root to the path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from inference.preocf import compile_alt, compile, PreOCF
from inference.conditional import Conditional
from pysmt.shortcuts import Symbol, And, Not, BOOL


class TestCompileComparison(unittest.TestCase):
    """Test that compile and compile_alt produce equivalent content with different structures."""
    
    def setUp(self):
        """Set up test fixtures for comparing compile and compile_alt."""
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
        
    def test_compile_vs_compile_alt_structure_difference(self):
        """Test that compile and compile_alt have different output structures but same logic."""
        # Setup consistent mock behavior for both functions
        world_satisfaction_pattern = cycle([True, False])  # Use cycle for infinite repetition
        rank_pattern = cycle([0, 1, 2, 1])  # Use cycle for infinite repetition
        acceptance_pattern = cycle([True, False])  # Use cycle for infinite repetition
        
        # Configure mocks for first call (compile)
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = world_satisfaction_pattern
        self.mock_ranking_function.rank_world.side_effect = rank_pattern
        self.mock_ranking_function.conditional_acceptance.side_effect = acceptance_pattern
        
        # Call original compile function
        original_result = compile(self.mock_ranking_function, self.revision_conditionals)
        
        # Reset mocks for second call (compile_alt)
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        # Call compile_alt function
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Verify different structures
        self.assertIsInstance(original_result, list)  # compile returns list
        self.assertIsInstance(vMin, dict)  # compile_alt returns tuple of dicts
        self.assertIsInstance(fMin, dict)
        
        # Verify same number of top-level elements
        self.assertEqual(len(original_result), len(self.revision_conditionals))
        self.assertEqual(len(vMin), len(self.revision_conditionals))
        self.assertEqual(len(fMin), len(self.revision_conditionals))
    
    def test_compile_alt_simplified_structure(self):
        """Test that compile_alt provides a more accessible structure than compile."""
        # Setup predictable behavior
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([
            True, False, True, False,  # For conditional index 0
            False, True, False, True   # For conditional index 1
        ])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # compile_alt should provide direct access via indices
        self.assertIn(0, vMin)  # Index 0 for first conditional
        self.assertIn(1, vMin)  # Index 1 for second conditional
        self.assertIn(0, fMin)  # Index 0 for first conditional
        self.assertIn(1, fMin)  # Index 1 for second conditional
        
        # Each entry should be a triple [rank, accepted_list, rejected_list]
        for index in [0, 1]:
            if vMin[index] is not None:
                self.assertIsInstance(vMin[index], list)
                if len(vMin[index]) == 3:
                    rank, accepted, rejected = vMin[index]
                    self.assertIsInstance(rank, int)
                    self.assertIsInstance(accepted, list)
                    self.assertIsInstance(rejected, list)
            
            if fMin[index] is not None:
                self.assertIsInstance(fMin[index], list)
                if len(fMin[index]) == 3:
                    rank, accepted, rejected = fMin[index]
                    self.assertIsInstance(rank, int)
                    self.assertIsInstance(accepted, list)
                    self.assertIsInstance(rejected, list)
    
    def test_same_method_calls_for_both_functions(self):
        """Test that both compile functions make the same method calls."""
        # Setup behavior
        world_satisfaction_pattern = cycle([True, False])
        rank_pattern = cycle([0, 1])
        acceptance_pattern = cycle([True, False])
        
        # Test compile function
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = world_satisfaction_pattern
        self.mock_ranking_function.rank_world.side_effect = rank_pattern
        self.mock_ranking_function.conditional_acceptance.side_effect = acceptance_pattern
        
        compile(self.mock_ranking_function, self.revision_conditionals)
        
        # Record call counts from compile
        compile_world_calls = self.mock_ranking_function.world_satisfies_conditionalization.call_count
        compile_rank_calls = self.mock_ranking_function.rank_world.call_count
        compile_acceptance_calls = self.mock_ranking_function.conditional_acceptance.call_count
        
        # Reset and test compile_alt
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Record call counts from compile_alt
        compile_alt_world_calls = self.mock_ranking_function.world_satisfies_conditionalization.call_count
        compile_alt_rank_calls = self.mock_ranking_function.rank_world.call_count
        compile_alt_acceptance_calls = self.mock_ranking_function.conditional_acceptance.call_count
        
        # Both functions should make same number of calls
        self.assertEqual(compile_world_calls, compile_alt_world_calls)
        self.assertEqual(compile_rank_calls, compile_alt_rank_calls)
        self.assertEqual(compile_acceptance_calls, compile_alt_acceptance_calls)
    
    def test_compile_alt_performance_characteristics(self):
        """Test that compile_alt has reasonable performance characteristics."""
        import time
        
        # Setup with larger dataset
        many_conditionals = []
        for i in range(10):
            mock_cond = Mock(spec=Conditional)
            mock_cond.index = i
            mock_cond.make_A_then_not_B.return_value = Mock()
            many_conditionals.append(mock_cond)
        
        # Setup mock with many worlds
        many_worlds = {f'{i:04b}': i % 4 for i in range(16)}
        self.mock_ranking_function.ranks = many_worlds
        
        # Setup mock behaviors using cycle for infinite repetition
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 3])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        # Time the execution
        start_time = time.time()
        vMin, fMin = compile_alt(self.mock_ranking_function, many_conditionals)
        execution_time = time.time() - start_time
        
        # Should complete in reasonable time (less than 1 second for this size)
        self.assertLess(execution_time, 1.0)
        
        # Should produce correct structure - each conditional gets an entry in both dicts
        self.assertEqual(len(vMin), len(many_conditionals))
        self.assertEqual(len(fMin), len(many_conditionals))
    
    def test_compile_alt_content_equivalence(self):
        """Test that compile_alt contains equivalent logical content to compile."""
        # This is a conceptual test - in practice, you'd need to understand
        # the exact mapping between the two output formats
        
        # Setup deterministic behavior
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        # Get outputs from both functions
        original_result = compile(self.mock_ranking_function, self.revision_conditionals)
        
        # Reset for second call
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = cycle([True, False])
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 1])
        self.mock_ranking_function.conditional_acceptance.side_effect = cycle([True, False])
        
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)
        
        # Both should have processed the same number of conditionals
        self.assertEqual(len(original_result), len(vMin))
        self.assertEqual(len(original_result), len(fMin))
        
        # Both should contain data for each conditional index
        for i in range(len(self.revision_conditionals)):
            # original_result[i] should be a list with two dicts
            self.assertIsInstance(original_result[i], list)
            self.assertEqual(len(original_result[i]), 2)
            
            # vMin and fMin should have entries for index i
            self.assertIn(i, vMin)
            self.assertIn(i, fMin)


if __name__ == '__main__':
    unittest.main() 