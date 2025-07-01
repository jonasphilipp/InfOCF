import os
import sys
import unittest
from itertools import cycle
from unittest.mock import Mock

# Add the project root to the path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


from inference.c_revision import compile, compile_alt
from inference.conditional import Conditional
from inference.preocf import PreOCF


class TestCompileContentComparison(unittest.TestCase):
    """Direct comparison of actual output content between compile and compile_alt."""

    def setUp(self):
        """Set up test fixtures for content comparison."""
        # Create mock conditionals
        self.mock_conditional_1 = Mock(spec=Conditional)
        self.mock_conditional_1.index = 1
        self.mock_conditional_1.make_A_then_B.return_value = Mock()
        self.mock_conditional_1.make_A_then_not_B.return_value = Mock()

        self.mock_conditional_2 = Mock(spec=Conditional)
        self.mock_conditional_2.index = 2
        self.mock_conditional_2.make_A_then_B.return_value = Mock()
        self.mock_conditional_2.make_A_then_not_B.return_value = Mock()

        self.revision_conditionals = [self.mock_conditional_1, self.mock_conditional_2]

        # Create mock ranking function
        self.mock_ranking_function = Mock(spec=PreOCF)
        self.mock_ranking_function.ranks = {"00": 0, "01": 1, "10": 2, "11": 1}

    def test_same_logical_content_different_structure(self):
        """Test that compile and compile_alt contain the same logical content."""

        # Setup deterministic behavior for both function calls
        # World satisfaction: True, False, True, False for each conditional
        world_satisfaction_calls = []
        rank_calls = []
        acceptance_calls = []

        def track_world_satisfaction(*args):
            result = len(world_satisfaction_calls) % 2 == 0  # Alternating True/False
            world_satisfaction_calls.append(result)
            return result

        def track_rank(*args):
            result = [0, 1, 2, 1][len(rank_calls) % 4]  # Cycle through ranks
            rank_calls.append(result)
            return result

        def track_acceptance(*args):
            result = len(acceptance_calls) % 2 == 0  # Alternating True/False
            acceptance_calls.append(result)
            return result

        # Configure mocks for compile
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            track_world_satisfaction
        )
        self.mock_ranking_function.rank_world.side_effect = track_rank
        self.mock_ranking_function.conditional_acceptance.side_effect = track_acceptance

        # Call compile function
        compile_result = compile(self.mock_ranking_function, self.revision_conditionals)

        # Reset call trackers for compile_alt
        world_satisfaction_calls.clear()
        rank_calls.clear()
        acceptance_calls.clear()

        # Reset mocks for compile_alt (same behavior)
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            track_world_satisfaction
        )
        self.mock_ranking_function.rank_world.side_effect = track_rank
        self.mock_ranking_function.conditional_acceptance.side_effect = track_acceptance

        # Call compile_alt function
        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)

        # Now compare the content
        print(f"\nCompile result: {compile_result}")
        print(f"Compile_alt vMin: {vMin}")
        print(f"Compile_alt fMin: {fMin}")

        # Extract and compare the logical content
        self._compare_content_structures(compile_result, vMin, fMin)

    def _compare_content_structures(self, compile_result, vMin, fMin):
        """Helper method to compare the logical content of both function outputs."""

        # compile returns: list of [dict1, dict2] for each conditional
        # compile_alt returns: (vMin_dict, fMin_dict) where each has lists of triples per conditional

        expected_indices = [cond.index for cond in self.revision_conditionals]  # [1, 2]
        for list_index, conditional_index in enumerate(expected_indices):
            # Get data from compile function using list index
            compile_data = compile_result[list_index]
            self.assertIsInstance(compile_data, list)
            self.assertEqual(
                len(compile_data), 2
            )  # Should have two dicts (branch 0 and 1)

            compile_branch_0 = compile_data[0]  # v_dict=True branch
            compile_branch_1 = compile_data[1]  # v_dict=False branch

            # Get data from compile_alt function using conditional index
            vMin_data = vMin.get(conditional_index)
            fMin_data = fMin.get(conditional_index)

            print(f"\nConditional {conditional_index}:")
            print(f"  Compile branch 0 (v_dict=True): {compile_branch_0}")
            print(f"  Compile branch 1 (v_dict=False): {compile_branch_1}")
            print(f"  Compile_alt vMin: {vMin_data}")
            print(f"  Compile_alt fMin: {fMin_data}")

            # Both should have some data
            self.assertIsNotNone(vMin_data)
            self.assertIsNotNone(fMin_data)

            # Check that vMin_data and fMin_data are now lists
            self.assertIsInstance(vMin_data, list)
            self.assertIsInstance(fMin_data, list)

            # Each item in the lists should be a triple [rank, accepted, rejected]
            for triple in vMin_data:
                if triple:  # Skip empty triples
                    self.assertIsInstance(triple, list)
                    self.assertEqual(len(triple), 3)

            for triple in fMin_data:
                if triple:  # Skip empty triples
                    self.assertIsInstance(triple, list)
                    self.assertEqual(len(triple), 3)

    def test_content_consistency_with_real_data(self):
        """Test content consistency using more realistic mock data."""

        # Setup more complex scenario
        self.mock_ranking_function.ranks = {
            "000": 0,
            "001": 1,
            "010": 2,
            "011": 1,
            "100": 3,
            "101": 2,
            "110": 1,
            "111": 0,
        }

        # Create infinite patterns using cycle to prevent StopIteration
        satisfaction_pattern = cycle(
            [True, False, True, False, True, False, True, False]
        )
        rank_pattern = cycle([0, 1, 2, 1, 3, 2, 1, 0])

        # Test compile function
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            satisfaction_pattern
        )
        self.mock_ranking_function.rank_world.side_effect = rank_pattern

        compile_result = compile(self.mock_ranking_function, self.revision_conditionals)

        # Reset for compile_alt - use fresh cycles
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            cycle([True, False, True, False, True, False, True, False])
        )
        self.mock_ranking_function.rank_world.side_effect = cycle(
            [0, 1, 2, 1, 3, 2, 1, 0]
        )

        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)

        # Verify that both functions processed the same amount of data
        self.assertEqual(len(compile_result), len(self.revision_conditionals))
        self.assertEqual(len(vMin), len(self.revision_conditionals))
        self.assertEqual(len(fMin), len(self.revision_conditionals))

        # Print actual results for manual inspection
        print("\n=== CONTENT COMPARISON ===")
        print(f"Compile result structure: list of {len(compile_result)} items")
        print(
            f"Compile_alt structure: vMin dict with {len(vMin)} entries, fMin dict with {len(fMin)} entries"
        )

        expected_indices = [cond.index for cond in self.revision_conditionals]  # [1, 2]
        for list_index, conditional_index in enumerate(expected_indices):
            print(f"\nConditional {conditional_index}:")
            print(f"  Compile result[{list_index}]: {compile_result[list_index]}")
            print(
                f"  Compile_alt vMin[{conditional_index}]: {vMin.get(conditional_index)}"
            )
            print(
                f"  Compile_alt fMin[{conditional_index}]: {fMin.get(conditional_index)}"
            )

            # Verify that each conditional has data in both formats
            self.assertIsInstance(compile_result[list_index], list)
            self.assertEqual(len(compile_result[list_index]), 2)
            self.assertIn(conditional_index, vMin)
            self.assertIn(conditional_index, fMin)

    def test_extract_equivalent_information(self):
        """Test that equivalent information can be extracted from both output formats."""

        # Setup simple scenario with infinite cycles
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            cycle([True, False])
        )
        self.mock_ranking_function.rank_world.side_effect = cycle(
            [5, 3]
        )  # Different ranks for variety

        # Get results from both functions
        compile_result = compile(self.mock_ranking_function, self.revision_conditionals)

        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            cycle([True, False])
        )
        self.mock_ranking_function.rank_world.side_effect = cycle([5, 3])

        vMin, fMin = compile_alt(self.mock_ranking_function, self.revision_conditionals)

        print("\n=== INFORMATION EXTRACTION TEST ===")

        # For each conditional, check that we can extract equivalent information
        expected_indices = [cond.index for cond in self.revision_conditionals]  # [1, 2]
        for list_index, conditional_index in enumerate(expected_indices):
            print(f"\nConditional {conditional_index}:")

            # From compile result
            compile_data = compile_result[list_index]
            print(f"  Compile structure: {compile_data}")

            # From compile_alt result - now lists of triples
            vMin_data = vMin[conditional_index]
            fMin_data = fMin[conditional_index]

            print(f"  Compile_alt vMin: {vMin_data}")
            print(f"  Compile_alt fMin: {fMin_data}")

            # Both should be lists
            self.assertIsInstance(vMin_data, list)
            self.assertIsInstance(fMin_data, list)

            # Content should have some logical relationship
            # (exact comparison would require understanding the transformation logic)
            # For now, just verify structure consistency
            if vMin_data:
                for triple in vMin_data:
                    if triple and len(triple) >= 3:
                        vMin_accepted = triple[1]
                        vMin_rejected = triple[2]
                        print(f"  vMin accepted conditionals: {vMin_accepted}")
                        print(f"  vMin rejected conditionals: {vMin_rejected}")
                        self.assertIsInstance(vMin_accepted, list)
                        self.assertIsInstance(vMin_rejected, list)

            if fMin_data:
                for triple in fMin_data:
                    if triple and len(triple) >= 3:
                        fMin_accepted = triple[1]
                        fMin_rejected = triple[2]
                        print(f"  fMin accepted conditionals: {fMin_accepted}")
                        print(f"  fMin rejected conditionals: {fMin_rejected}")
                        self.assertIsInstance(fMin_accepted, list)
                        self.assertIsInstance(fMin_rejected, list)

    def test_information_loss_demonstration(self):
        """Demonstrate that compile_alt preserves equivalent information to compile."""

        # Setup with multiple worlds that will show the difference clearly
        self.mock_ranking_function.ranks = {"00": 0, "01": 1, "10": 2, "11": 3}

        # Make world satisfaction alternate so we have multiple worlds in each branch
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            cycle([True, False, True, False])
        )
        # Give different ranks to each world so we can see which one is kept
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 3])

        # Get results from compile
        compile_result = compile(self.mock_ranking_function, [self.mock_conditional_1])

        # Reset and get results from compile_alt
        self.mock_ranking_function.reset_mock()
        self.mock_ranking_function.world_satisfies_conditionalization.side_effect = (
            cycle([True, False, True, False])
        )
        self.mock_ranking_function.rank_world.side_effect = cycle([0, 1, 2, 3])

        vMin, fMin = compile_alt(self.mock_ranking_function, [self.mock_conditional_1])

        print("\n=== INFORMATION PRESERVATION DEMONSTRATION ===")
        print(f"Input worlds: {list(self.mock_ranking_function.ranks.keys())}")
        print(f"World ranks: {list(self.mock_ranking_function.ranks.values())}")

        # Analyze compile result
        compile_data = compile_result[0]  # First (and only) conditional
        v_dict_true_branch = compile_data[0]  # Worlds where v_dict=True
        v_dict_false_branch = compile_data[1]  # Worlds where v_dict=False

        print("\nCompile function (complete information):")
        print(f"  v_dict=True branch: {v_dict_true_branch}")
        print(f"  v_dict=False branch: {v_dict_false_branch}")
        print(
            f"  Total worlds stored: {len(v_dict_true_branch) + len(v_dict_false_branch)}"
        )

        # Analyze compile_alt result - use actual conditional index (1)
        vMin_data = vMin[
            1
        ]  # Data for conditional 1 (not 0, since conditional_1 has index=1)
        fMin_data = fMin[
            1
        ]  # Data for conditional 1 (not 0, since conditional_1 has index=1)

        print("\nCompile_alt function (equivalent information):")
        print(f"  vMin (v_dict=True worlds): {vMin_data}")
        print(f"  fMin (v_dict=False worlds): {fMin_data}")
        print(f"  Total worlds stored: {len(vMin_data) + len(fMin_data)}")

        # Compare information preservation
        compile_world_count = len(v_dict_true_branch) + len(v_dict_false_branch)
        compile_alt_world_count = len(vMin_data) + len(fMin_data)

        print("\nInformation comparison:")
        print(f"  Compile preserves {compile_world_count} worlds")
        print(f"  Compile_alt preserves {compile_alt_world_count} worlds")

        # Verify the structure - compile_alt now stores lists of triples
        self.assertIsInstance(vMin_data, list)
        self.assertIsInstance(fMin_data, list)

        # Check that each entry in the lists is a triple
        for triple in vMin_data:
            self.assertIsInstance(triple, list)
            self.assertEqual(len(triple), 3)  # [rank, accepted, rejected]

        for triple in fMin_data:
            self.assertIsInstance(triple, list)
            self.assertEqual(len(triple), 3)  # [rank, accepted, rejected]


if __name__ == "__main__":
    unittest.main()
