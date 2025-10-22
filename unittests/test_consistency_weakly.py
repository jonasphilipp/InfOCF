import glob
import os
import sys

"""
Extended (weakly) consistency and partition tests.

Purpose
-------
Cover a broader set of weakly/extended consistency behaviors, including
properties of the last layer and interactions with facts, beyond the small
sanity checks.

Run
---
uv run pytest -q unittests/test_consistency_weakly.py
"""

import unittest

# Add the base directory to the Python path
BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.append(BASE_DIR)

from inference.consistency_sat import consistency, consistency_indices
from parser.Wrappers import parse_belief_base


class WeaklyConsistentTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.BASE_DIR = BASE_DIR
        # Path to the random belief base files
        cls.RANDOM_BELIEF_BASES_PATH = os.path.join(
            cls.BASE_DIR, "examples", "random_large"
        )

    def test_weakly_consistent_random_belief_bases(self):
        """Test consistency function with weakly=True parameter.

        When weakly=True:
        - Empty last partition → belief base is consistent
        - Non-empty last partition → belief base is weakly consistent

        Currently testing with consistent belief bases (expecting empty last partition).
        """
        # Get all random belief base files
        pattern = os.path.join(self.RANDOM_BELIEF_BASES_PATH, "randomTest_80_80_*.cl")
        belief_base_files = glob.glob(pattern)

        # Ensure we have some files to test
        self.assertTrue(len(belief_base_files) > 0, "No random belief base files found")

        # Test a subset of files (first 10 to keep test time reasonable)
        test_files = belief_base_files[:10]

        consistent_count = 0
        weakly_consistent_count = 0

        for belief_base_file in test_files:
            with self.subTest(belief_base_file=belief_base_file):
                # Parse the belief base
                belief_base = parse_belief_base(belief_base_file)

                # Test consistency with weakly=True
                result, stats = consistency(belief_base, solver="z3", weakly=True)

                # Check that we got a valid result (not False)
                self.assertIsInstance(
                    result,
                    list,
                    f"Expected list result for {belief_base_file}, got {type(result)}",
                )

                # Check that the partition is not empty
                self.assertGreater(
                    len(result),
                    0,
                    f"Expected non-empty partition for {belief_base_file}",
                )

                # Check the last partition to determine consistency type
                last_partition = result[-1]
                if len(last_partition) == 0:
                    consistent_count += 1
                    print(
                        f"✓ {os.path.basename(belief_base_file)}: CONSISTENT "
                        f"(empty last partition), Partition lengths: {[len(p) for p in result]}"
                    )
                else:
                    weakly_consistent_count += 1
                    print(
                        f"✓ {os.path.basename(belief_base_file)}: WEAKLY CONSISTENT "
                        f"(non-empty last partition), Partition lengths: {[len(p) for p in result]}"
                    )

                # Additional assertions about the partition structure
                self.assertTrue(
                    all(isinstance(p, list) for p in result),
                    "All partition elements should be lists",
                )

                # Check that the stats are reasonable
                partition_lengths, calls, levels = stats
                self.assertEqual(
                    len(partition_lengths),
                    len(result),
                    "Stats partition lengths should match result partition count",
                )
                self.assertGreater(calls, 0, "Should have made SAT solver calls")
                self.assertGreater(
                    levels, 0, "Should have processed at least one level"
                )

        print(
            f"\nSummary: {consistent_count}/{len(test_files)} belief bases were consistent (empty last partition)"
        )
        print(
            f"Summary: {weakly_consistent_count}/{len(test_files)} belief bases were weakly consistent (non-empty last partition)"
        )

    def test_consistency_indices_random_belief_bases(self):
        """Test consistency_indices function with weakly=True parameter.

        This function works with indices of conditionals rather than the conditionals themselves.
        Same semantics as consistency():
        - Empty last partition → belief base is consistent
        - Non-empty last partition → belief base is weakly consistent
        """
        # Get all random belief base files
        pattern = os.path.join(self.RANDOM_BELIEF_BASES_PATH, "randomTest_80_80_*.cl")
        belief_base_files = glob.glob(pattern)

        # Ensure we have some files to test
        self.assertTrue(len(belief_base_files) > 0, "No random belief base files found")

        # Test a subset of files (first 10 to keep test time reasonable)
        test_files = belief_base_files[:10]

        consistent_count = 0
        weakly_consistent_count = 0

        for belief_base_file in test_files:
            with self.subTest(belief_base_file=belief_base_file):
                # Parse the belief base
                belief_base = parse_belief_base(belief_base_file)

                # Test consistency_indices with weakly=True
                result, stats = consistency_indices(
                    belief_base, solver="z3", weakly=True
                )

                # Check that we got a valid result (not False)
                self.assertIsInstance(
                    result,
                    list,
                    f"Expected list result for {belief_base_file}, got {type(result)}",
                )

                # Check that the partition is not empty
                self.assertGreater(
                    len(result),
                    0,
                    f"Expected non-empty partition for {belief_base_file}",
                )

                # Check the last partition to determine consistency type
                last_partition = result[-1]
                if len(last_partition) == 0:
                    consistent_count += 1
                    print(
                        f"✓ {os.path.basename(belief_base_file)}: CONSISTENT (indices) "
                        f"(empty last partition), Partition lengths: {[len(p) for p in result]}"
                    )
                else:
                    weakly_consistent_count += 1
                    print(
                        f"✓ {os.path.basename(belief_base_file)}: WEAKLY CONSISTENT (indices) "
                        f"(non-empty last partition), Partition lengths: {[len(p) for p in result]}"
                    )

                # Additional assertions about the partition structure
                self.assertTrue(
                    all(isinstance(p, list) for p in result),
                    "All partition elements should be lists",
                )

                # For consistency_indices, partition elements should contain indices (strings/keys)
                for partition_level in result:
                    for item in partition_level:
                        # Items should be keys from the conditionals dictionary
                        self.assertIn(
                            item,
                            belief_base.conditionals.keys(),
                            f"Partition item {item} should be a valid conditional key",
                        )

                # Check that the stats are reasonable
                partition_lengths, calls, levels = stats
                self.assertEqual(
                    len(partition_lengths),
                    len(result),
                    "Stats partition lengths should match result partition count",
                )
                self.assertGreater(calls, 0, "Should have made SAT solver calls")
                self.assertGreater(
                    levels, 0, "Should have processed at least one level"
                )

        print(
            f"\nSummary (consistency_indices): {consistent_count}/{len(test_files)} belief bases were consistent (empty last partition)"
        )
        print(
            f"Summary (consistency_indices): {weakly_consistent_count}/{len(test_files)} belief bases were weakly consistent (non-empty last partition)"
        )

    def test_consistency_vs_consistency_indices_comparison(self):
        """Compare results between consistency and consistency_indices functions.

        Both functions should produce partitions with the same structure (same lengths),
        but consistency_indices works with indices while consistency works with objects.
        """
        pattern = os.path.join(self.RANDOM_BELIEF_BASES_PATH, "randomTest_80_80_*.cl")
        belief_base_files = glob.glob(pattern)

        # Test first 5 files for comparison
        test_files = belief_base_files[:5]

        for belief_base_file in test_files:
            with self.subTest(belief_base_file=belief_base_file):
                belief_base = parse_belief_base(belief_base_file)

                # Test both functions with weakly=True
                result_consistency, stats_consistency = consistency(
                    belief_base, solver="z3", weakly=True
                )
                result_indices, stats_indices = consistency_indices(
                    belief_base, solver="z3", weakly=True
                )

                # Both should return lists
                self.assertIsInstance(result_consistency, list)
                self.assertIsInstance(result_indices, list)

                # Partition structures should have the same lengths
                consistency_lengths = [len(p) for p in result_consistency]
                indices_lengths = [len(p) for p in result_indices]

                self.assertEqual(
                    consistency_lengths,
                    indices_lengths,
                    "Partition lengths should match between consistency and consistency_indices",
                )

                # Both should have the same consistency type (consistent vs weakly consistent)
                consistency_type = (
                    "CONSISTENT"
                    if len(result_consistency[-1]) == 0
                    else "WEAKLY CONSISTENT"
                )
                indices_type = (
                    "CONSISTENT"
                    if len(result_indices[-1]) == 0
                    else "WEAKLY CONSISTENT"
                )

                self.assertEqual(
                    consistency_type,
                    indices_type,
                    "Consistency types should match between both functions",
                )

                print(
                    f"✓ {os.path.basename(belief_base_file)}: Both functions agree - {consistency_type}"
                )
                print(f"  Partition lengths: {consistency_lengths}")

    def test_consistency_without_weakly_flag(self):
        """Test consistency function without weakly=True flag.

        When weakly=False (default), the function should return False for
        inconsistent belief bases instead of a partition with non-empty last element.
        """
        # Get one random belief base file for testing
        pattern = os.path.join(self.RANDOM_BELIEF_BASES_PATH, "randomTest_80_80_*.cl")
        belief_base_files = glob.glob(pattern)
        self.assertTrue(len(belief_base_files) > 0, "No random belief base files found")

        # Test the first file
        belief_base_file = belief_base_files[0]
        belief_base = parse_belief_base(belief_base_file)

        # Test consistency with weakly=False (default)
        result, stats = consistency(belief_base, solver="z3", weakly=False)

        # For the random belief bases, we expect they might be inconsistent when weakly=False
        # If the result is False, that means the belief base is inconsistent
        if result is False:
            print(
                f"✓ {os.path.basename(belief_base_file)}: INCONSISTENT (as expected), Stats: {stats}"
            )
        else:
            # If it's consistent, it should be a valid partition
            self.assertIsInstance(result, list)
            self.assertGreater(len(result), 0)
            print(
                f"✓ {os.path.basename(belief_base_file)}: CONSISTENT, Partition lengths: {[len(p) for p in result]}, Stats: {stats}"
            )

    def test_simple_known_belief_base(self):
        """Test with a simple known belief base from the unittests directory."""
        simple_ckb_path = os.path.join(self.BASE_DIR, "unittests", "simpleCKB.cl")
        self.assertTrue(
            os.path.exists(simple_ckb_path),
            f"Simple CKB file not found: {simple_ckb_path}",
        )

        # Parse the simple belief base
        belief_base = parse_belief_base(simple_ckb_path)

        # Test with weakly=True
        result_weakly, stats_weakly = consistency(belief_base, solver="z3", weakly=True)

        # Test with weakly=False
        result_normal, stats_normal = consistency(
            belief_base, solver="z3", weakly=False
        )

        # Interpret results
        if isinstance(result_weakly, list):
            if len(result_weakly[-1]) == 0:
                consistency_type = "CONSISTENT (empty last partition)"
            else:
                consistency_type = "WEAKLY CONSISTENT (non-empty last partition)"
        else:
            consistency_type = "INCONSISTENT"

        print(
            f"✓ simpleCKB.cl - Weakly=True: {consistency_type}, Partition lengths: {[len(p) for p in result_weakly] if isinstance(result_weakly, list) else result_weakly}"
        )
        print(
            f"✓ simpleCKB.cl - Weakly=False: {[len(p) for p in result_normal] if isinstance(result_normal, list) else result_normal}"
        )

        # Both should return valid results (either list or False)
        self.assertIsNotNone(result_weakly)
        self.assertIsNotNone(result_normal)

    def test_comprehensive_weakly_consistent_test(self):
        """Test a larger set of random belief bases to analyze consistency patterns."""
        pattern = os.path.join(self.RANDOM_BELIEF_BASES_PATH, "randomTest_80_80_*.cl")
        belief_base_files = glob.glob(pattern)

        # Test a larger subset (first 20 files)
        test_files = belief_base_files[:20]

        consistent_count = 0  # empty last partition
        weakly_consistent_count = 0  # non-empty last partition
        inconsistent_count = 0  # returns False with weakly=False

        for belief_base_file in test_files:
            with self.subTest(belief_base_file=belief_base_file):
                belief_base = parse_belief_base(belief_base_file)

                # Test both with and without weakly flag
                result_weakly, stats_weakly = consistency(
                    belief_base, solver="z3", weakly=True
                )
                result_normal, stats_normal = consistency(
                    belief_base, solver="z3", weakly=False
                )

                # Both should return valid results
                self.assertIsNotNone(result_weakly)
                self.assertIsNotNone(result_normal)

                # Analyze weakly=True results
                if isinstance(result_weakly, list):
                    if len(result_weakly[-1]) == 0:
                        consistent_count += 1
                    else:
                        weakly_consistent_count += 1
                        # This is a weakly consistent belief base - non-empty last partition
                        self.assertGreater(
                            len(result_weakly[-1]),
                            0,
                            "Expected non-empty last partition for weakly consistent belief base",
                        )

                # Check if it's inconsistent with normal consistency
                if result_normal is False:
                    inconsistent_count += 1
                    # If it's inconsistent normally, it should still return a partition with weakly=True
                    self.assertIsInstance(
                        result_weakly,
                        list,
                        "Weakly consistent check should return partition even for inconsistent belief base",
                    )

        print("\nComprehensive test results:")
        print(
            f"- Consistent (empty last partition): {consistent_count}/{len(test_files)}"
        )
        print(
            f"- Weakly consistent (non-empty last partition): {weakly_consistent_count}/{len(test_files)}"
        )
        print(f"- Inconsistent (normal mode): {inconsistent_count}/{len(test_files)}")

        # At least some belief bases should be processed successfully
        self.assertGreater(
            consistent_count + weakly_consistent_count,
            0,
            "Should have found at least one consistent or weakly consistent belief base",
        )


if __name__ == "__main__":
    unittest.main()
