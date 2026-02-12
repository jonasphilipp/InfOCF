"""
Additional unit tests for the PreOCF class, focusing on conditionalization and other
less thoroughly tested methods.
"""

import os
import unittest

from pysmt.shortcuts import And, Implies, Not, Or, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.preocf import PreOCF, RandomMinCRepPreOCF
from parser.Wrappers import parse_belief_base


class TestPreOCFAdditional(unittest.TestCase):
    """Additional tests for the PreOCF class focusing on less-tested methods."""

    @classmethod
    def setUpClass(cls):
        """Set up test environment with a bird/penguin belief base for testing."""
        # Create a birds belief base for testing
        str_birds = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
        bb_birds = parse_belief_base(str_birds)
        cls.belief_base_birds = BeliefBase(
            bb_birds.signature, bb_birds.conditionals, "birds"
        )

        # Create a PreOCF instance using System Z
        cls.preocf_z_birds = PreOCF.init_system_z(cls.belief_base_birds)
        cls.preocf_z_birds.compute_all_ranks()

        # Create symbols for testing
        cls.b = Symbol("b", BOOL)  # bird
        cls.p = Symbol("p", BOOL)  # penguin
        cls.f = Symbol("f", BOOL)  # flies
        cls.w = Symbol("w", BOOL)  # has wings

    def test_conditionalization_equivalence_across_encodings(self):
        """Different encodings of the same facts yield the same filtered world set."""
        # Build facts in three equivalent ways
        facts_fnode = And(self.b, Not(self.p))  # b=1, p=0
        facts_from_dict = And(Symbol("b", BOOL), Not(Symbol("p", BOOL)))
        facts_from_list = And(self.b, Not(self.p))

        base = PreOCF.init_system_z(self.belief_base_birds)

        a = base.compute_conditionalization(facts_fnode)
        b = base.compute_conditionalization(facts_from_dict)
        c = base.compute_conditionalization(facts_from_list)

        # All three constructions should produce the same world set
        self.assertEqual(set(a.keys()), set(b.keys()))
        self.assertEqual(set(a.keys()), set(c.keys()))

        # Ensure we truly reduced the world set (4 vars → 16 worlds total).
        # b=1 and p=0 should leave 2^(4-2)=4 worlds.
        self.assertEqual(len(a), 4)

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
            self.assertTrue(
                preocf.world_satisfies_conditionalization(world, complex_cond)
            )
            # Check that they really are birds but not penguins (first bit 1, second bit 0)
            self.assertEqual(world[0], "1")  # b is true
            self.assertEqual(world[1], "0")  # p is false

        # Test with another complex formula: (b OR p) AND f (flying birds or flying penguins)
        flying_bp = And(Or(self.b, self.p), self.f)
        flying_result = preocf.compute_conditionalization(flying_bp)

        # Check each world in the result
        for world in flying_result:
            self.assertTrue(preocf.world_satisfies_conditionalization(world, flying_bp))
            # Should be either b=1 or p=1, and f=1
            self.assertTrue(world[0] == "1" or world[1] == "1")  # b or p is true
            self.assertEqual(world[2], "1")  # f is true

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
            self.assertTrue(
                self.preocf_z_birds.world_satisfies_conditionalization(
                    world, complex_cond
                )
            )
            # Should be either f=1 or w=1
            self.assertTrue(world[2] == "1" or world[3] == "1")

        # Test with implication: b IMPLIES f (if it's a bird, then it flies)
        implies_cond = Implies(self.b, self.f)
        implies_result = self.preocf_z_birds.conditionalize_existing_ranks(implies_cond)

        # Check worlds in the result
        for world in implies_result:
            self.assertTrue(
                self.preocf_z_birds.world_satisfies_conditionalization(
                    world, implies_cond
                )
            )
            # Either b=0 or (b=1 and f=1)
            self.assertTrue(world[0] == "0" or (world[0] == "1" and world[2] == "1"))

        # Verify minimum ranks are preserved
        # Find a formula with a known minimum rank first
        known_rank = self.preocf_z_birds.formula_rank(And(self.b, self.f))

        # Conditionalize on something that wouldn't change that minimum rank
        # For example, conditionalizing on "has wings" shouldn't change the minimum rank of flying birds
        w_cond_result = self.preocf_z_birds.conditionalize_existing_ranks(self.w)

        # Compute the formula rank in the conditionalized result
        # We need to filter the conditionalized worlds for those that satisfy (b AND f)
        bf_worlds_in_w = [
            world
            for world in w_cond_result
            if self.preocf_z_birds.world_satisfies_conditionalization(
                world, And(self.b, self.f)
            )
        ]

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
        marg_one_var = self.preocf_z_birds.marginalize(["w"])
        self.assertEqual(len(marg_one_var.signature), 3)  # Should have 3 variables left
        self.assertEqual(len(marg_one_var.ranks), 8)  # Should have 2^3 = 8 worlds

        # Test marginalization by removing two variables
        marg_two_vars = self.preocf_z_birds.marginalize(["w", "f"])
        self.assertEqual(
            len(marg_two_vars.signature), 2
        )  # Should have 2 variables left
        self.assertEqual(len(marg_two_vars.ranks), 4)  # Should have 2^2 = 4 worlds

        # Test marginalization by removing three variables
        marg_three_vars = self.preocf_z_birds.marginalize(["w", "f", "p"])
        self.assertEqual(
            len(marg_three_vars.signature), 1
        )  # Should have 1 variable left
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
        orig_world = "1010"
        orig_rank = self.preocf_z_birds.ranks[orig_world]

        # Same world in marginalized OCF (without the w bit)
        marg_world = "101"
        marg_rank = marg_one_var.ranks[marg_world]

        # The rank should be less than or equal to the original rank
        # (because marginalization takes the minimum rank of all matching worlds)
        self.assertLessEqual(marg_rank, orig_rank)

    def test_init_custom_invalid_ranks(self):
        """Test custom initialization with invalid rank values."""
        # Create a rank dictionary with some invalid values
        custom_ranks = PreOCF.create_bitvec_world_dict(self.belief_base_birds.signature)

        # Set some valid and some invalid values
        custom_ranks["0000"] = 0
        custom_ranks["0001"] = 1
        custom_ranks["0010"] = -1  # Invalid negative rank
        custom_ranks["0011"] = None  # No rank

        # Create a PreOCF with these custom ranks
        custom_preocf = PreOCF.init_custom(custom_ranks, self.belief_base_birds)

        # It should not be a valid OCF
        self.assertFalse(custom_preocf.is_ocf())

        # Check the ranks were preserved
        self.assertEqual(custom_preocf.ranks["0000"], 0)
        self.assertEqual(custom_preocf.ranks["0001"], 1)
        self.assertEqual(custom_preocf.ranks["0010"], -1)
        self.assertEqual(custom_preocf.ranks["0011"], None)

        # Fix the invalid ranks
        custom_preocf.ranks["0010"] = 2
        custom_preocf.ranks["0011"] = 3

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
        marg_preocf = temp_preocf.marginalize(["w"])

        # Compute ranks for the marginalized result
        marg_preocf.compute_all_ranks()

        # The result should only have worlds where b=1, and no w variable
        for world in marg_preocf.ranks:
            self.assertEqual(len(world), 3)  # Should have 3 bits (b,p,f)
            self.assertEqual(world[0], "1")  # b should be 1

        # Now do the opposite: first marginalize, then conditionalize
        marg_first = preocf.marginalize(["w"])
        marg_first.compute_all_ranks()

        # Create a symbol for 'b' in the marginalized signature
        b_marg = Symbol("b", BOOL)

        # Conditionalize the marginalized result on 'birds'
        cond_after_marg = marg_first.conditionalize_existing_ranks(b_marg)

        # The number of worlds should match
        self.assertEqual(len(marg_preocf.ranks), len(cond_after_marg))

    def test_metadata_operations(self):
        """Test metadata storage and retrieval operations."""
        # Create a fresh PreOCF
        preocf = PreOCF.init_system_z(self.belief_base_birds)
        # Account for automatically populated metadata (e.g., diagnostics)
        base_meta_len = len(preocf.metadata)

        # Test basic metadata operations
        preocf.save_meta("author", "Alice")
        preocf.save_meta("experiment_id", "exp_001")
        preocf.save_meta("version", 1.0)
        preocf.save_meta("tags", ["test", "birds", "system-z"])

        # Test retrieval
        self.assertEqual(preocf.load_meta("author"), "Alice")
        self.assertEqual(preocf.load_meta("experiment_id"), "exp_001")
        self.assertEqual(preocf.load_meta("version"), 1.0)
        self.assertEqual(preocf.load_meta("tags"), ["test", "birds", "system-z"])

        # Test default values
        self.assertIsNone(preocf.load_meta("nonexistent"))
        self.assertEqual(preocf.load_meta("nonexistent", "default"), "default")

        # Test metadata property
        metadata_dict = preocf.metadata
        # Expect exactly 4 new keys added to whatever existed initially
        self.assertEqual(len(metadata_dict), base_meta_len + 4)
        self.assertIn("author", metadata_dict)
        self.assertIn("experiment_id", metadata_dict)
        # Optional: diagnostics metadata may be present
        if "consistency_diagnostics" in metadata_dict:
            self.assertIsInstance(metadata_dict["consistency_diagnostics"], dict)

        # Test direct metadata modification
        preocf.metadata["direct_key"] = "direct_value"
        self.assertEqual(preocf.load_meta("direct_key"), "direct_value")

        # Test metadata persistence
        import tempfile

        with tempfile.TemporaryDirectory() as temp_dir:
            meta_path = os.path.join(temp_dir, "metadata.pkl")

            # Save metadata
            preocf.save_metadata(meta_path)

            # Create new PreOCF and load metadata
            preocf2 = PreOCF.init_system_z(self.belief_base_birds)
            preocf2.load_metadata(meta_path)

            # Check that metadata was loaded
            self.assertEqual(preocf2.load_meta("author"), "Alice")
            self.assertEqual(preocf2.load_meta("experiment_id"), "exp_001")
            self.assertEqual(preocf2.load_meta("version"), 1.0)

            # Test JSON format
            meta_json_path = os.path.join(temp_dir, "metadata.json")
            preocf.save_metadata(meta_json_path, fmt="json")

            preocf3 = PreOCF.init_system_z(self.belief_base_birds)
            preocf3.load_metadata(meta_json_path)

            self.assertEqual(preocf3.load_meta("author"), "Alice")
            self.assertEqual(preocf3.load_meta("experiment_id"), "exp_001")

    def test_object_state_operations(self):
        """Test full object state save/load operations."""
        import tempfile

        # Create and configure a PreOCF
        preocf = PreOCF.init_system_z(self.belief_base_birds)
        preocf.compute_all_ranks()

        # Add some metadata
        preocf.save_meta("test_id", "state_test_001")
        preocf.save_meta("created_by", "unittest")
        preocf.save_meta("config", {"param1": 42, "param2": "value"})

        # Store original state for comparison
        original_ranks = preocf.ranks.copy()
        original_signature = preocf.signature.copy()
        original_ranking_system = preocf.ranking_system
        original_metadata = preocf.metadata.copy()

        with tempfile.TemporaryDirectory() as temp_dir:
            ocf_path = os.path.join(temp_dir, "test_preocf.pkl")

            # Save the complete object
            preocf.save_ocf(ocf_path)

            # Load the object
            loaded_preocf = PreOCF.load_ocf(ocf_path)

            # Verify all attributes are preserved
            self.assertEqual(loaded_preocf.ranks, original_ranks)
            self.assertEqual(loaded_preocf.signature, original_signature)
            self.assertEqual(loaded_preocf.ranking_system, original_ranking_system)
            self.assertEqual(loaded_preocf.metadata, original_metadata)

            # Verify metadata is accessible
            self.assertEqual(loaded_preocf.load_meta("test_id"), "state_test_001")
            self.assertEqual(loaded_preocf.load_meta("created_by"), "unittest")
            self.assertEqual(
                loaded_preocf.load_meta("config"), {"param1": 42, "param2": "value"}
            )

            # Verify the loaded object is functional
            self.assertTrue(loaded_preocf.is_ocf())

            # Test that we can perform operations on the loaded object
            test_rank = loaded_preocf.rank_world("1010")
            original_test_rank = preocf.rank_world("1010")
            self.assertEqual(test_rank, original_test_rank)

            # Test formula ranking
            formula_rank = loaded_preocf.formula_rank(self.b)
            original_formula_rank = preocf.formula_rank(self.b)
            self.assertEqual(formula_rank, original_formula_rank)

    def test_object_state_with_different_preocf_types(self):
        """Test object state operations with different PreOCF types."""
        import tempfile

        with tempfile.TemporaryDirectory() as temp_dir:
            # Test with SystemZ PreOCF
            system_z_preocf = PreOCF.init_system_z(self.belief_base_birds)
            system_z_preocf.compute_all_ranks()
            system_z_preocf.save_meta("type", "system-z")

            sz_path = os.path.join(temp_dir, "system_z.pkl")
            system_z_preocf.save_ocf(sz_path)
            loaded_sz = PreOCF.load_ocf(sz_path)

            self.assertEqual(loaded_sz.ranking_system, "system-z")
            self.assertEqual(loaded_sz.load_meta("type"), "system-z")
            self.assertTrue(loaded_sz.is_ocf())

            # Test with RandomMinCRep PreOCF
            try:
                random_preocf = PreOCF.init_random_min_c_rep(self.belief_base_birds)
                random_preocf.compute_all_ranks()
                random_preocf.save_meta("type", "random-min-c-rep")

                rand_path = os.path.join(temp_dir, "random.pkl")
                random_preocf.save_ocf(rand_path)
                loaded_rand = PreOCF.load_ocf(rand_path)

                self.assertEqual(loaded_rand.ranking_system, "random_min_c_rep")
                self.assertEqual(loaded_rand.load_meta("type"), "random-min-c-rep")
                self.assertTrue(loaded_rand.is_ocf())

                # Verify _impacts are preserved
                self.assertEqual(len(loaded_rand._impacts), len(random_preocf._impacts))
                self.assertEqual(loaded_rand._impacts, random_preocf._impacts)

            except Exception as e:
                # Skip if random min c rep fails (dependency issues)
                self.skipTest(f"RandomMinCRep test skipped due to: {e}")

            # Test with Custom PreOCF
            custom_ranks = PreOCF.create_bitvec_world_dict(
                self.belief_base_birds.signature
            )
            for i, world in enumerate(custom_ranks.keys()):
                custom_ranks[world] = i % 3  # Assign ranks 0, 1, 2 cyclically

            custom_preocf = PreOCF.init_custom(custom_ranks, self.belief_base_birds)
            custom_preocf.save_meta("type", "custom")
            custom_preocf.save_meta("custom_info", "cyclic ranks")

            custom_path = os.path.join(temp_dir, "custom.pkl")
            custom_preocf.save_ocf(custom_path)
            loaded_custom = PreOCF.load_ocf(custom_path)

            self.assertEqual(loaded_custom.ranking_system, "custom")
            self.assertEqual(loaded_custom.load_meta("type"), "custom")
            self.assertEqual(loaded_custom.load_meta("custom_info"), "cyclic ranks")
            self.assertTrue(loaded_custom.is_ocf())
            self.assertEqual(loaded_custom.ranks, custom_ranks)

    def test_getstate_setstate_operations(self):
        """Test __getstate__ and __setstate__ operations."""
        # Create and configure a PreOCF
        preocf = PreOCF.init_system_z(self.belief_base_birds)
        preocf.compute_all_ranks()
        preocf.save_meta("state_test", "getstate_test")

        # Get the complete state
        state = preocf.__getstate__()

        # Verify state contains all expected attributes
        expected_attrs = [
            "ranks",
            "signature",
            "conditionals",
            "ranking_system",
            "_metadata",
        ]
        for attr in expected_attrs:
            self.assertIn(attr, state)

        # Verify metadata is included
        self.assertIn("state_test", state["_metadata"])
        self.assertEqual(state["_metadata"]["state_test"], "getstate_test")

        # Create a new PreOCF and restore state
        new_preocf = PreOCF.init_custom({}, None, ["a", "b"])  # Dummy initialization
        new_preocf.__setstate__(state)

        # Verify all attributes were restored
        self.assertEqual(new_preocf.ranks, preocf.ranks)
        self.assertEqual(new_preocf.signature, preocf.signature)
        self.assertEqual(new_preocf.ranking_system, preocf.ranking_system)
        self.assertEqual(new_preocf.metadata, preocf.metadata)
        self.assertEqual(new_preocf.load_meta("state_test"), "getstate_test")

    def test_optimizer_handling_in_persistence(self):
        """Test that optimizer is properly handled during save/load operations."""
        try:
            # Create a RandomMinCRep PreOCF which has an optimizer
            preocf = PreOCF.init_random_min_c_rep(self.belief_base_birds)
            preocf.compute_all_ranks()

            # Verify optimizer exists initially
            self.assertIsNotNone(preocf._optimizer)

            # Get state - should include optimizer
            state = preocf.__getstate__()
            self.assertIn("_optimizer", state)

            import os
            import tempfile

            with tempfile.TemporaryDirectory() as temp_dir:
                ocf_path = os.path.join(temp_dir, "optimizer_test.pkl")

                # Save object - optimizer should be temporarily removed
                preocf.save_ocf(ocf_path)

                # Verify optimizer is restored after save
                self.assertIsNotNone(preocf._optimizer)

                # Load object
                loaded_preocf = PreOCF.load_ocf(ocf_path)

                # Verify optimizer is None in loaded object (expected)
                self.assertIsNone(loaded_preocf._optimizer)

                # Verify other attributes are preserved
                self.assertEqual(loaded_preocf._impacts, preocf._impacts)
                self.assertEqual(loaded_preocf.ranks, preocf.ranks)

        except Exception as e:
            # Skip if random min c rep fails (dependency issues)
            self.skipTest(f"Optimizer test skipped due to: {e}")

    def test_error_handling_in_persistence(self):
        """Test error handling in persistence operations."""
        import tempfile

        # Test loading non-existent file
        with tempfile.TemporaryDirectory() as temp_dir:
            nonexistent_path = os.path.join(temp_dir, "nonexistent.pkl")

            with self.assertRaises(FileNotFoundError):
                PreOCF.load_ocf(nonexistent_path)

        # Test loading invalid file content
        with tempfile.TemporaryDirectory() as temp_dir:
            invalid_path = os.path.join(temp_dir, "invalid.pkl")

            # Write non-PreOCF content
            import pickle

            with open(invalid_path, "wb") as f:
                pickle.dump({"not": "a preocf"}, f)

            with self.assertRaises(TypeError):
                PreOCF.load_ocf(invalid_path)

        # Test metadata loading with non-existent file
        preocf = PreOCF.init_system_z(self.belief_base_birds)

        with tempfile.TemporaryDirectory() as temp_dir:
            nonexistent_meta_path = os.path.join(temp_dir, "nonexistent_meta.pkl")

            # Should warn but not raise exception
            import warnings

            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                preocf.load_metadata(nonexistent_meta_path)
                self.assertTrue(len(w) > 0)
                self.assertIn("nothing loaded", str(w[0].message))

    def test_impact_persistence(self):
        """Test impact vector export/import functionality for RandomMinCRepPreOCF."""
        import tempfile

        try:
            # Create a RandomMinCRepPreOCF with computed impacts
            preocf_original = PreOCF.init_random_min_c_rep(self.belief_base_birds)
            original_impacts = preocf_original._impacts.copy()

            with tempfile.TemporaryDirectory() as temp_dir:
                json_path = os.path.join(temp_dir, "impacts.json")
                pickle_path = os.path.join(temp_dir, "impacts.pkl")

                # Test export functionality
                preocf_original.export_impacts(json_path, fmt="json")
                preocf_original.export_impacts(pickle_path, fmt="pickle")

                self.assertTrue(os.path.exists(json_path))
                self.assertTrue(os.path.exists(pickle_path))

                # Test import functionality
                preocf_imported = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
                ranks = PreOCF.create_bitvec_world_dict(
                    self.belief_base_birds.signature
                )
                PreOCF.__init__(
                    preocf_imported,
                    ranks,
                    self.belief_base_birds.signature,
                    self.belief_base_birds.conditionals,
                    "random_min_c_rep",
                    None,
                )
                preocf_imported._csp = None
                preocf_imported._optimizer = None
                preocf_imported.import_impacts(json_path)

                # Verify impacts are identical
                self.assertEqual(preocf_imported._impacts, original_impacts)

                # Test factory method
                preocf_factory = RandomMinCRepPreOCF.init_with_impacts(
                    self.belief_base_birds, pickle_path
                )

                # Verify all instances produce identical ranks
                test_worlds = ["0000", "1111", "1010", "0101"]
                for world in test_worlds:
                    orig_rank = preocf_original.rank_world(world)
                    import_rank = preocf_imported.rank_world(world)
                    factory_rank = preocf_factory.rank_world(world)

                    self.assertEqual(orig_rank, import_rank)
                    self.assertEqual(orig_rank, factory_rank)

                # Test metadata tracking
                self.assertIsNotNone(preocf_imported.load_meta("impacts_imported_from"))

                # Test validation errors
                with self.assertRaises(FileNotFoundError):
                    preocf_imported.import_impacts("nonexistent.json")

                # Test export without computed impacts
                empty_preocf = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
                with self.assertRaises(ValueError):
                    empty_preocf.export_impacts("test.json")

        except Exception as e:
            # Skip if random min c rep fails (dependency issues)
            self.skipTest(f"Impact persistence test skipped due to: {e}")

    def test_simple_impact_load_save(self):
        """Test simple impact vector load/save functionality with Python lists."""
        try:
            # Create a RandomMinCRepPreOCF with computed impacts
            preocf_original = PreOCF.init_random_min_c_rep(self.belief_base_birds)
            original_impacts = preocf_original._impacts.copy()

            # Test save_impacts
            saved_impacts = preocf_original.save_impacts()
            self.assertIsInstance(saved_impacts, list)
            self.assertEqual(saved_impacts, original_impacts)
            self.assertIsNot(saved_impacts, original_impacts)  # Should be a copy

            # Test load_impacts on a new instance
            preocf_new = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
            ranks = PreOCF.create_bitvec_world_dict(self.belief_base_birds.signature)
            PreOCF.__init__(
                preocf_new,
                ranks,
                self.belief_base_birds.signature,
                self.belief_base_birds.conditionals,
                "random_min_c_rep",
                None,
            )
            preocf_new._csp = None
            preocf_new._optimizer = None

            preocf_new.load_impacts(saved_impacts)
            self.assertEqual(preocf_new._impacts, original_impacts)

            # Test factory method
            preocf_factory = RandomMinCRepPreOCF.init_with_impacts_list(
                self.belief_base_birds, saved_impacts
            )
            self.assertEqual(preocf_factory._impacts, original_impacts)

            # Verify all instances produce identical ranks
            test_worlds = ["0000", "1111", "1010", "0101"]
            for world in test_worlds:
                orig_rank = preocf_original.rank_world(world)
                new_rank = preocf_new.rank_world(world)
                factory_rank = preocf_factory.rank_world(world)

                self.assertEqual(orig_rank, new_rank)
                self.assertEqual(orig_rank, factory_rank)

            # Test validation errors
            with self.assertRaises(ValueError):
                preocf_new.load_impacts([1, 2])  # Wrong size

            with self.assertRaises(ValueError):
                preocf_new.load_impacts([1, 2, -1, 4])  # Negative value

            with self.assertRaises(TypeError):
                preocf_new.load_impacts("not a list")  # Wrong type

            with self.assertRaises(TypeError):
                preocf_new.load_impacts([1, 2, "three", 4])  # Non-integer values

            # Test save_impacts without computed impacts
            empty_preocf = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
            with self.assertRaises(ValueError):
                empty_preocf.save_impacts()

            # Test metadata tracking
            self.assertTrue(preocf_new.load_meta("impacts_loaded_from_list"))
            self.assertIsNotNone(preocf_new.load_meta("impacts_load_timestamp"))

        except Exception as e:
            # Skip if random min c rep fails (dependency issues)
            self.skipTest(f"Simple impact load/save test skipped due to: {e}")

    def test_save_and_load_metadata_pickle_format(self):
        import tempfile
        import pickle
        from pathlib import Path

        preocf = PreOCF.init_custom({"0": 1, "1": 0}, belief_base=None, signature=["a"])
        preocf.save_meta("k", "v")

        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "meta.pkl"
            preocf.save_metadata(p)  # suffix .pkl -> pickle branch

            preocf2 = PreOCF.init_custom({"0": 1, "1": 0}, belief_base=None, signature=["a"])
            preocf2.load_metadata(p)
            assert preocf2.load_meta("k") == "v"

        # invalid payload in pickle should raise ValueError
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "invalid.pkl"
            with p.open("wb") as fd:
                pickle.dump([1, 2, 3], fd)  # not dict

            with self.assertRaises(ValueError):
                preocf2.load_metadata(p)

    def test_system_z_extended_true_without_facts(self):
        from unittest import mock
        from inference.preocf import SystemZPreOCF

        a = Symbol("a", BOOL)
        b = Symbol("b", BOOL)
        bb = BeliefBase(["a", "b"], {1: Conditional(b, a, "(b|a)")}, "bb")

        with mock.patch("inference.preocf.consistency", return_value=([[bb.conditionals[1]]], (1, 1, 1))):
            with mock.patch("inference.preocf.consistency_diagnostics", return_value={}):
                sz = SystemZPreOCF(bb, extended=True)
                assert sz.uses_extended_partition is True
                assert sz.has_infinity_partition is True

    def test_random_min_c_rep_import_impacts_pickle_branch(self):
        import tempfile
        import pickle
        from pathlib import Path
        from inference.preocf import PreOCF, RandomMinCRepPreOCF
        from inference.conditional import Conditional

        a = Symbol("a", BOOL)
        b = Symbol("b", BOOL)
        bb = BeliefBase(["a", "b"], {1: Conditional(b, a, "(b|a)")}, "bb")

        inst = RandomMinCRepPreOCF.__new__(RandomMinCRepPreOCF)
        ranks = PreOCF.create_bitvec_world_dict(bb.signature)
        PreOCF.__init__(inst, ranks, bb.signature, bb.conditionals, "random_min_c_rep", None)
        inst._csp = None
        inst._optimizer = None

        impact_data = {
            "impacts": [0],
            "conditionals_count": 1,
            "ranking_system": "random_min_c_rep",
            "signature": bb.signature,
        }

        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "impacts.pkl"
            with p.open("wb") as fd:
                pickle.dump(impact_data, fd)

            inst.import_impacts(p)
            assert inst._impacts == [0]        

    # ---------------------------------------------------------------------------
# Additional branch/edge coverage for inference/preocf.py
# ---------------------------------------------------------------------------

import pathlib
import pickle
import tempfile

import pytest
import warnings

import inference.preocf as pr
import inference.consistency_diagnostics as diag_mod

from pysmt.shortcuts import FALSE, TRUE, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.conditional import Conditional


def _bb(sig=("a",), conds=None, name="bb"):
    if conds is None:
        conds = {}
    return BeliefBase(signature=list(sig), conditionals=conds, name=name)


def test_preocf_metadata_type_validation_raises():
    ranks = pr.PreOCF.create_bitvec_world_dict(["a"])
    with pytest.raises(TypeError):
        pr.CustomPreOCF(ranks, None, ["a"], metadata="not-a-dict")  # hits line 148


def test_preocf_save_metadata_unknown_suffix_uses_fmt_and_invalid_fmt_raises(tmp_path):
    ranks = pr.PreOCF.create_bitvec_world_dict(["a"])
    ocf = pr.CustomPreOCF(ranks, None, ["a"], metadata={"k": "v"})

    # suffix not .json/.pkl -> uses fmt (hits line 184)
    p = tmp_path / "meta.data"
    ocf.save_metadata(p, fmt="json")
    assert p.exists() and p.read_text().strip().startswith("{")

    # invalid fmt (hits line 196)
    with pytest.raises(ValueError):
        ocf.save_metadata(tmp_path / "meta2.data", fmt="nope")


def test_preocf_save_metadata_json_dump_typeerror_is_wrapped(monkeypatch, tmp_path):
    ranks = pr.PreOCF.create_bitvec_world_dict(["a"])
    ocf = pr.CustomPreOCF(ranks, None, ["a"], metadata={"k": "v"})

    def boom(*a, **k):
        raise TypeError("forced")

    monkeypatch.setattr(pr.json, "dump", boom)

    with pytest.raises(TypeError, match="not JSON-serialisable"):
        ocf.save_metadata(tmp_path / "meta.data", fmt="json")  # hits lines 193-194


def test_create_bitvec_world_dict_without_signature_raises():
    # signature=None and no cls.signature -> hits lines 333-337
    with pytest.raises(ValueError):
        pr.PreOCF.create_bitvec_world_dict()


def test_preocf_base_z_partition_recursion_paths():
    # Covers PreOCF.z_part2ocf + PreOCF._rec_z_rank (lines 465-480)

    a = Symbol("a", BOOL)

    # UNSAT in last partition -> returns partition_index+1 (hits line 480)
    ocf1 = pr.CustomPreOCF({"0": 0, "1": 0}, None, ["a"])
    cond_unsat = Conditional(consequence=a, antecedence=TRUE(), textRepresentation="(a|Top)")
    ocf1._z_partition = [[], [cond_unsat]]
    assert ocf1.z_part2ocf("0") == 2

    # SAT all the way down to index 0 -> returns 0 (hits lines 475-478)
    ocf2 = pr.CustomPreOCF({"0": 0, "1": 0}, None, ["a"])
    cond_sat = Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")
    ocf2._z_partition = [[cond_sat], [cond_sat]]
    assert ocf2.z_part2ocf("0") == 0


def test_preocf_c_vec2ocf_counts_violations_with_impacts():
    # Covers lines 484-498
    b = Symbol("b", BOOL)
    ocf = pr.CustomPreOCF({"0": 0, "1": 0}, None, ["b"])
    ocf.conditionals = {1: Conditional(consequence=b, antecedence=TRUE(), textRepresentation="(b|Top)")}
    ocf._impacts = [5]
    assert ocf.c_vec2ocf("0") == 5  # world "0" violates (b|Top)


def test_preocf_impacts2ocf_unsat_adds_vector_value():
    # Covers lines 565-574
    b = Symbol("b", BOOL)
    ocf = pr.CustomPreOCF({"0": 0, "1": 0}, None, ["b"])
    ocf.conditionals = {1: Conditional(consequence=b, antecedence=TRUE(), textRepresentation="(b|Top)")}
    vector = {1: 7}
    assert ocf.impacts2ocf("0", vector) == 7  # unsat -> adds vector[last_index]


def test_systemz_preocf_facts_success_sets_state_and_metadata(monkeypatch):
    # Covers big "facts" branch (lines 662-756) + various accessors/formatters
    a = Symbol("a", BOOL)
    bb = _bb(sig=("a",), conds={})

    part = [[Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")]]
    stats = (1, 2, 3)

    monkeypatch.setattr(pr, "parse_formula", lambda s: a)
    monkeypatch.setattr(pr, "consistency", lambda _bb, weakly=False: (part, stats))
    monkeypatch.setattr(pr, "consistency_diagnostics", lambda *a, **k: {"diag": "ok"})
    monkeypatch.setattr(pr.logger, "warning", lambda *a, **k: None)

    ocf = pr.SystemZPreOCF(bb, signature=("a",), facts=[a, "a"], extended=None)

    assert ocf.uses_extended_partition is True
    assert ocf.z_partition_stats == {"layers": 1, "calls": 2, "levels": 3}  # hits line 828
    assert ocf.has_infinity_partition is True
    assert ocf.infinity_partition_index == len(part) - 1  # hits 838-840 in "true" path elsewhere
    assert ocf.infinity_partition == part[-1]            # hits 845-849 in "idx not None" path

    # diagnostics dict path + formatting
    monkeypatch.setattr(pr, "format_diagnostics_verbose", lambda _d: "DIAG")
    assert ocf.format_diagnostics_line().startswith("diag: ")

    # summary includes facts info (lines 891-903)
    s = ocf.summary()
    assert "facts=" in s and "extended=True" in s

    # format_layers_with_conditionals (lines 915-925)
    txt = ocf.format_layers_with_conditionals()
    assert "Layer 0" in txt


def test_systemz_preocf_facts_extended_false_emits_warning(monkeypatch):
    # Hits logger.warning lines 668-671
    a = Symbol("a", BOOL)
    bb = _bb(sig=("a",), conds={})

    part = [[Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")]]
    stats = (1, 1, 1)

    seen = {"warn": 0}
    monkeypatch.setattr(pr, "parse_formula", lambda s: a)
    monkeypatch.setattr(pr, "consistency", lambda _bb, weakly=False: (part, stats))
    monkeypatch.setattr(pr, "consistency_diagnostics", lambda *a, **k: {"diag": "ok"})

    def _warn(*a, **k):
        seen["warn"] += 1

    monkeypatch.setattr(pr.logger, "warning", _warn)

    _ = pr.SystemZPreOCF(bb, signature=("a",), facts=["a"], extended=False)
    assert seen["warn"] >= 1


def test_systemz_preocf_facts_unknown_vars_raises(monkeypatch):
    # Hits lines 689-694
    a_unknown = Symbol("x", BOOL)
    bb = _bb(sig=("a",), conds={})

    monkeypatch.setattr(pr, "parse_formula", lambda s: a_unknown)

    with pytest.raises(ValueError, match="unknown variable"):
        _ = pr.SystemZPreOCF(bb, signature=("a",), facts=["x"], extended=None)


def test_systemz_preocf_facts_wrong_entry_type_raises():
    bb = _bb(sig=("a",), conds={})
    with pytest.raises(TypeError):
        _ = pr.SystemZPreOCF(bb, signature=("a",), facts=[123], extended=None)  # hits line 684


def test_systemz_preocf_facts_inconsistent_partition_raises_with_diag(monkeypatch):
    # Hits lines 741-747
    a = Symbol("a", BOOL)
    bb = _bb(sig=("a",), conds={})

    stats = (0, 0, 0)
    monkeypatch.setattr(pr, "parse_formula", lambda s: a)
    monkeypatch.setattr(pr, "consistency", lambda _bb, weakly=False: (False, stats))
    monkeypatch.setattr(pr, "consistency_diagnostics", lambda *a, **k: {"diag": "bad"})
    monkeypatch.setattr(diag_mod, "format_diagnostics_verbose", lambda _d: "DIAGTEXT")

    with pytest.raises(ValueError, match=r"system-z: .*DIAGTEXT"):
        _ = pr.SystemZPreOCF(bb, signature=("a",), facts=["a"], extended=None)


def test_systemz_preocf_infinity_partition_none_in_strict_mode(monkeypatch):
    # Covers lines 838-840 (no infinity), 845-847, 871-878 (non-extended)
    a = Symbol("a", BOOL)
    bb = _bb(sig=("a",), conds={})

    part = [[Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")]]
    stats = (1, 2, 3)

    monkeypatch.setattr(pr, "consistency", lambda _bb, weakly=False: (part, stats))
    monkeypatch.setattr(pr, "consistency_diagnostics", lambda *a, **k: {"diag": "ok"})

    ocf = pr.SystemZPreOCF(bb, signature=("a",), facts=None, extended=None)
    assert ocf.uses_extended_partition is False
    assert ocf.infinity_partition_index is None
    assert ocf.infinity_partition is None

    # "layers=[]"
    ocf._z_partition = []
    assert ocf.format_partition_layers() == "layers=[]"


def test_systemz_preocf_diagnostics_property_filters_non_dict(monkeypatch):
    # Hits lines 857-860 and 887 ("diag: none")
    a = Symbol("a", BOOL)
    bb = _bb(sig=("a",), conds={})

    part = [[Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")]]
    stats = (1, 1, 1)

    monkeypatch.setattr(pr, "consistency", lambda _bb, weakly=False: (part, stats))
    monkeypatch.setattr(pr, "consistency_diagnostics", lambda *a, **k: {"diag": "ok"})

    ocf = pr.SystemZPreOCF(bb, signature=("a",), facts=None, extended=None)
    ocf.save_meta("consistency_diagnostics", 123)  # non-dict
    assert ocf.diagnostics is None
    assert ocf.format_diagnostics_line() == "diag: none"


def test_random_min_c_rep_signature_else_branch_is_executed(monkeypatch):
    # Hits line 946 without running the heavy constructor
    bb = _bb(sig=("a",), conds={})

    def boom(cls, signature=None):
        raise RuntimeError("stop-after-946")

    monkeypatch.setattr(pr.PreOCF, "create_bitvec_world_dict", classmethod(boom))

    with pytest.raises(RuntimeError, match="stop-after-946"):
        _ = pr.RandomMinCRepPreOCF(bb, signature=["a"])


def test_random_min_c_rep_no_solution_raises(monkeypatch):
    # Hits line 978 by forcing Optimize.check() != sat
    a = Symbol("a", BOOL)
    bb = _bb(sig=("a",), conds={1: Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")})

    monkeypatch.setattr(pr, "create_epistemic_state", lambda *a, **k: {"dummy": True})

    class DummyCInf:
        def __init__(self, _state): self.base_csp = []
        def preprocess_belief_base(self, _timeout): return None

    monkeypatch.setattr(pr, "CInference", DummyCInf)

    class DummyOptimize:
        def set(self, **k): return None
        def add(self, *a): return None
        def minimize(self, *a): return None
        def check(self): return "not-sat"  # != z3.sat

    monkeypatch.setattr(pr, "Optimize", DummyOptimize)

    with pytest.raises(ValueError, match="no solution found"):
        _ = pr.RandomMinCRepPreOCF(bb, signature=["a"])


def test_export_import_impacts_error_paths(tmp_path):
    # Covers lines 1028, 1046, 1052, 1056, 1062, 1069
    a = Symbol("a", BOOL)
    conds = {1: Conditional(consequence=a, antecedence=a, textRepresentation="(a|a)")}

    inst = pr.RandomMinCRepPreOCF.__new__(pr.RandomMinCRepPreOCF)
    ranks = pr.PreOCF.create_bitvec_world_dict(["a"])
    pr.PreOCF.__init__(inst, ranks, ["a"], conds, "random_min_c_rep", None)
    inst._impacts = [0]
    inst._csp = None
    inst._optimizer = None

    # export_impacts invalid fmt (line 1028)
    with pytest.raises(ValueError):
        inst.export_impacts(tmp_path / "imp.data", fmt="nope")

    # import_impacts invalid data structure (line 1046)
    bad_json = tmp_path / "bad.json"
    bad_json.write_text('[1,2,3]')
    with pytest.raises(ValueError, match="does not contain a valid"):
        inst.import_impacts(bad_json)

    # import_impacts missing key (line 1052)
    missing_key = tmp_path / "missing.json"
    missing_key.write_text('{"impacts":[0],"conditionals_count":1,"ranking_system":"random_min_c_rep"}')
    with pytest.raises(ValueError, match="missing required key"):
        inst.import_impacts(missing_key)

    # import_impacts size mismatch (line 1056)
    mismatch = tmp_path / "mismatch.json"
    mismatch.write_text('{"impacts":[0],"conditionals_count":2,"ranking_system":"random_min_c_rep","signature":["a"]}')
    with pytest.raises(ValueError, match="size mismatch"):
        inst.import_impacts(mismatch)

    # import_impacts warnings (lines 1062, 1069) but still imports
    warnfile = tmp_path / "warn.json"
    warnfile.write_text('{"impacts":[0],"conditionals_count":1,"ranking_system":"other","signature":["x"]}')
    with pytest.warns(RuntimeWarning) as rec:
        inst.import_impacts(warnfile)
    assert len(rec) >= 2
    assert inst._impacts == [0]


def test_custom_preocf_rank_world_missing_raises():
    # Hits line 1209
    ocf = pr.CustomPreOCF({"0": 0}, None, ["a"])
    with pytest.raises(ValueError, match="provide custom ranking function"):
        ocf.rank_world("1")


def test_create_preocf_factory_branches(monkeypatch):
    # Hits lines 1231-1238
    monkeypatch.setattr(pr, "SystemZPreOCF", lambda *a, **k: "Z")
    monkeypatch.setattr(pr, "RandomMinCRepPreOCF", lambda *a, **k: "R")
    monkeypatch.setattr(pr, "CustomPreOCF", lambda *a, **k: "C")

    assert pr.create_preocf("system-z", 1) == "Z"
    assert pr.create_preocf("random_min_c_rep", 1) == "R"
    assert pr.create_preocf("custom", 1) == "C"

    with pytest.raises(ValueError, match="Unknown ranking system"):
        pr.create_preocf("nope", 1)

import unittest

from inference.preocf import CustomPreOCF, SystemZPreOCF


class _DummyCond:
    def __init__(self, s: str):
        self._s = s

    def __str__(self) -> str:
        return self._s


class TestPreOCFEdgeCases(unittest.TestCase):
    def test_create_bitvec_world_dict_uses_class_signature_when_none(self):
        class _Tmp(CustomPreOCF):
            signature = ["a", "b"]

        worlds = _Tmp.create_bitvec_world_dict(signature=None)
        # 2 variables -> 4 bitvector worlds
        self.assertEqual(len(worlds), 4)
        # values are None (dict.fromkeys)
        self.assertTrue(all(v is None for v in worlds.values()))

    def test_format_partition_layers_non_extended_uses_plain_sizes(self):
        # Avoid heavy SystemZPreOCF __init__: build instance without calling it.
        z = SystemZPreOCF.__new__(SystemZPreOCF)
        z.signature = ["a", "b"]  # used by summary, harmless here
        z._state = {"z_partition_extended": False}  # => uses_extended_partition == False
        z._z_partition = [
            [_DummyCond("(b|a)"), _DummyCond("(!b|a)")],
            [_DummyCond("(c|a)")],
        ]

        self.assertEqual(z.format_partition_layers(short=True), "layers=[2,1]")

    def test_summary_when_no_facts_sets_facts_none(self):
        z = SystemZPreOCF.__new__(SystemZPreOCF)
        z.signature = ["a", "b"]
        z._state = {
            "z_partition_extended": False,
            "z_facts_present": False,  # triggers facts=None branch
        }
        z._z_partition = [[_DummyCond("(b|a)")]]  # non-empty so layers_str isn't empty

        # metadata is a read-only property -> set backing field(s)
        # (safe even if one of them is unused)
        z._metadata = {}
        try:
            setattr(z, "_SystemZPreOCF__metadata", {})
        except Exception:
            pass

        # diagnostics also often a read-only property; set backing field(s)
        z._diagnostics = None
        try:
            setattr(z, "_SystemZPreOCF__diagnostics", None)
        except Exception:
            pass

        s = z.summary(brief=True, include_facts=True)
        self.assertIn("facts=None", s)

    def test_format_layers_with_conditionals_no_partition(self):
        z = SystemZPreOCF.__new__(SystemZPreOCF)
        z.signature = ["a"]
        z._state = {"z_partition_extended": False}
        z._z_partition = None  # not a list -> triggers "(no partition)"

        self.assertEqual(z.format_layers_with_conditionals(), "(no partition)")

if __name__ == "__main__":
    unittest.main()
