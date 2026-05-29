"""
System Z symbolic bucket tests.

Run
---
uv run --python 3.12 --extra testing pytest -q unittests/test_system_z_symbolic.py
"""

import unittest

from inference.belief_base import BeliefBase
from inference.preocf import PreOCF
from parser.Wrappers import parse_belief_base


class TestSystemZSymbolic(unittest.TestCase):
    """Tests for the additive symbolic System Z helpers."""

    @classmethod
    def setUpClass(cls):
        birds_kb = "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),(w|b)\n}"
        birds_bb = parse_belief_base(birds_kb)
        cls.belief_base_birds = BeliefBase(
            birds_bb.signature, birds_bb.conditionals, "birds"
        )

        extended_kb = """
signature
   p, b, f, w, a

conditionals
birds002{
   (f | b),
   (!f | p),
   (Bottom | p,!b),
   (w | b)
}
"""
        extended_bb = parse_belief_base(extended_kb)
        cls.belief_base_extended = BeliefBase(
            extended_bb.signature, extended_bb.conditionals, "birds002"
        )

    def test_symbolic_helpers_preserve_initial_ranks_contract(self):
        """Using symbolic helpers should not eagerly fill the existing ranks dict."""

        preocf = PreOCF.init_system_z(self.belief_base_birds)
        initial_world_count = len(preocf.ranks)

        buckets = preocf.symbolic_rank_buckets()

        self.assertEqual(initial_world_count, len(preocf.ranks))
        self.assertEqual(len(buckets), len(preocf.partition_layer_sizes()) + 1)
        self.assertTrue(all(rank is None for rank in preocf.ranks.values()))

    def test_rank_bucket_formulas_match_rank_world(self):
        """Each world should satisfy exactly one symbolic bucket matching its rank."""

        preocf = PreOCF.init_system_z(self.belief_base_birds)
        buckets = preocf.symbolic_rank_buckets()

        for world in preocf.ranks.keys():
            matching_ranks = [
                bucket.rank
                for bucket in buckets
                if preocf.world_satisfies_conditionalization(world, bucket.formula)
            ]
            self.assertEqual(
                matching_ranks,
                [preocf.rank_world(world)],
                f"unexpected symbolic bucket membership for {world}",
            )

    def test_symbolic_bucket_enumeration_matches_classic_ranks(self):
        """Enumerating symbolic buckets should reproduce classic world groups."""

        classic = PreOCF.init_system_z(self.belief_base_birds)
        classic.compute_all_ranks()

        symbolic = PreOCF.init_system_z(self.belief_base_birds)
        for bucket in symbolic.symbolic_rank_buckets():
            expected_worlds = {
                world for world, rank in classic.ranks.items() if rank == bucket.rank
            }
            actual_worlds = set(symbolic.enumerate_rank_bucket_worlds(bucket.rank))
            self.assertEqual(actual_worlds, expected_worlds)

    def test_materialize_ranks_from_buckets_matches_compute_all_ranks(self):
        """Bucket-based materialization should match the current world-by-world path."""

        classic = PreOCF.init_system_z(self.belief_base_birds)
        classic.compute_all_ranks()

        symbolic = PreOCF.init_system_z(self.belief_base_birds)
        symbolic.materialize_ranks_from_buckets()

        self.assertEqual(symbolic.ranks, classic.ranks)
        self.assertTrue(symbolic.is_ocf())

    def test_extended_infinity_bucket_matches_classic_ranks(self):
        """Extended System Z should expose a matching infinity bucket when present."""

        classic = PreOCF.init_system_z(self.belief_base_extended, extended=True)
        classic.compute_all_ranks()

        symbolic = PreOCF.init_system_z(self.belief_base_extended, extended=True)
        buckets = symbolic.symbolic_rank_buckets()

        self.assertTrue(symbolic.uses_extended_partition)
        self.assertTrue(buckets[-1].is_infinity)

        expected_worlds = {
            world for world, rank in classic.ranks.items() if rank == buckets[-1].rank
        }
        actual_worlds = set(symbolic.enumerate_rank_bucket_worlds(buckets[-1].rank))

        self.assertTrue(expected_worlds)
        self.assertEqual(actual_worlds, expected_worlds)
