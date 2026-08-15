"""Differential and oracle coverage for weak System W/LexInf backends."""

from __future__ import annotations

from itertools import combinations
import json
import random
import tempfile
import unittest

from pysat.formula import WCNF

from inference.backend_diagnostics import (
    FiniteWorldOracle,
    compare_weak_backends,
    normalize_mcs_trace,
)
from inference.optimizer import OptimizerRC2
from inference.tseitin_transformation import TseitinTransformation
from parser.Wrappers import parse_belief_base, parse_queries


RULE_POOL = ["(b|a)", "(!b|a)", "(c|b)", "(!c|b)", "(a|c)"]
QUERIES = "(a|b),(!a|b),(b|c),(!b|c),(c|Top)"


def belief_base(rules: list[str]):
    return parse_belief_base(
        "signature\na,b,c\n\nconditionals\nkb{\n" + ",\n".join(rules) + "\n}"
    )


class TestWeakBackendDifferential(unittest.TestCase):
    def assert_backends_match_oracle(self, rules: list[str]) -> None:
        bb = belief_base(rules)
        queries = parse_queries(QUERIES)
        try:
            oracle = FiniteWorldOracle(bb)
        except ValueError:  # Not weakly consistent: outside this test's domain.
            return
        for operator in ("system-w", "lex_inf"):
            expected = {}
            oracle_trace = []
            for index, query in queries.conditionals.items():
                expected[index] = oracle.infer(query, operator)
                oracle_trace.extend(oracle.trace)
            comparison = compare_weak_backends(bb, queries, operator)
            self.assertTrue(comparison.agrees, comparison)
            self.assertEqual(comparison.rc2.partition, oracle.partition)
            self.assertEqual(comparison.z3.partition, oracle.partition)
            self.assertEqual(comparison.rc2.results, expected)
            self.assertEqual(comparison.z3.results, expected)
            self.assertEqual(
                normalize_mcs_trace(comparison.rc2.trace),
                normalize_mcs_trace(oracle_trace),
            )
            self.assertEqual(
                normalize_mcs_trace(comparison.z3.trace),
                normalize_mcs_trace(oracle_trace),
            )

    def test_handcrafted_weakly_inconsistent_cases(self):
        self.assert_backends_match_oracle(["(b|a)", "(!b|a)"])
        self.assert_backends_match_oracle(["(b|a)", "(!b|a)", "(c|b)"])

    def test_bounded_exhaustive_small_cases(self):
        for size in (2, 3):
            for selected in combinations(RULE_POOL, size):
                self.assert_backends_match_oracle(list(selected))

    def test_seeded_random_cases(self):
        for seed in range(10, 16):
            rng = random.Random(seed)
            self.assert_backends_match_oracle(rng.sample(RULE_POOL, 4))

    def test_disagreement_artifact_is_replayable(self):
        bb = belief_base(["(b|a)", "(!b|a)"])
        comparison = compare_weak_backends(bb, parse_queries(QUERIES), "system-w")
        with tempfile.TemporaryDirectory() as directory:
            path = comparison.save(directory, seed=17)
            artifact = json.loads(path.read_text())
        self.assertEqual(artifact["seed"], 17)
        self.assertIn("signature", artifact["belief_base"])
        self.assertIn("partition", artifact["rc2"])
        self.assertIn("trace", artifact["rc2"])
        self.assertIn("queries", artifact)

    def test_tseitin_preserves_top_and_bottom(self):
        top = next(iter(parse_queries("(a|Top)").conditionals.values()))
        bottom = next(iter(parse_queries("(Bottom|a)").conditionals.values()))
        self.assertEqual(TseitinTransformation({}).query_to_cnf(top), [[[1]], [[-1]]])
        self.assertEqual(TseitinTransformation({}).query_to_cnf(bottom), [[[]], [[1]]])


class TestRC2MCSContracts(unittest.TestCase):
    @staticmethod
    def optimizer(nf_cnf_dict):
        return OptimizerRC2({"pmaxsat_solver": "rc2", "nf_cnf_dict": nf_cnf_dict})

    def test_empty_mcs(self):
        wcnf = WCNF()
        wcnf.append([1], weight=1)
        result = self.optimizer({1: [[1]]}).minimal_correction_subsets(wcnf)
        self.assertEqual(result, [[]])

    def test_forced_and_duplicate_clause_violations(self):
        wcnf = WCNF()
        wcnf.append([1])
        wcnf.append([2])
        wcnf.append([-1], weight=1)
        wcnf.append([-1], weight=1)  # Same conditional contributes duplicate clauses.
        wcnf.append([-2], weight=1)
        result = self.optimizer({1: [[-1], [-1]], 2: [[-2]]}).minimal_correction_subsets(wcnf)
        self.assertEqual({frozenset(item) for item in result}, {frozenset({1, 2})})

    def test_ignored_indices_are_not_reported(self):
        wcnf = WCNF()
        wcnf.append([1])
        wcnf.append([-1], weight=1)
        result = self.optimizer({1: [[-1]]}).minimal_correction_subsets(wcnf, ignore=[1])
        self.assertEqual(result, [[]])
