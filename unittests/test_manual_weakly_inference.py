"""
Manual weakly-semantics checks.

Purpose
-------
Validate edge-case behavior for weakly/extended semantics across systems.

How to add cases
----------------
Use `run_case(belief_base_str, queries_str, expected, systems=None)`:
- belief_base_str / queries_str: inline belief base and queries text
- expected: list[bool] aligned to the order of queries in `queries_str`
- systems: defaults to ["system-z", "system-w", "lex_inf"]; z3 variants
  are also exercised where available via pmaxsat selection

Semantics
---------
weakly=True (extended). SMT solver is z3.

Run
---
uv run pytest -q unittests/test_manual_weakly_inference.py
"""

import unittest

from inference.inference_manager import InferenceManager
from parser.Wrappers import parse_belief_base, parse_queries


def run_case(
    belief_base_str: str,
    queries_str: str,
    expected: list[bool],
    systems: list[str] | None = None,
):
    if systems is None:
        systems = [
            "system-z",
            "system-w",
            "lex_inf",
            # Exercise z3 variants where available via pmaxsat selection in operator:
            # We trigger z3 variants by passing pmaxsat_solver="z3" through InferenceManager API.
        ]

    belief_base = parse_belief_base(belief_base_str)
    queries = parse_queries(queries_str)

    for system in systems:
        # default variant
        manager = InferenceManager(
            belief_base, inference_system=system, smt_solver="z3", weakly=True
        )
        results = manager.inference(queries)
        actual = results["result"].tolist()
        assert actual == expected, (
            f"System {system} mismatch. Expected {expected} but got {actual}.\n"
            f"Belief base: {belief_base_str}\nQueries: {queries_str}"
        )
        # z3 pmaxsat variant where meaningful (system-w and lex_inf)
        if system in ["system-w", "lex_inf"]:
            manager_z3 = InferenceManager(
                belief_base,
                inference_system=system,
                smt_solver="z3",
                pmaxsat_solver="z3",
                weakly=True,
            )
            results_z3 = manager_z3.inference(queries)
            actual_z3 = results_z3["result"].tolist()
            assert actual_z3 == expected, (
                f"System {system} (z3 variant) mismatch. Expected {expected} but got {actual_z3}.\n"
                f"Belief base: {belief_base_str}\nQueries: {queries_str}"
            )


class TestManualWeaklyInference(unittest.TestCase):
    def test_delta1(self):
        # Δ1 = { (Bottom | a) }
        bb = "signature\na,b\n\nconditionals\ndelta1{\n(Bottom|a)\n}"
        qs = "(b|a),(a|Top),(Bottom|a)"
        expected = [True, False, True]
        run_case(bb, qs, expected)

    def test_delta2(self):
        # Δ2 = { (b|a), (!b|a) }
        bb = "signature\na,b\n\nconditionals\ndelta2{\n(b|a),\n(!b|a)\n}"
        qs = "(b|a),(a|Top),(Bottom|a)"
        expected = [True, False, True]
        run_case(bb, qs, expected)

    def test_delta3(self):
        # Δ3 = { (b|a), (!b|a), (d|c) }
        bb = "signature\na,b,c,d\n\nconditionals\ndelta3{\n(b|a),\n(!b|a),\n(d|c)\n}"
        qs = "(d|c),(d|a,c),(!d|a,c),(!d|c)"
        expected = [True, True, True, False]
        run_case(bb, qs, expected)

    def test_delta4(self):
        # Δ4 = { (b|p), (f|b), (!f|p), (f|p,j), (Bottom|p,!j) }
        bb = (
            "signature\n"
            "b,p,f,j\n\n"
            "conditionals\n"
            "delta4{\n"
            "(b|p),\n"
            "(f|b),\n"
            "(!f|p),\n"
            "(f|p,j),\n"
            "(Bottom|p,!j)\n"
            "}"
        )
        # Queries and expected results
        qs = "(f|b),(Bottom|p)"
        expected = [True, True]
        run_case(bb, qs, expected)

    def test_delta5(self):
        # Δ5 = { (b|p), (f|b), (!f|p), (f|p,j), (Bottom|p,b,f,j) }
        bb = (
            "signature\n"
            "b,p,f,j\n\n"
            "conditionals\n"
            "delta5{\n"
            "(b|p),\n"
            "(f|b),\n"
            "(!f|p),\n"
            "(f|p,j),\n"
            "(Bottom|p,b,f,j)\n"
            "}"
        )
        # Queries and expected results
        qs = "(!j|p,f,b)"
        expected = [True]
        run_case(bb, qs, expected)


if __name__ == "__main__":
    unittest.main()
