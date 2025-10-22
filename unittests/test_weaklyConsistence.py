"""
Weakly consistency sanity tests.

Purpose
-------
Quick checks that weakly/extended partitioning and consistency behave as expected
for selected belief bases. Intended as sanity checks rather than exhaustive coverage.

Notes
-----
- Focuses on consistency utilities; operator-specific behavior should be covered
  in the CSV-driven and manual weakly tests.

Run
---
uv run pytest -q unittests/test_weaklyConsistence.py
"""

import unittest

from inference.consistency_sat import consistency, consistency_indices
from parser.Wrappers import parse_belief_base


class InferenceCorrectnessTest(unittest.TestCase):
    def test_weakly_inconsistent(self):
        weaklyInconsistentCKB = """
        signature
            a,b,c

        conditionals
        empty{
            (Bottom|Top),
            (Bottom|Top),
            (Bottom|Top),
            (Bottom|Top),
            (Bottom|Top),
            (Bottom|Top),
            (Bottom|Top),
            (Bottom|Top)

        }
        """
        ckb = parse_belief_base(weaklyInconsistentCKB)
        a, b = consistency(ckb, "z3", True)
        ai, bi = consistency_indices(ckb, "z3", True)
        assert a == False
        assert ai == False


if __name__ == "__main__":
    unittest.main()
