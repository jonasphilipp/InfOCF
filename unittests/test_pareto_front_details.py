import unittest
from pathlib import Path

from inference.c_revision import (
    c_inference_pareto_front,
    c_inference_pareto_front_details,
)
from parser.Wrappers import parse_belief_base


class TestParetoFrontDetails(unittest.TestCase):
    def test_details_match_tuple_front(self):
        examples_root = Path(__file__).resolve().parent.parent / "examples" / "birds"
        belief_base = parse_belief_base(str(examples_root / "kb_birds001.cl"))

        tuple_front = sorted(c_inference_pareto_front(belief_base))
        details = c_inference_pareto_front_details(belief_base)

        detailed_front = sorted(
            tuple(solution["impact_vector"]) for solution in details["solutions"]
        )

        self.assertEqual(details["solution_count"], len(tuple_front))
        self.assertEqual(detailed_front, tuple_front)
        self.assertEqual(
            len(details["conditional_order"]), len(belief_base.conditionals)
        )

        if details["solutions"]:
            first_solution = details["solutions"][0]
            self.assertEqual(
                len(first_solution["impacts"]), len(belief_base.conditionals)
            )
            self.assertIn("label", first_solution)
            self.assertIn("id", first_solution)


if __name__ == "__main__":
    unittest.main()
