import unittest

from inference.inference_operator import InferenceOperator
from parser.Wrappers import parse_belief_base, parse_queries


def run_case(bb: str, qs: str, expected: list[bool], systems=None):
    if systems is None:
        systems = ["system-z", "system-w", "lex_inf"]
    belief_base = parse_belief_base(bb)
    queries = parse_queries(qs)
    for sys in systems:
        # default variant
        op = InferenceOperator(belief_base, sys, smt_solver="z3", weakly=True)
        res = op.inference(queries)
        actual = res["result"].tolist()
        assert actual == expected, (
            f"System {sys} mismatch. Expected {expected} but got {actual}.\n"
            f"BB: {bb}\nQ: {qs}"
        )
        # z3 pmaxsat variant for systems that support it
        if sys in ["system-w", "lex_inf"]:
            op_z3 = InferenceOperator(
                belief_base, sys, smt_solver="z3", pmaxsat_solver="z3", weakly=True
            )
            res_z3 = op_z3.inference(queries)
            actual_z3 = res_z3["result"].tolist()
            assert actual_z3 == expected, (
                f"System {sys} (z3 variant) mismatch. Expected {expected} but got {actual_z3}.\n"
                f"BB: {bb}\nQ: {qs}"
            )


class TestWeaklyEdgeCases(unittest.TestCase):
    def test_vacuity_impossible_antecedent(self):
        # a is forbidden by last layer → (b|a) must be True
        bb = "signature\n" "a,b\n\n" "conditionals\n" "kb{\n" "(Bottom|a)\n" "}"
        qs = "(b|a)"
        run_case(bb, qs, [True])

    def test_last_layer_implies_consequence(self):
        # Last layer excludes p & ¬j, together with (f|b),(b|p) should entail (!j|p,f,b)
        bb = (
            "signature\n"
            "b,p,f,j\n\n"
            "conditionals\n"
            "kb{\n"
            "(b|p),\n"
            "(f|b),\n"
            "(!f|p),\n"
            "(f|p,j),\n"
            "(Bottom|p,!j)\n"
            "}"
        )
        qs = "(!j|p,f,b)"
        run_case(bb, qs, [True])

    def test_partition_contradiction_vs_knowledge(self):
        # Two contradictory rules on a placed in last layer should still allow unrelated (d|c)
        bb = (
            "signature\n"
            "a,b,c,d\n\n"
            "conditionals\n"
            "kb{\n"
            "(b|a),\n"
            "(!b|a),\n"
            "(d|c)\n"
            "}"
        )
        qs = "(d|c),(d|a,c),(!d|a,c),(!d|c)"
        run_case(bb, qs, [True, True, True, False])

    def test_default_mode_remains_strict(self):
        # Same as first case but in strict mode should treat as inconsistency for inference
        bb = "signature\n" "a,b\n\n" "conditionals\n" "kb{\n" "(Bottom|a)\n" "}"
        qs = parse_queries("(b|a),(a|Top),(Bottom|a)")
        belief_base = parse_belief_base(bb)
        for sys in ["system-z", "system-w", "lex_inf"]:
            with self.assertRaises(AssertionError):
                op = InferenceOperator(belief_base, sys, smt_solver="z3", weakly=False)
                _ = op.inference(qs)


if __name__ == "__main__":
    unittest.main()
