import pytest
from z3 import z3

from inference.tseitin_transformation import TseitinTransformation


def test_expr_to_signed_id_negation_sign_is_consistent():
    tt = TseitinTransformation(epistemic_state={})

    x = z3.Bool("x")
    idx = tt.expr_to_signed_id(x)
    id_not_x = tt.expr_to_signed_id(z3.Not(x))

    assert id_not_x == -idx


def test_goal2intcnf_handles_or_and_unit_literals():
    tt = TseitinTransformation(epistemic_state={})

    x = z3.Bool("x")
    y = z3.Bool("y")

    g = z3.Goal()
    g.add(z3.Or(x, z3.Not(y)))  # OR branch
    g.add(z3.Not(x))           # unit literal branch

    cnf = tt.goal2intcnf(g)

    assert len(cnf) == 2
    assert len(cnf[0]) == 2  # OR -> 2 literals
    assert len(cnf[1]) == 1  # unit -> 1 literal

    # Not(y) should appear as a negative literal somewhere in the OR clause
    assert any(lit < 0 for lit in cnf[0])
