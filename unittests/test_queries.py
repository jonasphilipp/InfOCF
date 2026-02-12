from pysmt.shortcuts import Symbol

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.queries import Queries


def _cond(text: str = "(b|a)") -> Conditional:
    a = Symbol("a")
    b = Symbol("b")
    return Conditional(consequence=b, antecedence=a, textRepresentation=text)


# ---------------------------------------------------------------------------
# Standardfälle
# ---------------------------------------------------------------------------

def test_queries_constructed_from_dict_has_expected_fields():
    q0 = _cond("(b|a)")
    q1 = _cond("(b|a)")

    queries = Queries({0: q0, 1: q1})

    assert queries.name == "from_dict"
    assert queries.conditionals[0] is q0
    assert queries.conditionals[1] is q1
    # Beim Dict-Init wird die Signatur in der aktuellen Implementierung nicht gesetzt
    assert queries.signature == []


def test_queries_constructed_from_belief_base_has_expected_fields():
    bb = BeliefBase(signature=["a", "b"], conditionals={0: _cond()}, name="KB1")

    queries = Queries(bb)

    assert queries.name == "KB1"
    assert queries.signature == ["a", "b"]
    # Aktuelle Implementierung: conditionals wird direkt referenziert (kein Copy)
    assert queries.conditionals is bb.conditionals


# ---------------------------------------------------------------------------
# Randfälle / Robustheit
# ---------------------------------------------------------------------------

def test_queries_empty_dict_is_allowed_and_results_empty_conditionals():
    queries = Queries({})
    assert queries.name == "from_dict"
    assert queries.conditionals == {}
    assert queries.signature == []


def test_queries_invalid_input_keeps_safe_defaults():
    # weder dict noch BeliefBase -> Defaults bleiben erhalten
    queries = Queries(queries=object())  # type: ignore[arg-type]
    assert queries.name == "queries"
    assert queries.signature == []
    assert queries.conditionals == {}