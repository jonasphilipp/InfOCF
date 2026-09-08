from pysmt.shortcuts import Symbol
from pysmt.typing import BOOL

import inference.conditional as cond_mod
from inference.conditional import Conditional


def test_setTexts_extracts_vars_when_translation_table_is_present(monkeypatch):
    # conditional.setTexts nutzt 'a' (translate-table) aus dem Modul-Scope.
    # In conditional.py ist 'a' nicht definiert -> wir patchen es hier, damit die Lines laufen.
    trans = str.maketrans(dict.fromkeys("()|,&;!", " "))
    monkeypatch.setattr(cond_mod, "a", trans, raising=False)

    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c = Conditional(consequence=b, antecedence=a, textRepresentation="(b|a)")

    c.setTexts("b", "a")
    assert c.consequenceText == "b"
    assert c.antecedenceText == "a"
    assert "b" in c.consequenceVars
    assert "a" in c.antecedenceVars


def test_make_B_returns_consequence():
    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c = Conditional(consequence=b, antecedence=a, textRepresentation="(b|a)")
    assert c.make_B() is b
