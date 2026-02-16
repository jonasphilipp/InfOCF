import pytest
from pysmt.shortcuts import Symbol, Or, TRUE, Not

from inference.preocf import PreOCF
from inference.conditional import Conditional
from inference.c_revision_model import (
    _literal_info,
    _extract_cond_masks,
    CRevisionModel,
)
from inference.c_revision import (
    compile_alt_fast,
    translate_to_csp,
    solve_and_get_model,
)

# ------------------------------
# Eingaben (aus deiner Vorgabe)
# ------------------------------
SIGMA = ["a", "b", "c"]  # Reihenfolge = Bitpositionen

PSI_HUMAN = {
    "abc": 3,
    "ab¬c": 1,
    "a¬bc": 4,
    "a¬b¬c": 3,
    "¬abc": 4,
    "¬ab¬c": 3,
    "¬a¬bc": 2,
    "¬a¬b¬c": 0,
}

def to_bitstring(name: str) -> str:
    # name wie "ab¬c" -> "110" in Reihenfolge SIGMA=["a","b","c"]
    bits = []
    bits.append("1" if "a" in name and "¬a" not in name else ("0" if "¬a" in name else None))
    bits.append("1" if "b" in name and "¬b" not in name else ("0" if "¬b" in name else None))
    bits.append("1" if "c" in name and "¬c" not in name else ("0" if "¬c" in name else None))
    s = "".join(bits)
    assert set(s) <= {"0","1"} and len(s) == 3, f"Ungültiger Weltname: {name} -> {s}"
    return s

PSI_BITS = {to_bitstring(k): v for k, v in PSI_HUMAN.items()}

# Revisions-Konditional: A = a ∨ b als (A | ⊤)
A_FORMULA = Or(Symbol("a"), Symbol("b"))
COND_A_TRUE = Conditional(consequence=A_FORMULA, antecedence=TRUE(), textRepresentation="(a∨b|⊤)")
COND_A_TRUE.index = 1  # eindeutiger Index

# ------------------------------
# Minimal valide PreOCF-Implementierung für Tests
# ------------------------------
class ManualPreOCF(PreOCF):
    """
    PreOCF mit fixen Rängen: erwartet 'ranks' als dict {bitstring: int},
    z.B. {"111": 3, "110": 1, ..., "000": 0}.
    """
    def __init__(self, ranks: dict[str, int], signature: list[str]):
        super().__init__(ranks=ranks, signature=signature, conditionals=None, ranking_system="manual")
        self._ranks = ranks
        self.signature = signature  # sicherstellen, dass Attribut existiert

    def rank_world(self, world_bits) -> int:
        """
        Liefert den Rang κ(ω) für die Welt 'world_bits'.
        'world_bits' ist typischerweise eine Sequenz/Iterable aus {0,1}
        in derselben Reihenfolge wie 'self.signature'.
        """
        bitstr = "".join("1" if int(b) else "0" for b in world_bits)
        return self._ranks[bitstr]

@pytest.fixture(scope="module")
def pre():
    return ManualPreOCF(PSI_BITS, SIGMA)

# ------------------------------
# Tests: Syntax-Splitting
# ------------------------------
def test_literal_info_and_extract_masks():
    a = Symbol("a"); b = Symbol("b")
    # _literal_info
    assert _literal_info(a) == ("a", 1)
    assert _literal_info(Not(a)) == ("a", 0)
    assert _literal_info(Or(a, b)) is None  # kein Literal -> None

    # _extract_cond_masks: nur mit Literal/Literal -> Maske
    cond_lit = Conditional(consequence=b, antecedence=a, textRepresentation="(b|a)")
    cond_lit.index = 42
    sig_index = {v: i for i, v in enumerate(SIGMA)}

    mask = _extract_cond_masks(cond_lit, sig_index)
    assert mask == (sig_index["a"], 1, sig_index["b"], 1)

    # Für (a∨b|⊤) -> Nicht-Literale: None (fällt später auf Welt-Solver zurück)
    mask_none = _extract_cond_masks(COND_A_TRUE, sig_index)
    assert mask_none is None

# ------------------------------
# Tests: Kompilation (Model vs. Referenz)
# ------------------------------
def test_compilation_model_matches_fast(pre):
    # Inkrementelles Modell
    model = CRevisionModel.from_preocf_and_conditionals(pre, [COND_A_TRUE])
    vMin_model, fMin_model = model.to_compilation()

    # Referenz/optimiert
    vMin_fast, fMin_fast = compile_alt_fast(pre, [COND_A_TRUE])

    idx = COND_A_TRUE.index
    assert idx in vMin_model and idx in fMin_model
    assert idx in vMin_fast and idx in fMin_fast

    # Vergleich der Tripellisten (rang, acc_ohne_self, rej_ohne_self), deterministisch sortiert
    def norm(lst):
        return sorted([(r, sorted(acc), sorted(rej)) for (r, acc, rej) in lst])

    assert norm(vMin_model[idx]) == norm(vMin_fast[idx])
    assert norm(fMin_model[idx]) == norm(fMin_fast[idx])

# ------------------------------
# Tests: CSP bauen und lösen
# ------------------------------
def test_translate_to_csp_and_solve(pre):
    model = CRevisionModel.from_preocf_and_conditionals(pre, [COND_A_TRUE])
    compilation = model.to_compilation()

    csp = translate_to_csp(compilation, gamma_plus_zero=False)
    assert isinstance(csp, list) and len(csp) > 0

    m = solve_and_get_model(csp)
    assert m is not None and isinstance(m, dict)

    # Es gibt gamma+_i und gamma-_i Variablen; prüfe auf beide Präfixe
    assert any(k.startswith(("gamma+_", "gamma-_")) for k in m.keys())

# ------------------------------
# Tests: Fallback (Nicht-Literal-Formeln)
# ------------------------------
def test_world_satisfaction_fallback(pre):
    # Welt (0,0,0) verletzt A=a∨b; Welt (1,0,0) erfüllt A
    w000 = "000"; w100 = "100"

    # In w100: A ist wahr, ¬A ist falsch
    assert pre.world_satisfies_conditionalization(w100, COND_A_TRUE.make_A_then_B()) is True
    assert pre.world_satisfies_conditionalization(w100, COND_A_TRUE.make_A_then_not_B()) is False

    # In w000: A ist falsch, ¬A ist wahr
    assert pre.world_satisfies_conditionalization(w000, COND_A_TRUE.make_A_then_B()) is False
    assert pre.world_satisfies_conditionalization(w000, COND_A_TRUE.make_A_then_not_B()) is True