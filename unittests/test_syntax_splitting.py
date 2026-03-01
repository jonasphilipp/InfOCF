# test_syntax_splitting.py
# Benötigt: pytest, pysmt, more-itertools 
import os
import pytest
from pysmt.shortcuts import Symbol, TRUE, And, Or, Not

from inference.conditional import Conditional

# Importiere die zu testenden Funktionen 
from synsplit.split import (
    atoms,
    interpretations,
    interpretation_is_true,
    in_sigma3_only,
    calculate_conditional_syntax_splittings,
    filter_genuine_splittings,
    filter_safe_conditional_syntax_splittings,
    write_output_to_file,
    calc_all_conditional_syntax_splittings,
)


# ------------------------------
# Fixtures / kleine Bausteine
# ------------------------------

@pytest.fixture
def symbols():
    # vier Standardatome
    return Symbol("a"), Symbol("b"), Symbol("c"), Symbol("d"), Symbol("f"), Symbol("g"), Symbol("o"), Symbol("r"), Symbol("s"), Symbol("u")


@pytest.fixture
def cond_a(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (a | ⊤): nutzt ausschließlich Atom 'a'
    cnd = Conditional(consequence=a, antecedence=TRUE(), textRepresentation="(a|⊤)")
    cnd.index = 1
    return cnd


@pytest.fixture
def cond_b(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (b | ⊤): nutzt ausschließlich Atom 'b'
    cnd = Conditional(consequence=b, antecedence=TRUE(), textRepresentation="(b|⊤)")
    cnd.index = 2
    return cnd


@pytest.fixture
def cond_ab(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (a ∨ b | ⊤): Nicht-Literal, nutzt {a,b}
    cnd = Conditional(
        consequence=Or(a, b), antecedence=TRUE(), textRepresentation="(a∨b|⊤)"
    )
    cnd.index = 3
    return cnd

@pytest.fixture
def cond_a_b(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (a | b): Literal, nutzt {a,b}
    cnd = Conditional(
        consequence=a, antecedence=b, textRepresentation="(a|b)"
    )
    cnd.index = 4
    return cnd

@pytest.fixture
def cond_b_c(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (b | c): Literal, nutzt {b,c}
    cnd = Conditional(
        consequence=b, antecedence=c, textRepresentation="(b|c)"
    )
    cnd.index = 5
    return cnd

@pytest.fixture
def cond_nota_c(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (¬a | c): Literal, nutzt {¬a,c}
    cnd = Conditional(
        consequence=Not(a), antecedence=c, textRepresentation="(¬a|c)"
    )
    cnd.index = 6
    return cnd

@pytest.fixture
def cond_d_b(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (d | b): Literal, nutzt {d,b}
    cnd = Conditional(
        consequence=d, antecedence=b, textRepresentation="(d|b)"
    )
    cnd.index = 7
    return cnd

@pytest.fixture
def cond_g_b(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (g | b): Literal, nutzt {g,b}
    cnd = Conditional(
        consequence=g, antecedence=b, textRepresentation="(g|b)"
    )
    cnd.index = 8
    return cnd

@pytest.fixture
def cond_nots_r(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (¬s | r): Literal, nutzt {¬s,r}
    cnd = Conditional(
        consequence=Not(s), antecedence=r, textRepresentation="(¬s|r)"
    )
    cnd.index = 9
    return cnd

@pytest.fixture
def cond_notr_s(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (¬r | s): Literal, nutzt {¬r,s}
    cnd = Conditional(
        consequence=Not(r), antecedence=s, textRepresentation="(¬r|s)"
    )
    cnd.index = 10
    return cnd

@pytest.fixture
def cond_b_sr(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (b | sr): Literal, nutzt {b,s,r}
    cnd = Conditional(
        consequence=b, antecedence=And(s,r), textRepresentation="(b|sr)"
    )
    cnd.index = 11
    return cnd

@pytest.fixture
def cond_u_or(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (u | or): Literal, nutzt {u,o,r}
    cnd = Conditional(
        consequence=u, antecedence=And(o,r), textRepresentation="(u|or)"
    )
    cnd.index = 12
    return cnd

@pytest.fixture
def cond_noto_r(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (¬o | r): Literal, nutzt {¬o,r}
    cnd = Conditional(
        consequence=Not(o), antecedence=r, textRepresentation="(¬o|r)"
    )
    cnd.index = 13
    return cnd

@pytest.fixture
def cond_o_snotr(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (o | s¬r): Literal, nutzt {o,s,¬r}
    cnd = Conditional(
        consequence=o, antecedence=And(s,Not(r)), textRepresentation="(o|s¬r)"
    )
    cnd.index = 14
    return cnd

@pytest.fixture
def cond_notd_a(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (¬d | a): Literal, nutzt {¬d,a}
    cnd = Conditional(
        consequence=Not(d), antecedence=a, textRepresentation="(¬d|a)"
    )
    cnd.index = 15
    return cnd

@pytest.fixture
def cond_c_ab(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (c | ab): Literal, nutzt {c,a,b}
    cnd = Conditional(
        consequence=c, antecedence=And(a,b), textRepresentation="(c|ab)"
    )
    cnd.index = 16
    return cnd

@pytest.fixture
def cond_c_b(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (c | b): Literal, nutzt {c,b}
    cnd = Conditional(
        consequence=c, antecedence=b, textRepresentation="(c|b)"
    )
    cnd.index = 17
    return cnd

@pytest.fixture
def cond_g_c(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (g | c): Literal, nutzt {g,c}
    cnd = Conditional(
        consequence=g, antecedence=c, textRepresentation="(g|c)"
    )
    cnd.index = 18
    return cnd

@pytest.fixture
def cond_f_b(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # (f | b): Literal, nutzt {f,b}
    cnd = Conditional(
        consequence=f, antecedence=b, textRepresentation="(f|b)"
    )
    cnd.index = 19
    return cnd

# ------------------------------
# atoms(): für Conditional & FNode
# ------------------------------

def test_atoms_on_conditional_and_formula(cond_a, cond_ab):
    # Conditional mit nur 'a'
    assert atoms(cond_a) == {"a"}

    # Conditional mit a∨b → Vereinigung {a,b}
    assert atoms(cond_ab) == {"a", "b"}

    # direkt auf FNode (Formel) arbeiten
    assert atoms(cond_ab.consequence) == {"a", "b"}


# ------------------------------
# interpretation_is_true() & interpretations()
# ------------------------------

def test_interpretation_truth(symbols):
    a, b, c, d, f, g, o, r, s, u = symbols
    # A = a ∨ b
    A = Or(a, b)

    # alle Belegungen für {a,b} generieren
    ints = interpretations({"a", "b"})
    # Konsistenz: 4 Interpretationen
    assert len(ints) == 4
    # (a,b) = (False, False) → A=False, sonst True
    table = {(d["a"], d["b"]): interpretation_is_true(A, d) for d in ints}
    assert table[(False, False)] is False
    assert table[(True, False)] is True
    assert table[(False, True)] is True
    assert table[(True, True)] is True


# ------------------------------
# in_sigma3_only()
# ------------------------------

def test_in_sigma3_only_positive_and_negative(cond_a, cond_ab):
    # cond_a nutzt nur 'a'
    assert in_sigma3_only(cond_a, {"a"}) is True
    assert in_sigma3_only(cond_a, {"b"}) is False

    # cond_ab nutzt {a,b}
    assert in_sigma3_only(cond_ab, {"a"}) is False
    assert in_sigma3_only(cond_ab, {"a", "b"}) is True


# ------------------------------
# calculate_conditional_syntax_splittings()
# ------------------------------
""" 
def test_calculate_conditional_syntax_splittings_simple(cond_a, cond_b):
    # Sigma = {a,b}
    sigma = {"a", "b"}
    # Delta enthält genau zwei "disjunkte" Konditionale: eines auf a, eines auf b
    delta = {cond_a, cond_b}

    splittings = calculate_conditional_syntax_splittings(sigma, delta)

    # Erwartung: Es gibt u.a. das „natürliche“ Splitting
    #   sigma3 = ∅, sigma1 = {a}, sigma2 = {b}
    #   delta1 = {(a|⊤)}, delta2 = {(b|⊤)}
    # symmetrische Variante {b}/{a} wird durch Code (Sortier-Check) vermieden
    assert len(splittings) > 0

    # prüfe, dass unser erwartetes Splitting tatsächlich enthalten ist
    found = False
    for sigma3, sigma1, sigma2, delta1, delta2 in splittings:
        if sigma3 == set() and sigma1 == {"a"} and sigma2 == {"b"}:
            if delta1 == {cond_a} and delta2 == {cond_b}:
                found = True
                break
    assert found, "Erwartetes ({a}|{b})-Splitting nicht gefunden."
"""   

# [Heyninck et al. AIII 2023, Example 8]
def test_calculate_conditional_syntax_splittings_simple(cond_c_b, cond_g_c, cond_f_b):
    # Sigma = {b,c,g,f}
    sigma = {"b", "c", "g", "f"}
    # Delta enthält drei Konditionale
    delta = {cond_c_b, cond_g_c, cond_f_b}

    splittings = calculate_conditional_syntax_splittings(sigma, delta)

    #   sigma3 = {b}, sigma1 = {c,g}, sigma2 = {f}
    #   delta1 = {cond_c_b, cond_g_c}, delta2 = {cond_f_b}
    assert len(splittings) > 0

    # prüfe, dass unser erwartetes Splitting tatsächlich enthalten ist
    found = False
    for sigma3, sigma1, sigma2, delta1, delta2 in splittings:
        if sigma3 == {"b"} and sigma1 == {"c", "g"} and sigma2 == {"f"}:
            if delta1 == {cond_c_b, cond_g_c} and delta2 == {cond_f_b}:
                found = True
                break
    assert found, "Erwartetes Bicycle-Splitting (Σ3={b}, Σ1={c,g}, Σ2={f}) nicht gefunden."  


# ------------------------------
# filter_genuine_splittings()
# ------------------------------
"""
def test_filter_genuine_splittings_behaviour(cond_a, cond_b):
    # baue zwei Splittings: eins genuin, eins nicht genuin
    sigma3 = set()
    s1 = {"a"}
    s2 = {"b"}
    genuin = (sigma3, s1, s2, {cond_a}, {cond_b})
    # nicht genuin: delta1 ⊆ delta2
    not_genuin = (sigma3, s1, s2, {cond_a}, {cond_a, cond_b})

    filtered = filter_genuine_splittings([genuin, not_genuin])
    assert genuin in filtered
    assert not_genuin not in filtered
"""

# [Spiegel et al. IJCAI 2025, Example 8] // [Heyninck et al. AIII 2023, Example 8]
def test_filter_genuine_splittings_behaviour(cond_nots_r, cond_notr_s, cond_b_sr, cond_o_snotr, cond_noto_r, cond_u_or, cond_c_b, cond_g_c, cond_f_b):
    # baue zwei Splittings: eins genuin, eins nicht genuin
    # erste Splitting ([Spiegel et al. IJCAI 2025, Example 8]):
    sigma3 = {"s", "r"}
    sigma1 = {"b"}
    sigma2 = {"o", "u"}
    delta1 = {cond_nots_r, cond_notr_s}
    delta2 = {cond_nots_r, cond_notr_s, cond_b_sr, cond_o_snotr, cond_noto_r, cond_u_or}
    # nicht genuin: delta1 ⊆ delta2
    not_genuin = (sigma3, sigma1, sigma2, delta1, delta2)

    # zweite Splitting ([Heyninck et al. AIII 2023, Example 8]):
    sigma3_b = {"b"}
    sigma1_b = {"f"}
    sigma2_b = {"c", "g"}
    delta1_b = {cond_f_b}
    delta2_b = {cond_c_b, cond_g_c}
    # genuin: delta1 \nsubseteq delta2 und delta2 \nsubseteq delta1 
    genuin = (sigma3_b, sigma1_b, sigma2_b, delta1_b, delta2_b)

    filtered = filter_genuine_splittings([genuin, not_genuin])
    assert genuin in filtered
    assert not_genuin not in filtered    


# ------------------------------
# filter_safe_conditional_syntax_splittings()
# ------------------------------

"""
def test_filter_safe_conditional_syntax_splittings_trivial_empty_relevant(cond_a, cond_b):
    sigma3 = {"a", "b"}
    sigma1 = set()
    sigma2 = set()
    delta1 = {cond_a, cond_b}
    delta2 = {cond_a, cond_b}
    splittings = [(sigma3, sigma1, sigma2, delta1, delta2)]

    # generalized=True: Konditionale, die nur in sigma3 liegen, werden ignoriert ⇒ relevant = ∅
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=True)
    assert (sigma3, sigma1, sigma2, delta1, delta2) in safe
"""

# [Spiegel et al. IJCAI 2025, Example 7]
def test_filter_safe_conditional_syntax_splittings_trivial_empty_relevant(cond_nots_r, cond_notr_s, cond_b_sr, cond_g_b, cond_o_snotr, cond_noto_r, cond_u_or):
    sigma3 = {"s", "r"}
    sigma1 = {"b", "g"}
    sigma2 = {"o", "u"}
    delta1 = {cond_nots_r, cond_notr_s, cond_b_sr, cond_g_b}
    delta2 = {cond_nots_r, cond_notr_s, cond_o_snotr, cond_noto_r, cond_u_or}
    splittings = [(sigma3, sigma1, sigma2, delta1, delta2)]

    # generalized=True
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=True)
    assert (sigma3, sigma1, sigma2, delta1, delta2) in safe

    # generalized=False
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=False)
    assert (sigma3, sigma1, sigma2, delta1, delta2) not in safe


# [Heyninck et al. AIII 2023, Example 7]
def test_filter_safe_conditional_syntax_splittings_non_generalized_simple(cond_a_b, cond_b_c, cond_nota_c, cond_d_b):
    # Sigma = {a,b,c,d}, sigma3 = {b}, sigma1={a,c}, sigma2={d}, 
    sigma3 = {"b"}
    sigma1 = {"a","c"}
    sigma2 = {"d"}
    delta1 = {cond_a_b, cond_b_c, cond_nota_c}
    delta2 = {cond_d_b}
    splittings = [(sigma3, sigma1, sigma2, delta1, delta2)]

    # generalized=True
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=True)
    assert (sigma3, sigma1, sigma2, delta1, delta2) in safe

    # generalized=False
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=False)
    assert (sigma3, sigma1, sigma2, delta1, delta2) in safe


# [Heyninck et al. AIII 2023, Example 6]
def test_filter_safe_conditional_syntax_splittings_rejects_non_safe_splitting(cond_d_b, cond_notd_a, cond_c_ab):
    # Sigma = {a,b,c,d}, sigma3 = {a,b}, sigma1={d}, sigma2={c}, 
    sigma3 = {"a","b"}
    sigma1 = {"d"}
    sigma2 = {"c"}
    delta1 = {cond_d_b, cond_notd_a}
    delta2 = {cond_c_ab}
    splittings = [(sigma3, sigma1, sigma2, delta1, delta2)]

    # generalized=True
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=True)
    assert (sigma3, sigma1, sigma2, delta1, delta2) not in safe

    # generalized=False
    safe = filter_safe_conditional_syntax_splittings(splittings, generalized=False)
    assert (sigma3, sigma1, sigma2, delta1, delta2) not in safe    


# ------------------------------
# write_output_to_file()
# ------------------------------

def test_write_output_to_file_creates_file(tmp_path, cond_a, cond_b):
    # 1) Setup: minimal sinnvolle Inputs
    sigma = {"a", "b"}
    sigma3 = set()
    sigma1 = {"a"}
    sigma2 = {"b"}
    cond_splittings = [(sigma3, sigma1, sigma2, {cond_a}, {cond_b})]
    genuine_splittings = [(sigma3, sigma1, sigma2, {cond_a}, {cond_b})]
    safe_splittings = [(sigma3, sigma1, sigma2, {cond_a}, {cond_b})]
    genuine_safe_splittings = [(sigma3, sigma1, sigma2, {cond_a}, {cond_b})]
    generalized_safe_splittings = [(sigma3, sigma1, sigma2, {cond_a}, {cond_b})]
    genuine_generalized_safe_splittings = [(sigma3, sigma1, sigma2, {cond_a}, {cond_b})]

    # 2) in ein temporäres Verzeichnis wechseln, damit das Repo nicht beschrieben wird
    cwd = os.getcwd()
    try:
        os.chdir(tmp_path)

        # 3) Funktion aufrufen
        write_output_to_file(
            sigma,
            {cond_a, cond_b},
            cond_splittings,
            genuine_splittings,
            safe_splittings,
            genuine_safe_splittings,
            generalized_safe_splittings,
            genuine_generalized_safe_splittings,
        )

        # 4) Datei muss existieren
        out_file = tmp_path / "synsplit" / "output" / "splittings_output.txt"
        assert out_file.exists(), "Ausgabedatei wurde nicht erzeugt."

        # 5) Inhalt grob prüfen (Header vorhanden)
        content = out_file.read_text(encoding="utf-8")
        assert "Konditionale Syntax-Splittings:" in content
        assert "Genuine konditionale Syntax-Splittings:" in content
        assert "Sichere konditionale Syntax-Splittings:" in content
        assert "Generalisierte sichere konditionale Syntax-Splittings:" in content
        assert "Genuine generalisierte sichere konditionale Syntax-Splittings:" in content
    finally:
        os.chdir(cwd)


# ------------------------------
# calc_all_conditional_syntax_splittings()
# ------------------------------

def test_calc_all_conditional_syntax_splittings_pipeline(monkeypatch):
    """
    Testet, dass calc_all_conditional_syntax_splittings

    - den Pfad korrekt an parse_belief_base übergibt,
    - aus der zurückgegebenen belief_base korrekt sigma und delta baut,
    - calculate_conditional_syntax_splittings, filter_genuine_splittings und
      filter_safe_conditional_syntax_splittings (mit generalized=True/False) aufruft,
    - und write_output_to_file mit den erwarteten Werten aufruft.
    """
    import synsplit.split as split_mod

    calls = {}

    class DummyBeliefBase:
        def __init__(self):
            self.signature = ["a", "b", "c"]
            self.conditionals = {"c1": "C1", "c2": "C2"}

    def fake_parse_belief_base(path: str):
        calls["parse_path"] = path
        return DummyBeliefBase()

    def fake_calculate_conditional_syntax_splittings(sigma, delta):
        calls["calculate_args"] = (set(sigma), set(delta))
        return [("S3", "S1", "S2", "D1", "D2")]

    def fake_filter_genuine_splittings(splittings):
        calls.setdefault("genuine_args", []).append(list(splittings))
        idx = len(calls["genuine_args"])
        if idx == 1:
            return ["GEN_COND"]
        elif idx == 2:
            return ["GEN_SAFE"]
        else:
            return ["GEN_GEN_SAFE"]

    def fake_filter_safe_conditional_syntax_splittings(splittings, generalized=False):
        calls.setdefault("safe_args", []).append((list(splittings), generalized))
        return ["SAFE_GEN"] if generalized else ["SAFE"]

    def fake_write_output_to_file(
        sigma,
        delta,
        cond_splittings,
        genuine_splittings,
        safe_splittings,
        genuine_safe_splittings,
        generalized_safe_splittings,
        genuine_generalized_safe_splittings,
    ):
        calls["write"] = dict(
            sigma=set(sigma),
            delta=set(delta),
            cond_splittings=cond_splittings,
            genuine_splittings=genuine_splittings,
            safe_splittings=safe_splittings,
            genuine_safe_splittings=genuine_safe_splittings,
            generalized_safe_splittings=generalized_safe_splittings,
            genuine_generalized_safe_splittings=genuine_generalized_safe_splittings,
        )

    monkeypatch.setattr(split_mod, "parse_belief_base", fake_parse_belief_base)
    monkeypatch.setattr(
        split_mod,
        "calculate_conditional_syntax_splittings",
        fake_calculate_conditional_syntax_splittings,
    )
    monkeypatch.setattr(split_mod, "filter_genuine_splittings", fake_filter_genuine_splittings)
    monkeypatch.setattr(
        split_mod,
        "filter_safe_conditional_syntax_splittings",
        fake_filter_safe_conditional_syntax_splittings,
    )
    monkeypatch.setattr(split_mod, "write_output_to_file", fake_write_output_to_file)

    dummy_path = "some/path/to/kb.cl"
    calc_all_conditional_syntax_splittings(dummy_path)

    assert calls["parse_path"] == dummy_path

    calc_sigma, calc_delta = calls["calculate_args"]
    assert calc_sigma == {"a", "b", "c"}
    assert calc_delta == {"C1", "C2"}

    # generalized=False und generalized=True wurden beide genutzt
    assert len(calls["safe_args"]) == 2
    assert calls["safe_args"][0][1] is False
    assert calls["safe_args"][1][1] is True

    write = calls["write"]
    assert write["sigma"] == {"a", "b", "c"}
    assert write["delta"] == {"C1", "C2"}
    assert write["cond_splittings"] == [("S3", "S1", "S2", "D1", "D2")]
    assert write["genuine_splittings"] == ["GEN_COND"]
    assert write["safe_splittings"] == ["SAFE"]
    assert write["genuine_safe_splittings"] == ["GEN_SAFE"]
    assert write["generalized_safe_splittings"] == ["SAFE_GEN"]
    assert write["genuine_generalized_safe_splittings"] == ["GEN_GEN_SAFE"]

def test_main_calls_calc_and_prints_runtime(monkeypatch, capsys):
    import os
    import synsplit.split as split_mod

    calls = {"path": None}

    # Stub: wir wollen NICHT wirklich eine .cl Datei parsen
    def fake_calc_all(cl_file_path):
        calls["path"] = cl_file_path

    # kontrollierte Zeitmessung: 10.0 -> 12.5 => 2.5000 Sekunden
    times = iter([10.0, 12.5])

    def fake_time():
        return next(times)

    monkeypatch.setattr(split_mod, "calc_all_conditional_syntax_splittings", fake_calc_all)
    monkeypatch.setattr(split_mod.time, "time", fake_time)

    # ausführen
    split_mod.main()

    # erwarteter Pfad (genau wie in main zusammengebaut)
    expected_path = os.path.join(
        "examples",
        "AO_Beispiele_Konditionale_KBs",
        "B_Saeugetiere6",
        "KB_Saeugetiere6",
        "kb_Saeugetiere6.cl",
    )
    assert calls["path"] == expected_path

    out = capsys.readouterr().out
    assert "Laufzeit: 2.5000 Sekunden" in out
