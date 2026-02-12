import pytest
from pysmt.shortcuts import Symbol, TRUE, Or

import os

BENCH_ROUNDS = int(os.getenv("BENCH_ROUNDS", "6"))
BENCH_WARMUP = int(os.getenv("BENCH_WARMUP", "1"))
MICRO_BATCH_CASES = int(os.getenv("MICRO_BATCH_CASES", "80"))
MAX_N_ATOMS = int(os.getenv("MAX_N_ATOMS", "8"))           # für calc_scaling_atoms 
MAX_N_ATOMS_PIPE = int(os.getenv("MAX_N_ATOMS_PIPE", "4")) # für pipeline_matrix

from synsplit.split import (
    calculate_conditional_syntax_splittings,
    filter_genuine_splittings,
    filter_safe_conditional_syntax_splittings,
)
from inference.conditional import Conditional


# ------------------------------
# Testdaten 
# ------------------------------

def _symbols():
    a = Symbol("a")
    b = Symbol("b")
    c = Symbol("c")
    return a, b, c

def _cond_a():
    a, b, c = _symbols()
    cnd = Conditional(consequence=a, antecedence=TRUE(), textRepresentation="(a|⊤)")
    cnd.index = 1
    return cnd

def _cond_b():
    a, b, c = _symbols()
    cnd = Conditional(consequence=b, antecedence=TRUE(), textRepresentation="(b|⊤)")
    cnd.index = 2
    return cnd

def _cond_ab():
    a, b, c = _symbols()
    cnd = Conditional(consequence=Or(a, b), antecedence=TRUE(), textRepresentation="(a∨b|⊤)")
    cnd.index = 3
    return cnd


# ------------------------------
# Benchmarks
# ------------------------------

@pytest.mark.parametrize(
    "label,sigma,delta",
    [
        (
            "tiny-2atoms-2conds",
            {"a", "b"},
            {_cond_a(), _cond_b()},
        ),
        (
            "small-2atoms-3conds",
            {"a", "b"},
            {_cond_a(), _cond_b(), _cond_ab()},
        ),
    ],
    ids=lambda p: p[0] if isinstance(p, tuple) else str(p),
)
def test_calculate_conditional_syntax_splittings(benchmark, label, sigma, delta):
    """
    Misst die Laufzeit der Berechnung der konditionalen Syntax-Splittings
    für kleine, aber repräsentative Eingaben.
    """
    benchmark.group = f"calc-splittings-{label}"

    def run():
        return list(calculate_conditional_syntax_splittings(sigma, delta))

    result = benchmark.pedantic(run, iterations=1, rounds=15, warmup_rounds=2)
    # Sanity: Ergebnis ist iterierbar / nicht leer in Standardfällen
    assert isinstance(result, list)


@pytest.mark.parametrize(
    "label,sigma,delta,generalized",
    [
        ("pipeline-tiny-generalized-false", {"a", "b"}, {_cond_a(), _cond_b()}, False),
        ("pipeline-tiny-generalized-true", {"a", "b"}, {_cond_a(), _cond_b()}, True),
        ("pipeline-small-generalized-true", {"a", "b"}, {_cond_a(), _cond_b(), _cond_ab()}, True),
    ],
    ids=lambda p: p[0] if isinstance(p, tuple) else str(p),
)
def test_filter_pipeline(benchmark, label, sigma, delta, generalized):
    """
    Misst die komplette Pipeline:
      calculate_conditional_syntax_splittings → filter_genuine_splittings → filter_safe_conditional_syntax_splittings
    """
    benchmark.group = f"pipeline-{label}"

    # Vorbereitung außerhalb der Messung? Nein: Wir wollen hier die End-to-End-Kosten messen.
    def run():
        splittings = list(calculate_conditional_syntax_splittings(sigma, delta))
        genuine = list(filter_genuine_splittings(splittings))
        safe = list(filter_safe_conditional_syntax_splittings(splittings, generalized=generalized))
        # etwas Arbeit mit den Ergebnissen, damit nichts wegoptimiert wird
        return len(splittings), len(genuine), len(safe)

    result = benchmark.pedantic(run, iterations=1, rounds=20, warmup_rounds=2)
    assert isinstance(result, tuple) and len(result) == 3

from itertools import combinations

def _mk_atoms_and_conditionals(n: int, seed: int = 1):
    # baue Strings und korrespondierende pysmt-Symbole
    names = [f"p{i}" for i in range(n)]
    syms = [Symbol(name) for name in names]
    sigma = set(names)

    delta = set()

    # Einfache Konditionale
    for idx, s in enumerate(syms, start=1):
        cnd = Conditional(consequence=s, antecedence=TRUE(), textRepresentation=f"({s.symbol_name()}|⊤)")
        cnd.index = idx
        delta.add(cnd)

    # Einige OR-Kombinationen
    next_index = len(delta) + 1
    for (i, j) in list(combinations(range(n), 2))[: max(0, n - 1)]:
        disj = Or(syms[i], syms[j])
        cnd = Conditional(consequence=disj, antecedence=TRUE(),
                          textRepresentation=f"({syms[i].symbol_name()}∨{syms[j].symbol_name()}|⊤)")
        cnd.index = next_index
        next_index += 1
        delta.add(cnd)

    return sigma, delta


# ---------------------------------------------------------------------
# Skalierung
# ---------------------------------------------------------------------
@pytest.mark.parametrize(
    "label,n_atoms",
    [("n2", 2), ("n4", 4), ("n8", 8)],
)
def test_calc_scaling_atoms(benchmark, label, n_atoms):
    """
    Misst die Kosten von calculate_conditional_syntax_splittings bei wachsender Problemgröße.
    """
    sigma, delta = _mk_atoms_and_conditionals(n_atoms)
    benchmark.group = f"synsplit-calc-scale-{label}"

    def run():
        return list(calculate_conditional_syntax_splittings(sigma, delta))

    res = benchmark.pedantic(run, iterations=1, rounds=12, warmup_rounds=2)
    assert isinstance(res, list)


# ---------------------------------------------------------------------
# Pipeline-Matrix
# ---------------------------------------------------------------------
PIPE_SIZES = [("n2", 2), ("n4", 4)]
if MAX_N_ATOMS_PIPE >= 6:
    PIPE_SIZES.append(("n6", 6))
if MAX_N_ATOMS_PIPE >= 8:
    PIPE_SIZES.append(("n8", 8))

@pytest.mark.parametrize("gen", [False, True], ids=["genFalse", "genTrue"])
@pytest.mark.parametrize("label,n_atoms", PIPE_SIZES)
def test_pipeline_matrix(benchmark, gen, label, n_atoms):
    sigma, delta = _mk_atoms_and_conditionals(n_atoms)
    benchmark.group = f"synsplit-e2e-{label}-{'genT' if gen else 'genF'}"

    # n8 ist schwer → separat drosseln
    rounds = 4 if n_atoms >= 8 else BENCH_ROUNDS
    warmup = 1 if n_atoms >= 8 else BENCH_WARMUP

    def run():
        spl = list(calculate_conditional_syntax_splittings(sigma, delta))
        genuine = list(filter_genuine_splittings(spl))
        safe = list(filter_safe_conditional_syntax_splittings(splittings=spl, generalized=gen))
        return len(spl), len(genuine), len(safe)

    res = benchmark.pedantic(run, iterations=1, rounds=rounds, warmup_rounds=warmup)
    assert isinstance(res, tuple) and len(res) == 3


# ---------------------------------------------------------------------
# Micro-Batch
# ---------------------------------------------------------------------
def test_micro_batch_many_small_instances(benchmark):
    cases = [_mk_atoms_and_conditionals(3, seed=10 + i) for i in range(300)]
    benchmark.group = "synsplit-micro-batch-300x-small"

    def run():
        out = 0
        for sigma, delta in cases:
            spl = list(calculate_conditional_syntax_splittings(sigma, delta))
            out += len(spl)
        return out

    res = benchmark.pedantic(run, iterations=1, rounds=12, warmup_rounds=2)
    assert isinstance(res, int) and res >= 0    