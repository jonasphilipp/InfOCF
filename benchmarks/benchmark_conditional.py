# benchmarks/benchmark_conditional.py
# Voraussetzungen:
#   pip install -U pytest pytest-benchmark pysmt
#
# Läufe:
#   uv run pytest -q benchmarks/benchmark_conditional.py --benchmark-only
#   BENCH_ROUNDS=4 BENCH_WARMUP=1 N_OBJECTS=5000 uv run pytest -q --benchmark-only

from __future__ import annotations

import os
import sys
import random
from pathlib import Path
import pytest

# ========= sys.path Bootstrap (damit Imports ohne Installation funktionieren) =========
def _add_project_paths():
    here = Path(__file__).resolve()
    root = None
    for p in [here.parent, *here.parents]:
        if (p / "pyproject.toml").exists():
            root = p
            break
    if root is None:
        root = here.parent.parent

    for c in (root, root / "src", root / "InfOCF"):
        if c.is_dir():
            sys.path.insert(0, str(c.resolve()))

    # falls inference/ als Unterordner liegt: dessen Parent auf sys.path
    try:
        for d in root.rglob("inference"):
            if d.is_dir():
                sys.path.insert(0, str(d.parent.resolve()))
    except Exception:
        pass

_add_project_paths()
# =====================================================================================

from pysmt.shortcuts import Symbol, TRUE, Not, And, Or
from inference.conditional import Conditional


# ---------------------------
# Tuning per Umgebungsvariablen
# ---------------------------
BENCH_ROUNDS = int(os.getenv("BENCH_ROUNDS", "6"))
BENCH_WARMUP = int(os.getenv("BENCH_WARMUP", "1"))

N_OBJECTS = int(os.getenv("N_OBJECTS", "20000"))   # wie viele Conditionals erzeugt/inserted werden
N_VARS = int(os.getenv("N_VARS", "200"))           # Variablenpool
COMPLEX_RATE = float(os.getenv("COMPLEX_RATE", "0.20"))  # Anteil komplexerer Konsequenzen


# ---------------------------
# Helper
# ---------------------------
def _make_symbols(n: int):
    return [Symbol(f"p{i}") for i in range(n)]

def _make_conditionals(n_objects: int, n_vars: int, complex_rate: float, seed: int = 1):
    """
    Erzeugt eine Liste von Conditional-Objekten mit deterministischen Daten.
    Die Konsequenz ist meist ein Symbol (oder Not(Symbol)), manchmal And/Or-Kombis.
    """
    rnd = random.Random(seed)
    syms = _make_symbols(n_vars)

    out: list[Conditional] = []
    for i in range(1, n_objects + 1):
        s = syms[rnd.randrange(n_vars)]
        r = rnd.random()

        if r < complex_rate:
            a = syms[rnd.randrange(n_vars)]
            b = syms[rnd.randrange(n_vars)]
            cons = And(a, Not(b)) if rnd.random() < 0.5 else Or(a, b)
        else:
            cons = s if rnd.random() < 0.7 else Not(s)

        c = Conditional(consequence=cons, antecedence=TRUE(), textRepresentation="(…|⊤)")
        c.index = i
        out.append(c)

    return out


@pytest.fixture(scope="module")
def conditional_list():
    # einmal generieren, dann in mehreren Benchmarks nutzen
    return _make_conditionals(N_OBJECTS, N_VARS, COMPLEX_RATE, seed=1)


# ---------------------------
# Benchmarks
# ---------------------------

def test_conditional_construction(benchmark):
    """
    Misst: reines Erzeugen von Conditional-Objekten.
    """
    benchmark.group = "conditional-construct"

    def run():
        conds = _make_conditionals(N_OBJECTS, N_VARS, COMPLEX_RATE, seed=1)
        return len(conds)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, int) and res == N_OBJECTS


def test_conditional_set_insert(benchmark, conditional_list):
    """
    Misst: Hashing + Set-Insert (wichtig für Performance in eurem Code).
    """
    benchmark.group = "conditional-set-insert"

    def run():
        s = set()
        for c in conditional_list:
            s.add(c)
        return len(s)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, int) and res > 0


def test_conditional_dict_keys(benchmark, conditional_list):
    """
    Misst: Dict-Key-Hashing (Conditional als Key).
    """
    benchmark.group = "conditional-dict-keys"

    def run():
        d = {}
        for c in conditional_list:
            d[c] = c.index
        return len(d)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, int) and res > 0


def test_conditional_equality_pairs(benchmark, conditional_list):
    """
    Misst: viele Equality-Vergleiche.
    Falls Conditional kein __eq__ hat, misst es trotzdem die Objektgleichheit (Baseline).
    """
    benchmark.group = "conditional-eq"

    # vorbereiten: Paare (gleich/ungleich) deterministisch mischen
    pairs = []
    step = max(1, len(conditional_list) // 2000)
    sampled = conditional_list[::step][:2000]  # max ~2000 Paare
    for i, c in enumerate(sampled):
        pairs.append((c, c))  # equal
        if i + 1 < len(sampled):
            pairs.append((c, sampled[i + 1]))  # likely not equal

    def run():
        acc = 0
        for a, b in pairs:
            acc += int(a == b)
        return acc

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, int)


def test_conditional_string_access(benchmark, conditional_list):
    """
    Misst: Zugriff auf textRepresentation 
    """
    benchmark.group = "conditional-textrepr"

    def run():
        total = 0
        for c in conditional_list:
            tr = getattr(c, "textRepresentation", "")
            total += len(tr) if isinstance(tr, str) else 0
        return total

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, int) and res >= 0
