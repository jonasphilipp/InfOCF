# benchmarks/benchmark_consistency_sat.py
# Voraussetzungen:
#   pip install -U pytest pytest-benchmark pysmt
#
# Läufe:
#   uv run pytest -q benchmarks/benchmark_consistency_sat.py --benchmark-only
#   BENCH_ROUNDS=4 BENCH_WARMUP=1 MAX_COND=40 uv run pytest -q --benchmark-only
#
# Diese Benchmarks messen primär:
#   - inference.consistency_sat.consistency(...)
#   - inference.consistency_sat.consistency_indices(...)

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

    try:
        for d in root.rglob("inference"):
            if d.is_dir():
                sys.path.insert(0, str(d.parent.resolve()))
    except Exception:
        pass

_add_project_paths()
# =====================================================================================

from pysmt.shortcuts import Symbol, TRUE, Not
from inference.conditional import Conditional
from inference.belief_base import BeliefBase
from inference.consistency_sat import consistency, consistency_indices


# ---------------------------
# Tuning per Umgebungsvariablen
# ---------------------------
BENCH_ROUNDS = int(os.getenv("BENCH_ROUNDS", "6"))
BENCH_WARMUP = int(os.getenv("BENCH_WARMUP", "1"))

# MAX_COND hält das Ganze im Zaum – consistency() macht viele solver calls
MAX_COND = int(os.getenv("MAX_COND", "40"))  # Default bewusst moderat

# ---------------------------
# Helper: BeliefBases generieren
# ---------------------------
def _make_belief_base(n_vars: int, n_conds: int, seed: int, make_unsat: bool) -> BeliefBase:
    """
    Baut eine BeliefBase mit n_conds Conditionals.
    """
    rnd = random.Random(seed)
    n_conds = min(n_conds, MAX_COND)

    vars_ = [Symbol(f"p{i}") for i in range(n_vars)]
    signature = [f"p{i}" for i in range(n_vars)]

    conds: dict[int, Conditional] = {}
    idx = 1

    # viele "einfache" Regeln (p | ⊤) oder (¬p | ⊤)
    # Das erzeugt solver-lastige Arbeit, bleibt aber kontrollierbar.
    for _ in range(max(0, n_conds - (2 if make_unsat else 0))):
        v = vars_[rnd.randrange(n_vars)]
        cons = v if rnd.random() < 0.7 else Not(v)  # etwas mehr positive Literale
        c = Conditional(consequence=cons, antecedence=TRUE(), textRepresentation="(…|⊤)")
        c.index = idx
        conds[idx] = c
        idx += 1

    # Wenn unsat: füge p0 und ¬p0 sicher hinzu
    if make_unsat:
        p0 = vars_[0]
        c_pos = Conditional(consequence=p0, antecedence=TRUE(), textRepresentation="(p0|⊤)")
        c_pos.index = idx
        conds[idx] = c_pos
        idx += 1

        c_neg = Conditional(consequence=Not(p0), antecedence=TRUE(), textRepresentation="(¬p0|⊤)")
        c_neg.index = idx
        conds[idx] = c_neg
        idx += 1

    return BeliefBase(signature=signature, conditionals=conds, name="bench_bb")


@pytest.fixture(scope="module")
def bbs():
    """
    Ein paar feste Workloads:
      - sat small/medium
      - unsat small/medium
    """
    return {
        "sat_small": _make_belief_base(n_vars=12, n_conds=15, seed=1, make_unsat=False),
        "sat_medium": _make_belief_base(n_vars=25, n_conds=35, seed=2, make_unsat=False),
        "unsat_small": _make_belief_base(n_vars=12, n_conds=15, seed=3, make_unsat=True),
        "unsat_medium": _make_belief_base(n_vars=25, n_conds=35, seed=4, make_unsat=True),
    }


# ---------------------------
# Benchmarks: consistency()
# ---------------------------
@pytest.mark.parametrize("weakly", [False, True], ids=["weaklyFalse", "weaklyTrue"])
@pytest.mark.parametrize("case", ["sat_small", "sat_medium", "unsat_small", "unsat_medium"])
def test_consistency_sat(benchmark, bbs, weakly, case):
    """
    Benchmark für inference.consistency_sat.consistency().
    """
    bb = bbs[case]
    benchmark.group = f"consistency-{case}-{'weak' if weakly else 'strong'}"

    def run():
        return consistency(bb, solver="z3", weakly=weakly)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)

    # Sanity: Return ist entweder False oder (partition, stats)
    assert res is False or (isinstance(res, tuple) and len(res) == 2)


# ---------------------------
# Benchmarks: consistency_indices()
# ---------------------------
@pytest.mark.parametrize("weakly", [False, True], ids=["weaklyFalse", "weaklyTrue"])
@pytest.mark.parametrize("case", ["sat_small", "sat_medium", "unsat_small", "unsat_medium"])
def test_consistency_indices_sat(benchmark, bbs, weakly, case):
    """
    Benchmark für inference.consistency_sat.consistency_indices().
    """
    bb = bbs[case]
    benchmark.group = f"consistency_indices-{case}-{'weak' if weakly else 'strong'}"

    def run():
        return consistency_indices(bb, solver="z3", weakly=weakly)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert res is False or (isinstance(res, tuple) and len(res) == 2)
