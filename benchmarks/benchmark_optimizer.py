# benchmarks/benchmark_optimizer.py
# Voraussetzungen:
#   pip install -U pytest pytest-benchmark python-sat[pblib,aiger]
#
# Läufe:
#   uv run pytest -q benchmarks/benchmark_optimizer.py --benchmark-only
#   BENCH_ROUNDS=4 BENCH_WARMUP=1 uv run pytest -q --benchmark-only
#
# Gemessene Targets (inference/optimizer.py):
#   - remove_supersets
#   - Optimizer.get_violated_conditional
#   - Optimizer.exclude_violated
#   - OptimizerRC2.minimal_correction_subsets  (RC2 Start/Compute Overhead)

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

from pysat.card import IDPool
from pysat.formula import WCNF

from inference.deadline import Deadline
from inference.optimizer import OptimizerRC2, remove_supersets


# ---------------------------
# Tuning per Umgebungsvariablen
# ---------------------------
BENCH_ROUNDS = int(os.getenv("BENCH_ROUNDS", "6"))
BENCH_WARMUP = int(os.getenv("BENCH_WARMUP", "1"))

# Größensteuerung
N_SETS = int(os.getenv("N_SETS", "400"))                 # remove_supersets workload
SET_UNIVERSE = int(os.getenv("SET_UNIVERSE", "120"))     # Element-Range in Sets

N_COND = int(os.getenv("N_COND", "60"))                  # nf_cnf_dict Größe
CLAUSES_PER_COND = int(os.getenv("CLAUSES_PER_COND", "3"))
LITS_PER_CLAUSE = int(os.getenv("LITS_PER_CLAUSE", "3"))

RC2_HARD_CLAUSES = int(os.getenv("RC2_HARD_CLAUSES", "30"))
RC2_VARS = int(os.getenv("RC2_VARS", "40"))


# ---------------------------
# Helper: Testdaten
# ---------------------------
def _make_sets_with_supersets(n_sets: int, universe: int, seed: int = 1) -> list[set[int]]:
    """
    Erzeugt viele Sets mit absichtlich eingebauten Supersets.
    remove_supersets ist O(n^2) in der Anzahl Sets → n_sets steuert Laufzeit.
    """
    rnd = random.Random(seed)
    base = []
    for _ in range(n_sets):
        k = rnd.randint(1, 10)
        s = set(rnd.randrange(universe) for _ in range(k))
        base.append(s)

    # baue absichtlich Supersets: jedes 5. Set wird ein Superset von einem früheren
    for i in range(0, n_sets, 5):
        if i >= 3:
            base[i] = set(base[i - 3]) | {rnd.randrange(universe), rnd.randrange(universe)}
    return base


def _make_epistemic_state_with_nf_cnf_dict(
    n_cond: int,
    clauses_per_cond: int,
    lits_per_clause: int,
    n_vars: int,
    seed: int = 2,
) -> dict[str, object]:
    rnd = random.Random(seed)
    pool = IDPool()
    nf_cnf_dict: dict[int, list[list[int]]] = {}

    for idx in range(1, n_cond + 1):
        cnf: list[list[int]] = []
        for _ in range(clauses_per_cond):
            clause = []
            for _ in range(lits_per_clause):
                v = rnd.randint(1, n_vars)
                lit = v if rnd.random() < 0.5 else -v
                clause.append(lit)
            cnf.append(clause)
        nf_cnf_dict[idx] = cnf

    return {
        "pool": pool,
        "nf_cnf_dict": nf_cnf_dict,
        # optional: pmaxsat_solver steuert RC2-Backend 
        "pmaxsat_solver": "rc2g3",
    }


def _make_model(n_vars: int, seed: int = 3) -> list[int]:
    """Erzeugt ein simples SAT-Model: für jede Variable entweder +i oder -i."""
    rnd = random.Random(seed)
    return [i if rnd.random() < 0.5 else -i for i in range(1, n_vars + 1)]


def _make_trivial_wcnf(n_vars: int, n_hard: int, seed: int = 4) -> WCNF:
    rnd = random.Random(seed)
    w = WCNF()
    for _ in range(n_hard):
        clause = []
        for _ in range(3):
            v = rnd.randint(1, n_vars)
            clause.append(v if rnd.random() < 0.5 else -v)
        w.append(clause)  
    return w


@pytest.fixture(scope="module")
def sets_workload():
    return _make_sets_with_supersets(N_SETS, SET_UNIVERSE, seed=1)


@pytest.fixture(scope="module")
def optimizer_state():
    # n_vars bewusst etwas größer als N_COND, um Vielfalt zu haben
    return _make_epistemic_state_with_nf_cnf_dict(
        n_cond=N_COND,
        clauses_per_cond=CLAUSES_PER_COND,
        lits_per_clause=LITS_PER_CLAUSE,
        n_vars=max(20, N_COND),
        seed=2,
    )


@pytest.fixture(scope="module")
def optimizer_obj(optimizer_state):
    return OptimizerRC2(optimizer_state)


@pytest.fixture(scope="module")
def model_and_cost():
    n_vars = max(20, N_COND)
    model = _make_model(n_vars=n_vars, seed=3)
    # cost steuert, wie viele Violations get_violated_conditional “früh” sammeln will
    cost = 10
    return model, cost


@pytest.fixture(scope="module")
def trivial_wcnf():
    return _make_trivial_wcnf(n_vars=RC2_VARS, n_hard=RC2_HARD_CLAUSES, seed=4)


# ---------------------------
# Benchmarks
# ---------------------------

def test_remove_supersets_benchmark(benchmark, sets_workload):
    benchmark.group = "optimizer-remove_supersets"

    def run():
        return remove_supersets(sets_workload)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, list)


def test_get_violated_conditional_benchmark(benchmark, optimizer_obj, model_and_cost):
    """
    Misst Optimizer.get_violated_conditional() 
    """
    model, cost = model_and_cost
    benchmark.group = "optimizer-get_violated"

    def run():
        return optimizer_obj.get_violated_conditional(model=model, cost=cost, ignore=[])

    violated = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(violated, set)


def test_exclude_violated_benchmark(benchmark, optimizer_obj):
    """
    Misst Optimizer.exclude_violated() 
    """
    benchmark.group = "optimizer-exclude_violated"

    violated = set(range(1, min(N_COND, 20) + 1))

    def run():
        return optimizer_obj.exclude_violated(violated)

    constraints = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(constraints, list) and constraints
