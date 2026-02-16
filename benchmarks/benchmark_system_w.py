from __future__ import annotations

import os
import sys
from pathlib import Path
import pytest
from pysmt.shortcuts import Symbol, TRUE

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

from inference.system_w import SystemW
from inference.conditional import Conditional
from inference.belief_base import BeliefBase
from inference.tseitin_transformation import TseitinTransformation

# ---------------------------
# Tuning per Umgebungsvariablen
# ---------------------------
BENCH_ROUNDS = int(os.getenv("BENCH_ROUNDS", "6"))
BENCH_WARMUP = int(os.getenv("BENCH_WARMUP", "1"))
BURST_CALLS  = int(os.getenv("BURST_CALLS", "300"))

# ---------------------------
# Fixtures / Setup
# ---------------------------
@pytest.fixture(scope="module")
def sysw_fixture():
    a = Symbol("a")
    b = Symbol("b")

    c1 = Conditional(consequence=a, antecedence=TRUE(), textRepresentation="(a|⊤)")
    c1.index = 1
    c2 = Conditional(consequence=b, antecedence=TRUE(), textRepresentation="(b|⊤)")
    c2.index = 2

    bb = BeliefBase(signature=["a", "b"], conditionals={1: c1, 2: c2}, name="bench_bb")

    epistemic_state = {
        "belief_base": bb,
        "partition": [[1], [2]],  # zwei Partitionen: nötig für weakly=True (len-2)
        "preprocessing_done": True,
        "preprocessing_time": 0.0,
        "preprocessing_timed_out": False,
        "inference_system": "system_w",
        "weakly": False,
        "smt_solver": "z3",
    }

    t = TseitinTransformation(epistemic_state)
    t.belief_base_to_cnf(v=False, f=False, nf=True)

    sysw = SystemW(epistemic_state)

    def _rec_stub(_hard_constraints, partition_index, _deadline):
        # simple, deterministische Regel:
        # je tiefer die Rekursion (kleinerer partition_index), desto "strenger"
        return partition_index >= 0

    sysw._rec_inference = _rec_stub  # type: ignore[method-assign]
    return sysw, c1  # c1 als Query-Vorlage


# ---------------------------
# Benchmarks
# ---------------------------

@pytest.mark.parametrize("weakly", [False, True], ids=["weaklyFalse", "weaklyTrue"])
def test_systemw_inference_single_call(benchmark, sysw_fixture, weakly):
    sysw, query = sysw_fixture
    benchmark.group = f"system_w-inference-single-{'weak' if weakly else 'strong'}"

    def run():
        return sysw._inference(query=query, weakly=weakly, deadline=None)

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, bool)


@pytest.mark.parametrize("weakly", [False, True], ids=["weaklyFalse", "weaklyTrue"])
def test_systemw_inference_burst(benchmark, sysw_fixture, weakly):
    sysw, query = sysw_fixture
    benchmark.group = f"system_w-inference-burst-{'weak' if weakly else 'strong'}"

    def run():
        acc = 0
        for _ in range(BURST_CALLS):
            acc += int(bool(sysw._inference(query=query, weakly=weakly, deadline=None)))
        return acc

    res = benchmark.pedantic(run, iterations=1, rounds=BENCH_ROUNDS, warmup_rounds=BENCH_WARMUP)
    assert isinstance(res, int)
