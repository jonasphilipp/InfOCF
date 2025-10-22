"""
Benchmark: Incremental c-revision compilation vs full recompute.

Measures compilation time (building vMin/fMin) for a sequence of added
revision conditionals using:

- Full recompute each step: compile_alt_fast(preocf, conds)
- Incremental caches: CRevisionModel.add_conditional + to_compilation()

Notes:
- Uses all-zero CustomPreOCF ranks, gamma vectors not solved here.
- Random seed fixed for reproducibility.
"""

from __future__ import annotations

import random
import statistics
import time
from typing import List, Tuple

from pysmt.shortcuts import Not, Symbol
from pysmt.typing import BOOL

from inference.c_revision import compile_alt_fast
from inference.c_revision_model import CRevisionModel
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF


def make_all_zero_preocf(sig: List[str]) -> CustomPreOCF:
    ranks: dict[str, int | None] = {
        format(i, f"0{len(sig)}b"): 0 for i in range(2 ** len(sig))
    }
    return CustomPreOCF(ranks, signature=sig)


def random_conditional(sig: List[str], idx: int, rng: random.Random) -> Conditional:
    var_a = rng.choice(sig)
    var_b = rng.choice([v for v in sig if v != var_a])
    ante = Symbol(var_a, BOOL)
    cons = Symbol(var_b, BOOL)
    if rng.random() < 0.5:
        ante = Not(ante)
    if rng.random() < 0.5:
        cons = Not(cons)
    cond = Conditional(cons, ante, f"({str(cons)}|{str(ante)})")
    cond.index = idx
    return cond


def build_conditionals(
    sig: List[str], count: int, start: int, rng: random.Random
) -> List[Conditional]:
    return [random_conditional(sig, start + i, rng) for i in range(count)]


def bench_once(
    sig_vars: int, base_count: int, add_count: int, seed: int = 42
) -> Tuple[float, float]:
    # Non-cryptographic PRNG is sufficient for benchmarking; suppress Bandit B311
    rng = random.Random(seed)  # nosec B311
    sig = [chr(ord("a") + i) for i in range(sig_vars)]
    preocf = make_all_zero_preocf(sig)

    base = build_conditionals(sig, base_count, 1, rng)
    added = build_conditionals(sig, add_count, 1 + base_count, rng)

    # Full recompute timings
    full_times: List[float] = []
    conds: List[Conditional] = base[:]
    for cond in added:
        conds.append(cond)
        t0 = time.perf_counter()
        _ = compile_alt_fast(preocf, conds)
        full_times.append(time.perf_counter() - t0)

    # Incremental timings
    incr_times: List[float] = []
    model = CRevisionModel.from_preocf_and_conditionals(preocf, base)
    for cond in added:
        model.add_conditional(cond)
        t0 = time.perf_counter()
        _ = model.to_compilation()
        incr_times.append(time.perf_counter() - t0)

    return sum(full_times), sum(incr_times)


def run_benchmarks():
    configs = [
        (3, 3, 5),
        (4, 4, 8),
        (5, 6, 10),
    ]
    trials = 3

    print("Incremental c-revision compilation benchmark (times in ms)\n")
    print("sig | base | add | full_recompute | incremental | speedup")
    print("----+------+-----+----------------+------------+--------")
    for sig_vars, base_count, add_count in configs:
        full_list: List[float] = []
        incr_list: List[float] = []
        for t in range(trials):
            full_s, incr_s = bench_once(sig_vars, base_count, add_count, seed=100 + t)
            # convert to ms
            full_list.append(full_s * 1000.0)
            incr_list.append(incr_s * 1000.0)
        full_ms = statistics.mean(full_list)
        incr_ms = statistics.mean(incr_list)
        speed = full_ms / incr_ms if incr_ms > 0 else float("inf")
        print(
            f" {sig_vars:>2} | {base_count:>4} | {add_count:>3} | {full_ms:>14.2f} | {incr_ms:>10.2f} | {speed:>6.2f}x"
        )


if __name__ == "__main__":
    run_benchmarks()
