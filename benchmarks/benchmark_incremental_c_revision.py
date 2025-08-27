"""
Benchmark: Incremental c-revision compilation vs full recompute.

Measures compilation time (building vMin/fMin) for a sequence of added
revision conditionals using:

- Full recompute each step: compile_alt_fast(preocf, conds)
- Incremental caches: CRevisionModel.add_conditional + to_compilation()

Upgraded scenarios (kept moderate):
- Defaults close to the original sizes for fair, quick runs
- Optional injection of some complex antecedents (conjunctions) to occasionally
  force solver fallback

Notes:
- Uses all-zero CustomPreOCF ranks; gamma vectors are not solved here.
- Random seed fixed for reproducibility unless overridden.
"""

from __future__ import annotations

import argparse
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
    ranks = {format(i, f"0{len(sig)}b"): 0 for i in range(2 ** len(sig))}
    return CustomPreOCF(ranks, signature=sig)


def random_conditional(
    sig: List[str], idx: int, rng: random.Random, complex_prob: float = 0.0
) -> Conditional:
    """Generate a (possibly) complex conditional.

    - With probability ``complex_prob``, make antecedence a conjunction of two
      distinct variables (optionally negated), which defeats literal-mask
      extraction and forces solver fallback in the compiler.
    - Otherwise, use single-literal A and B (optionally negated), allowing the
      fast mask path.
    """
    var_a = rng.choice(sig)
    var_b = rng.choice([v for v in sig if v != var_a])

    # Consequence is always a single literal (possibly negated)
    cons_sym = Symbol(var_b, BOOL)
    if rng.random() < 0.5:
        cons_sym = Not(cons_sym)

    # Antecedence: either single literal or a conjunction for complexity
    if rng.random() < complex_prob and len(sig) >= 2:
        other = rng.choice([v for v in sig if v != var_a])
        a1 = Symbol(var_a, BOOL)
        a2 = Symbol(other, BOOL)
        if rng.random() < 0.5:
            a1 = Not(a1)
        if rng.random() < 0.5:
            a2 = Not(a2)
        ante = a1 & a2  # complex antecedence
    else:
        ante = Symbol(var_a, BOOL)
        if rng.random() < 0.5:
            ante = Not(ante)

    cond = Conditional(cons_sym, ante, f"({str(cons_sym)}|{str(ante)})")
    cond.index = idx
    return cond


def build_conditionals(
    sig: List[str], count: int, start: int, rng: random.Random, complex_prob: float
) -> List[Conditional]:
    return [
        random_conditional(sig, start + i, rng, complex_prob=complex_prob)
        for i in range(count)
    ]


def bench_once(
    sig_vars: int,
    base_count: int,
    add_count: int,
    *,
    seed: int = 42,
    complex_prob: float = 0.0,
) -> Tuple[float, float]:
    # Non-cryptographic PRNG is sufficient for benchmarking; suppress Bandit B311
    rng = random.Random(seed)  # nosec B311
    sig = [chr(ord("a") + i) for i in range(sig_vars)]
    preocf = make_all_zero_preocf(sig)

    base = build_conditionals(sig, base_count, 1, rng, complex_prob)
    added = build_conditionals(sig, add_count, 1 + base_count, rng, complex_prob)

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
    parser = argparse.ArgumentParser(
        description="Incremental vs full c-revision compilation benchmark"
    )
    parser.add_argument("--trials", type=int, default=3, help="number of trials")
    parser.add_argument(
        "--configs",
        type=str,
        default="5,6,10;6,10,20",
        help=(
            "semicolon-separated triplets sig,base,add; defaults keep hard case at 20 "
            "(e.g. '5,6,10;6,10,20')"
        ),
    )
    parser.add_argument(
        "--complex-prob",
        type=float,
        default=0.2,
        help="probability a conditional uses a complex antecedence",
    )
    parser.add_argument(
        "--seed", type=int, default=100, help="base random seed (per trial offset)"
    )
    args = parser.parse_args()

    # Parse configs
    configs: List[Tuple[int, int, int]] = []
    for chunk in args.configs.split(";"):
        s, b, a = chunk.split(",")
        configs.append((int(s), int(b), int(a)))

    print("Incremental c-revision compilation benchmark (times in ms)\n")
    print(
        f"complex_prob={args.complex_prob:.2f} (higher → more solver fallbacks), trials={args.trials}"
    )
    print("sig | base | add | full_recompute | incremental | speedup")
    print("----+------+-----+----------------+------------+--------")
    for sig_vars, base_count, add_count in configs:
        full_list: List[float] = []
        incr_list: List[float] = []
        for t in range(args.trials):
            full_s, incr_s = bench_once(
                sig_vars,
                base_count,
                add_count,
                seed=args.seed + t,
                complex_prob=args.complex_prob,
            )
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
