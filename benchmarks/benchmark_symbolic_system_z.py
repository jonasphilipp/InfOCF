from __future__ import annotations

import argparse
from pathlib import Path
from time import perf_counter

from inference.belief_base import BeliefBase
from inference.consistency_sat import consistency
from inference.preocf import PreOCF
from parser.Wrappers import parse_belief_base

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_REAL_BENCHMARK_CASES = [
    REPO_ROOT / "examples" / "random_large" / "randomTest_10_10_0.cl",
    REPO_ROOT / "examples" / "random_large" / "randomTest_12_12_50.cl",
]
EXTENDED_REAL_BENCHMARK_CASES = [
    REPO_ROOT / "examples" / "random_large" / "randomTest_14_14_14.cl",
    REPO_ROOT / "examples" / "random_large" / "randomTest_16_16_3.cl",
]


def build_synthetic_belief_base() -> BeliefBase:
    """Build a System Z example with extra irrelevant variables.

    The extra signature symbols create larger world cubes without changing the
    logical structure of the rules, which is useful for comparing symbolic
    grouping against world-by-world ranking.
    """

    kb_string = """
signature
   a, b, c, d, e, f, g, h

conditionals
symbolic_bench{
   (b | a),
   (!c | b),
   (d | c),
   (!e | d)
}
"""
    parsed = parse_belief_base(kb_string)
    return BeliefBase(parsed.signature, parsed.conditionals, "symbolic_bench")


def load_real_belief_base(path: Path) -> BeliefBase:
    """Load a benchmark belief base from a real `.cl` example file."""

    parsed = parse_belief_base(str(path))
    return BeliefBase(parsed.signature, parsed.conditionals, path.stem)


def benchmark_belief_base(belief_base: BeliefBase, label: str) -> None:
    """Benchmark classic and symbolic System Z paths for one belief base."""

    total_worlds = 2 ** len(belief_base.signature)

    start = perf_counter()
    partition, stats = consistency(belief_base, weakly=False)
    consistency_ms = (perf_counter() - start) * 1000.0

    start = perf_counter()
    empty_ranks = PreOCF.create_bitvec_world_dict(belief_base.signature)
    ranks_dict_ms = (perf_counter() - start) * 1000.0

    start = perf_counter()
    classic = PreOCF.init_system_z(belief_base)
    init_ms = (perf_counter() - start) * 1000.0

    start = perf_counter()
    classic.compute_all_ranks()
    classic_ms = (perf_counter() - start) * 1000.0

    symbolic = PreOCF.init_system_z(belief_base)
    start = perf_counter()
    buckets = symbolic.symbolic_rank_buckets()
    bucket_build_ms = (perf_counter() - start) * 1000.0

    start = perf_counter()
    symbolic.materialize_ranks_from_buckets()
    symbolic_ms = (perf_counter() - start) * 1000.0

    print(f"=== {label} ===")
    print(f"Belief base: {belief_base.name}")
    print(f"Signature size: {len(belief_base.signature)} vars -> {total_worlds} worlds")
    print(f"Conditionals: {len(belief_base.conditionals)}")
    print(f"Raw consistency(): {consistency_ms:.2f} ms")
    print(f"Eager ranks dict creation: {ranks_dict_ms:.2f} ms")
    print(f"init_system_z(): {init_ms:.2f} ms")
    print(
        f"Approx init overhead beyond consistency: {max(0.0, init_ms - consistency_ms):.2f} ms"
    )
    print(f"Prebuilt ranks entries: {len(empty_ranks)}")
    print(f"Partition stats from consistency(): {stats[0]}")
    print(f"Partition layer sizes: {symbolic.partition_layer_sizes()}")
    print(f"Symbolic bucket count: {len(buckets)}")
    print(f"Classic compute_all_ranks() after init: {classic_ms:.2f} ms")
    print(f"Build symbolic buckets: {bucket_build_ms:.2f} ms")
    print(f"Materialize via symbolic buckets after init: {symbolic_ms:.2f} ms")
    print(f"Ranks identical: {classic.ranks == symbolic.ranks}")
    print()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark classic vs symbolic System Z ranking."
    )
    parser.add_argument(
        "--extended",
        action="store_true",
        help="Include slower 14/16-variable real benchmark files.",
    )
    return parser.parse_args()


def run_benchmark(include_extended: bool = False) -> None:
    benchmark_belief_base(
        build_synthetic_belief_base(), "System Z symbolic benchmark (synthetic)"
    )

    real_cases = list(DEFAULT_REAL_BENCHMARK_CASES)
    if include_extended:
        real_cases.extend(EXTENDED_REAL_BENCHMARK_CASES)

    for path in real_cases:
        benchmark_belief_base(
            load_real_belief_base(path),
            f"System Z symbolic benchmark (real file: {path.name})",
        )


if __name__ == "__main__":
    args = parse_args()
    run_benchmark(include_extended=args.extended)
