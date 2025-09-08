from __future__ import annotations

from time import perf_counter

from pysmt.shortcuts import And, Not, Symbol
from pysmt.typing import BOOL

from inference.belief_base import BeliefBase
from inference.c_revision import compile_alt_fast
from inference.conditional import Conditional
from inference.preocf import PreOCF, SystemZPreOCF


class CountingSystemZPreOCF(SystemZPreOCF):
    """System Z PreOCF that counts rank lookups and actual computations.

    - rank_calls: total invocations of rank_world (including cached reads)
    - compute_calls: number of times a rank is actually computed (cache miss or force)
    """

    def __init__(self, belief_base: BeliefBase, signature: list[str] | None = None):
        # Ensure we pass a concrete list to the parent to satisfy type checkers
        sig_for_parent: list[str] = (
            belief_base.signature if signature is None else signature
        )
        super().__init__(belief_base, sig_for_parent)
        self.rank_calls: int = 0
        self.compute_calls: int = 0

    def rank_world(self, world: str, force_calculation: bool = False) -> int:  # type: ignore[override]
        self.rank_calls += 1
        # Count only real computations (cache miss or explicit force)
        if force_calculation or self.ranks[world] is None:
            self.compute_calls += 1
        return super().rank_world(world, force_calculation)


def build_revision_conditionals(signature: list[str]) -> list[Conditional]:
    """Create a small set of revision conditionals with a rare antecedent.

    Using A = a ∧ b ∧ c so only 1/8th of worlds contribute for 6 variables.
    This highlights the benefit of lazy rank calculation.
    """
    a = Symbol("a", BOOL)
    b = Symbol("b", BOOL)
    c = Symbol("c", BOOL)
    d = Symbol("d", BOOL)
    e = Symbol("e", BOOL)
    f = Symbol("f", BOOL)

    A = And(a, b, c)

    conds: list[Conditional] = []

    cond1 = Conditional(d, A, "(d|(a & b & c))")
    cond1.index = 1
    conds.append(cond1)

    cond2 = Conditional(Not(e), A, "(!e|(a & b & c))")
    cond2.index = 2
    conds.append(cond2)

    cond3 = Conditional(f, A, "(f|(a & b & c))")
    cond3.index = 3
    conds.append(cond3)

    return conds


def count_contributing_worlds(
    preocf: PreOCF, revision_conditionals: list[Conditional]
) -> int:
    """Count unique worlds that satisfy any A∧B or A∧¬B among revision conditionals."""
    contributing: set[str] = set()
    for cond in revision_conditionals:
        contributing.update(
            preocf.filter_worlds_by_conditionalization(cond.make_A_then_B())
        )
        contributing.update(
            preocf.filter_worlds_by_conditionalization(cond.make_A_then_not_B())
        )
    return len(contributing)


def run_benchmark(signature: list[str]) -> None:
    revision_conditionals = build_revision_conditionals(signature)
    # Type-safe: filter out None indices before building the mapping
    cond_map: dict[int, Conditional] = {
        int(c.index): c for c in revision_conditionals if c.index is not None
    }
    bb = BeliefBase(signature, cond_map, "bench_kb")

    preocf = CountingSystemZPreOCF(bb, signature)

    total_worlds = 2 ** len(signature)
    contributing_worlds = count_contributing_worlds(preocf, revision_conditionals)

    start = perf_counter()
    _ = compile_alt_fast(preocf, revision_conditionals)
    elapsed_ms = (perf_counter() - start) * 1000.0

    print("=== c-revision rank computation micro-benchmark ===")
    print(f"Signature size: {len(signature)} vars → {total_worlds} worlds")
    print(f"Contributing worlds (|A∧B| ∪ |A∧¬B|): {contributing_worlds}")
    print(f"rank_world calls: {preocf.rank_calls}")
    print(f"rank computations (cache misses): {preocf.compute_calls}")
    print(f"compile_alt_fast time: {elapsed_ms:.2f} ms")
    print()
    print("Note: After implementing lazy rank in compile_alt_fast,")
    print("      'rank computations' should drop close to 'contributing worlds'.")


if __name__ == "__main__":
    # 6 variables → 64 worlds; keeps the benchmark fast
    sig = ["a", "b", "c", "d", "e", "f"]
    run_benchmark(sig)
