#!/usr/bin/env python3
"""Compare the old (script-level) and new (library) Pareto front implementations.

Uses 6-variable / 6-conditional random knowledge bases from
examples/random_large/ to cross-validate both approaches.

Old implementation: run_c_revision_birds_custom.calculate_pareto_front
  - builds RandomMinCRepPreOCF (c-inference CSP)
  - uses z3.Optimize with priority="pareto" + explicit blocking constraint

New implementation: inference.c_revision.c_revision_pareto_front
  - builds c-revision CSP (compile_alt_fast + translate_to_csp)
  - uses z3.Optimize with priority="pareto" (no explicit blocking)
"""

from __future__ import annotations

import sys
import time
from pathlib import Path

# ---------------------------------------------------------------------------
# imports
# ---------------------------------------------------------------------------
from inference.belief_base import BeliefBase
from inference.c_revision import (
    c_inference_pareto_front,
    c_revision_pareto_front,
)
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF
from parser.Wrappers import parse_belief_base

EXAMPLES_DIR = Path("examples/random_large")
MAX_PAIRS = 100
# only use 6-variable KBs (64 worlds) -- tractable for pareto enumeration
SIG_SIZE = 6


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------


def new_pareto_front(belief_base: BeliefBase) -> list[tuple[int, ...]] | None:
    """Compute Pareto front via the new c_revision_pareto_front library fn."""
    try:
        sig = belief_base.signature
        n = len(sig)
        ranks = {format(i, f"0{n}b"): 0 for i in range(2**n)}
        preocf = CustomPreOCF(ranks, belief_base, sig)

        rev_conds: list[Conditional] = []
        for idx, cond in belief_base.conditionals.items():
            rc = Conditional(
                cond.consequence, cond.antecedence, cond.textRepresentation
            )
            rc.index = idx
            rev_conds.append(rc)

        solutions = c_revision_pareto_front(preocf, rev_conds, gamma_plus_zero=True)

        indices = sorted(c.index for c in rev_conds)
        return [tuple(sol.get(f"gamma-_{i}", 0) for i in indices) for sol in solutions]
    except Exception as exc:
        print(f"    [new] failed: {exc}")
        return None


def discover_pairs(directory: Path, sig_size: int, max_pairs: int):
    """Return up to *max_pairs* (kb_path, query_path) tuples."""
    pairs = []
    for idx in range(200):  # file indices go 0..99 typically
        kb = directory / f"randomTest_{sig_size}_{sig_size}_{idx}.cl"
        qr = directory / f"randomQueries_{sig_size}_{sig_size}_{idx}.clq"
        if kb.exists() and qr.exists():
            pairs.append((kb, qr))
        if len(pairs) >= max_pairs:
            break
    return pairs


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    pairs = discover_pairs(EXAMPLES_DIR, SIG_SIZE, MAX_PAIRS)
    if not pairs:
        print(f"no test pairs found in {EXAMPLES_DIR} for sig_size={SIG_SIZE}")
        sys.exit(1)

    print(f"found {len(pairs)} KB/query pairs (sig_size={SIG_SIZE})")
    print("=" * 72)

    passed = 0
    failed = 0
    skipped = 0
    old_total_ms = 0.0
    new_total_ms = 0.0

    for i, (kb_path, _qr_path) in enumerate(pairs):
        label = kb_path.stem
        try:
            bb = parse_belief_base(str(kb_path))
        except Exception as exc:
            print(f"[{i:3d}] {label}: SKIP (parse error: {exc})")
            skipped += 1
            continue

        # --- c-inference CSP implementation ---
        t0 = time.perf_counter()
        old_result = c_inference_pareto_front(bb) or None
        old_ms = (time.perf_counter() - t0) * 1000.0

        # --- new implementation ---
        t0 = time.perf_counter()
        new_result = new_pareto_front(bb)
        new_ms = (time.perf_counter() - t0) * 1000.0

        old_total_ms += old_ms
        new_total_ms += new_ms

        # compare
        if old_result is None and new_result is None:
            status = "SKIP (both None)"
            skipped += 1
        elif old_result is None or new_result is None:
            status = f"FAIL (one None: old={old_result is not None}, new={new_result is not None})"
            failed += 1
        else:
            old_set = set(old_result)
            new_set = set(new_result)
            if old_set == new_set:
                status = f"OK  ({len(old_set)} pts)"
                passed += 1
            else:
                only_old = old_set - new_set
                only_new = new_set - old_set
                status = f"MISMATCH  old_only={only_old}  new_only={only_new}"
                failed += 1

        print(f"[{i:3d}] {label}: {status}  (old {old_ms:.0f}ms, new {new_ms:.0f}ms)")

    print()
    print("=" * 72)
    print(f"results: {passed} passed, {failed} failed, {skipped} skipped")
    print(f"total time: old {old_total_ms:.0f}ms, new {new_total_ms:.0f}ms")
    if passed + failed > 0:
        print(
            f"avg time per KB: old {old_total_ms / (passed + failed):.0f}ms, "
            f"new {new_total_ms / (passed + failed):.0f}ms"
        )

    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
