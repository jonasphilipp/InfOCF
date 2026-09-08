#!/usr/bin/env python3
"""Compute and cross-validate the Pareto front of impact vectors.

Runs two independent implementations and compares their results:
  (A) c-inference CSP   -- via CInference (MaxSAT) + z3.Optimize
  (B) c-revision CSP    -- via compile_alt_fast + translate_to_csp + z3.Optimize

Usage:
    # specific KB files
    uv run python calculate_pareto_front.py examples/birds/kb_birds001.cl path/to/my_kb.cl

    # inline KB string
    uv run python calculate_pareto_front.py --inline 'signature
    b,p,f,w
    conditionals
    birds{(f|b),(!f|p),(b|p),(w|b)}'

    # run on all built-in example KBs (default)
    uv run python calculate_pareto_front.py

    # save results to JSON (one file per KB, written when both implementations agree)
    uv run python calculate_pareto_front.py --save-json results/ planning/bsp_01.cl
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from inference.belief_base import BeliefBase
from inference.c_revision import (
    c_inference_pareto_front,
    c_revision_pareto_front,
)
from inference.conditional import Conditional
from inference.preocf import CustomPreOCF
from parser.Wrappers import parse_belief_base

# ---------------------------------------------------------------------------
# implementation A: c-inference CSP (MaxSAT compilation -> SMT)
# ---------------------------------------------------------------------------


def pareto_front_cinference(belief_base: BeliefBase) -> list[tuple[int, ...]] | None:
    """Pareto front via c-inference CSP."""
    result = c_inference_pareto_front(belief_base)
    return result if result else None


# ---------------------------------------------------------------------------
# implementation B: c-revision CSP (compile_alt_fast -> SMT)
# ---------------------------------------------------------------------------


def pareto_front_crevision(belief_base: BeliefBase) -> list[tuple[int, ...]] | None:
    """Pareto front via c-revision CSP (gamma_plus_zero=True, uniform rank 0)."""
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
        return None


# ---------------------------------------------------------------------------
# presentation
# ---------------------------------------------------------------------------


def format_vector(vec: tuple[int, ...], indices: list[int]) -> str:
    """Pretty-print an eta/impact vector."""
    parts = [f"eta_{i}={v}" for i, v in zip(indices, vec, strict=False)]
    return "(" + ", ".join(parts) + ")"


def save_result_json(
    out_dir: Path,
    label: str,
    bb: BeliefBase,
    vectors: list[tuple[int, ...]],
) -> Path:
    """Write a JSON result file and return its path."""
    indices = sorted(bb.conditionals.keys())
    data = {
        "knowledge_base": label,
        "signature": bb.signature,
        "conditionals": {
            str(idx): bb.conditionals[idx].textRepresentation for idx in indices
        },
        "pareto_front": [
            {f"eta_{i}": v for i, v in zip(indices, vec, strict=False)}
            for vec in sorted(vectors)
        ],
        "num_solutions": len(vectors),
    }
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / f"{label}.json"
    with open(out_path, "w") as fh:
        json.dump(data, fh, indent=2)
    return out_path


def run_one_kb(label: str, bb: BeliefBase, *, save_dir: Path | None = None) -> bool:
    """Run both implementations on one KB. Returns True if results match."""
    sig = bb.signature
    n_vars = len(sig)
    n_conds = len(bb.conditionals)
    indices = sorted(bb.conditionals.keys())

    print(f"\n{'=' * 72}")
    print(f"  {label}")
    print(f"  signature ({n_vars} vars): {', '.join(sig)}")
    print(f"  conditionals ({n_conds}):")
    for idx in indices:
        print(f"    r{idx} = {bb.conditionals[idx].textRepresentation}")
    print(f"{'=' * 72}")

    # --- implementation A ---
    t0 = time.perf_counter()
    result_a = pareto_front_cinference(bb)
    ms_a = (time.perf_counter() - t0) * 1000.0

    # --- implementation B ---
    t0 = time.perf_counter()
    result_b = pareto_front_crevision(bb)
    ms_b = (time.perf_counter() - t0) * 1000.0

    # display
    if result_a is not None:
        print(f"\n  [A] c-inference CSP  ({ms_a:.0f} ms, {len(result_a)} solution(s)):")
        for i, vec in enumerate(sorted(result_a), 1):
            print(f"       {i}. {format_vector(vec, indices)}")
    else:
        print("\n  [A] c-inference CSP: FAILED")

    if result_b is not None:
        print(f"\n  [B] c-revision CSP   ({ms_b:.0f} ms, {len(result_b)} solution(s)):")
        for i, vec in enumerate(sorted(result_b), 1):
            print(f"       {i}. {format_vector(vec, indices)}")
    else:
        print("\n  [B] c-revision CSP: FAILED")

    # compare (treat None and [] as equivalent -- both mean "no solutions")
    norm_a = set(result_a) if result_a else set()
    norm_b = set(result_b) if result_b else set()
    match = False
    if norm_a == norm_b and not norm_a:
        print("\n  >> AGREE  (no Pareto-optimal vectors -- KB likely inconsistent)")
        match = True
    elif result_a is None or result_b is None:
        print("\n  >> MISMATCH (one implementation failed)")
    elif set(result_a) == set(result_b):
        print(f"\n  >> MATCH  ({len(result_a)} Pareto-optimal vector(s) agree)")
        match = True
    else:
        only_a = set(result_a) - set(result_b)
        only_b = set(result_b) - set(result_a)
        print("\n  >> MISMATCH")
        if only_a:
            print(f"     only in [A]: {only_a}")
        if only_b:
            print(f"     only in [B]: {only_b}")

    # save JSON when both agree and there are solutions
    if match and save_dir is not None and norm_a:
        vectors = sorted(norm_a)
        out_path = save_result_json(save_dir, label, bb, vectors)
        print(f"  >> saved: {out_path}")

    return match


# ---------------------------------------------------------------------------
# KB discovery
# ---------------------------------------------------------------------------


def discover_builtin_kbs() -> list[tuple[str, str]]:
    """Return (label, path) pairs for all tractable built-in KBs."""
    root = Path(__file__).parent
    pairs: list[tuple[str, str]] = []

    # birds examples
    birds_dir = root / "examples" / "birds"
    if birds_dir.exists():
        for f in sorted(birds_dir.glob("kb_*.cl")):
            pairs.append((f.stem, str(f)))
        for f in sorted(birds_dir.glob("example*.cl")):
            pairs.append((f.stem, str(f)))

    # AO domain examples (skip those > 12 vars -- too expensive)
    ao_dir = root / "examples" / "AO_Beispiele_Konditionale_KBs"
    if ao_dir.exists():
        for sub in sorted(ao_dir.iterdir()):
            if not sub.is_dir():
                continue
            kb_files = list(sub.rglob("kb_*.cl"))
            if not kb_files:
                continue
            kb_path = kb_files[0]
            # quick var count check
            with open(kb_path) as fh:
                lines = fh.readlines()
            if len(lines) >= 2:
                n_vars = len(lines[1].strip().split(","))
                if n_vars > 12:
                    continue
            pairs.append((sub.name, str(kb_path)))

    # gen examples
    gen_dir = root / "examples" / "gen"
    if gen_dir.exists():
        for f in sorted(gen_dir.glob("kb_gen*.cl")):
            pairs.append((f.stem, str(f)))

    return pairs


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Compute and cross-validate Pareto front of impact vectors."
    )
    parser.add_argument(
        "kb_files",
        nargs="*",
        help="paths to .cl knowledge base files (default: all built-in examples)",
    )
    parser.add_argument(
        "--inline",
        type=str,
        default=None,
        help="inline KB string instead of files",
    )
    parser.add_argument(
        "--save-json",
        type=str,
        default=None,
        metavar="DIR",
        help="save results as JSON files in DIR (only when both implementations agree)",
    )
    args = parser.parse_args()

    kbs: list[tuple[str, BeliefBase]] = []

    if args.inline:
        bb = parse_belief_base(args.inline)
        kbs.append(("inline", bb))
    elif args.kb_files:
        for path in args.kb_files:
            try:
                bb = parse_belief_base(path)
                kbs.append((Path(path).stem, bb))
            except Exception as exc:
                print(f"[skip] {path}: {exc}", file=sys.stderr)
    else:
        # default: all built-in tractable KBs
        for label, path in discover_builtin_kbs():
            try:
                bb = parse_belief_base(path)
                kbs.append((label, bb))
            except Exception as exc:
                print(f"[skip] {label}: {exc}", file=sys.stderr)

    if not kbs:
        print("no knowledge bases to process", file=sys.stderr)
        sys.exit(1)

    save_dir = Path(args.save_json) if args.save_json else None

    print(f"processing {len(kbs)} knowledge base(s)")
    if save_dir:
        print(f"saving results to: {save_dir}/")

    passed = 0
    failed = 0
    for label, bb in kbs:
        ok = run_one_kb(label, bb, save_dir=save_dir)
        if ok:
            passed += 1
        else:
            failed += 1

    print(f"\n{'=' * 72}")
    print(f"SUMMARY: {passed} matched, {failed} mismatched/failed, {len(kbs)} total")
    print(f"{'=' * 72}")

    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
