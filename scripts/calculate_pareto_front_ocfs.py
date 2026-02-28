#!/usr/bin/env python3
"""Compute Pareto-optimal eta vectors and their induced OCFs.

For each knowledge base, enumerates the full Pareto front of c-representation
impact vectors (cross-validated via both c-inference and c-revision CSPs),
then computes the induced OCF for each vector using:
    kappa(omega) = sum of eta_i for all conditionals i falsified by omega

Usage:
    # specific KB files
    uv run python calculate_pareto_front_ocfs.py planning/bsp_01.cl planning/kr2026_example4.cl

    # save JSON results
    uv run python calculate_pareto_front_ocfs.py --save-json results/ planning/bsp_01.cl

    # batch: random examples (first N of given signature size)
    uv run python calculate_pareto_front_ocfs.py --random-large 6 --max 20

    # all built-in examples
    uv run python calculate_pareto_front_ocfs.py --builtin
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
from inference.preocf import CustomPreOCF, RandomMinCRepPreOCF
from parser.Wrappers import parse_belief_base

# ---------------------------------------------------------------------------
# ocf computation from eta vector
# ---------------------------------------------------------------------------


def etas_to_ocf(
    belief_base: BeliefBase, eta_vector: list[int]
) -> tuple[dict[str, int], RandomMinCRepPreOCF]:
    """Compute the full OCF induced by an eta vector (Definition 1 of the paper).

    kappa(omega) = sum of eta_i for each conditional i that omega falsifies.

    Returns (ranks_dict, ocf_instance) so the caller can also run acceptance
    checks via the instance.
    """
    ocf_instance = RandomMinCRepPreOCF.init_with_impacts_list(belief_base, eta_vector)
    ocf_instance.compute_all_ranks()
    ranks = {w: r for w, r in ocf_instance.ranks.items() if r is not None}
    return ranks, ocf_instance


def verify_ocf_accepts_kb(
    ocf_instance: RandomMinCRepPreOCF,
    belief_base: BeliefBase,
) -> list[tuple[int, str, bool]]:
    """Check that the OCF accepts every conditional in the KB.

    Returns a list of (index, text_repr, accepted) for each conditional.
    An OCF is a valid c-representation iff all conditionals are accepted:
        kappa(A_i & B_i) < kappa(A_i & ~B_i)
    """
    results = []
    for idx in sorted(belief_base.conditionals.keys()):
        cond = belief_base.conditionals[idx]
        accepted = ocf_instance.conditional_acceptance(cond)
        results.append((idx, cond.textRepresentation, accepted))
    return results


def verbose_world(world: str, signature: list[str]) -> str:
    """Convert a bitstring world to readable form like 'b, !p, f, w'."""
    parts = []
    for i, var in enumerate(signature):
        if world[i] == "1":
            parts.append(var)
        else:
            parts.append(f"!{var}")
    return ", ".join(parts)


# ---------------------------------------------------------------------------
# pareto front (both implementations)
# ---------------------------------------------------------------------------


def compute_pareto_front(
    belief_base: BeliefBase,
) -> tuple[list[tuple[int, ...]] | None, list[tuple[int, ...]] | None]:
    """Return (cinference_result, crevision_result)."""
    # implementation A: c-inference CSP
    try:
        result_a = c_inference_pareto_front(belief_base) or None
    except Exception:
        result_a = None

    # implementation B: c-revision CSP
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
        result_b: list[tuple[int, ...]] | None = [
            tuple(sol.get(f"gamma-_{i}", 0) for i in indices) for sol in solutions
        ] or None
    except Exception:
        result_b = None

    return result_a, result_b


# ---------------------------------------------------------------------------
# process one KB
# ---------------------------------------------------------------------------


def process_kb(
    label: str,
    bb: BeliefBase,
    *,
    save_dir: Path | None = None,
    verbose: bool = True,
) -> bool:
    """Compute Pareto front + OCFs for one KB. Returns True if both impls agree."""
    sig = bb.signature
    indices = sorted(bb.conditionals.keys())

    if verbose:
        print(f"\n{'=' * 72}")
        print(f"  {label}")
        print(f"  signature ({len(sig)} vars): {', '.join(sig)}")
        print(f"  conditionals ({len(bb.conditionals)}):")
        for idx in indices:
            print(f"    r{idx} = {bb.conditionals[idx].textRepresentation}")
        print(f"{'=' * 72}")

    t0 = time.perf_counter()
    result_a, result_b = compute_pareto_front(bb)
    ms = (time.perf_counter() - t0) * 1000.0

    # check agreement
    norm_a = set(result_a) if result_a else set()
    norm_b = set(result_b) if result_b else set()
    match = norm_a == norm_b

    vectors = sorted(norm_a) if match and norm_a else sorted(norm_a | norm_b)

    if verbose:
        status = "MATCH" if match else "MISMATCH"
        print(f"\n  {status} ({len(vectors)} vector(s), {ms:.0f} ms)")
        if not match:
            only_a = norm_a - norm_b
            only_b = norm_b - norm_a
            if only_a:
                print(f"  only in [A]: {only_a}")
            if only_b:
                print(f"  only in [B]: {only_b}")

    # compute OCFs for each vector and verify acceptance
    ocfs: list[dict] = []
    all_verified = True
    for vec_idx, vec in enumerate(vectors, 1):
        eta_list = list(vec)
        ocf_ranks, ocf_instance = etas_to_ocf(bb, eta_list)

        # verify: the induced OCF must accept every conditional in the KB
        checks = verify_ocf_accepts_kb(ocf_instance, bb)
        all_accepted = all(ok for _, _, ok in checks)
        if not all_accepted:
            all_verified = False

        if verbose:
            eta_str = ", ".join(
                f"eta_{i}={v}" for i, v in zip(indices, vec, strict=False)
            )
            print(f"\n  solution {vec_idx}: ({eta_str})")

            # verification result
            if all_accepted:
                print(f"    verification: OK (all {len(checks)} conditionals accepted)")
            else:
                rejected = [(i, t) for i, t, ok in checks if not ok]
                print(
                    f"    verification: FAIL ({len(rejected)} conditional(s) NOT accepted)"
                )
                for i, t in rejected:
                    print(f"      r{i} = {t}  <-- NOT ACCEPTED")

            # group worlds by rank for compact display
            by_rank: dict[int, list[str]] = {}
            for w, r in sorted(ocf_ranks.items(), key=lambda x: (x[1], x[0])):
                by_rank.setdefault(r, []).append(w)
            for rank in sorted(by_rank):
                worlds = by_rank[rank]
                # show up to 4 worlds per rank, then summarize
                shown = worlds[:4]
                desc = [f"{w} ({verbose_world(w, sig)})" for w in shown]
                suffix = f" ... +{len(worlds) - 4} more" if len(worlds) > 4 else ""
                print(f"    rank {rank:3d}: {', '.join(desc)}{suffix}")

        ocfs.append(
            {
                "eta": {f"eta_{i}": v for i, v in zip(indices, vec, strict=False)},
                "verified": all_accepted,
                "ocf": {
                    w: {"rank": r, "world_verbose": verbose_world(w, sig)}
                    for w, r in sorted(ocf_ranks.items(), key=lambda x: (x[1], x[0]))
                },
            }
        )

    if verbose and vectors:
        if all_verified:
            print(
                f"\n  >> all {len(vectors)} OCF(s) verified: every conditional accepted"
            )
        else:
            print("\n  >> WARNING: some OCF(s) failed verification!")

    # save JSON
    if save_dir is not None and vectors:
        data = {
            "knowledge_base": label,
            "signature": sig,
            "conditionals": {
                str(idx): bb.conditionals[idx].textRepresentation for idx in indices
            },
            "implementations_agree": match,
            "num_solutions": len(vectors),
            "pareto_front": ocfs,
        }
        save_dir.mkdir(parents=True, exist_ok=True)
        out_path = save_dir / f"{label}_ocf.json"
        with open(out_path, "w") as fh:
            json.dump(data, fh, indent=2)
        if verbose:
            print(f"\n  >> saved: {out_path}")

    return match


# ---------------------------------------------------------------------------
# KB discovery helpers
# ---------------------------------------------------------------------------


def discover_random_large(sig_size: int, max_count: int) -> list[tuple[str, str]]:
    """Find random_large KB files for given signature size."""
    base = Path("examples/random_large")
    pairs = []
    for idx in range(200):
        kb = base / f"randomTest_{sig_size}_{sig_size}_{idx}.cl"
        if kb.exists():
            pairs.append((kb.stem, str(kb)))
        if len(pairs) >= max_count:
            break
    return pairs


def discover_builtin() -> list[tuple[str, str]]:
    """All tractable built-in KBs (up to 12 vars)."""
    root = Path(__file__).parent
    pairs: list[tuple[str, str]] = []

    for d in ["examples/birds", "examples/gen"]:
        p = root / d
        if p.exists():
            for f in sorted(p.glob("kb_*.cl")):
                pairs.append((f.stem, str(f)))
            for f in sorted(p.glob("example*.cl")):
                pairs.append((f.stem, str(f)))

    ao_dir = root / "examples" / "AO_Beispiele_Konditionale_KBs"
    if ao_dir.exists():
        for sub in sorted(ao_dir.iterdir()):
            if not sub.is_dir():
                continue
            kb_files = list(sub.rglob("kb_*.cl"))
            if not kb_files:
                continue
            kb_path = kb_files[0]
            with open(kb_path) as fh:
                lines = fh.readlines()
            if len(lines) >= 2 and len(lines[1].strip().split(",")) <= 12:
                pairs.append((sub.name, str(kb_path)))

    return pairs


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Compute Pareto-optimal eta vectors and induced OCFs."
    )
    parser.add_argument(
        "kb_files",
        nargs="*",
        help="paths to .cl knowledge base files",
    )
    parser.add_argument(
        "--save-json",
        type=str,
        default=None,
        metavar="DIR",
        help="save results as JSON files in DIR",
    )
    parser.add_argument(
        "--random-large",
        type=int,
        default=None,
        metavar="SIG_SIZE",
        help="use random_large examples with given signature size",
    )
    parser.add_argument(
        "--max",
        type=int,
        default=100,
        help="max number of KBs when using --random-large (default: 100)",
    )
    parser.add_argument(
        "--builtin",
        action="store_true",
        help="run on all built-in example KBs",
    )
    parser.add_argument(
        "-q",
        "--quiet",
        action="store_true",
        help="suppress per-world OCF output (still prints vectors and summary)",
    )
    args = parser.parse_args()

    kbs: list[tuple[str, BeliefBase]] = []

    if args.random_large is not None:
        for label, path in discover_random_large(args.random_large, args.max):
            try:
                kbs.append((label, parse_belief_base(path)))
            except Exception as exc:
                print(f"[skip] {label}: {exc}", file=sys.stderr)
    elif args.builtin:
        for label, path in discover_builtin():
            try:
                kbs.append((label, parse_belief_base(path)))
            except Exception as exc:
                print(f"[skip] {label}: {exc}", file=sys.stderr)
    elif args.kb_files:
        for path in args.kb_files:
            try:
                kbs.append((Path(path).stem, parse_belief_base(path)))
            except Exception as exc:
                print(f"[skip] {path}: {exc}", file=sys.stderr)
    else:
        parser.print_help()
        sys.exit(0)

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
        ok = process_kb(label, bb, save_dir=save_dir, verbose=not args.quiet)
        if ok:
            passed += 1
        else:
            failed += 1

    print(f"\n{'=' * 72}")
    print(f"SUMMARY: {passed} matched, {failed} mismatched, {len(kbs)} total")
    print(f"{'=' * 72}")

    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
