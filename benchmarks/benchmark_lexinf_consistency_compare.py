from __future__ import annotations

import argparse
import re
from pathlib import Path

import pandas as pd

from inference.inference_manager import InferenceManager
from parser.Wrappers import parse_belief_base, parse_queries

REPO_ROOT = Path(__file__).resolve().parent.parent
FILENAME_RE = re.compile(r"randomTest_(\d+)_(\d+)_(\d+)\.cl$")
PAPER_COMBINATIONS = {
    (6, 6),
    (8, 8),
    (10, 10),
    (12, 12),
    (14, 14),
    (16, 16),
    (18, 18),
    (20, 20),
    (30, 30),
    (40, 40),
    (50, 50),
    (60, 60),
    (60, 80),
    (60, 100),
    (60, 120),
    (80, 60),
    (80, 80),
    (80, 120),
    (80, 160),
    (100, 60),
    (100, 100),
    (100, 160),
    (100, 200),
    (120, 60),
    (120, 80),
    (120, 120),
    (120, 160),
}


def natural_key(path: Path) -> tuple[int, int, int, str]:
    match = FILENAME_RE.match(path.name)
    if not match:
        return (10**9, 10**9, 10**9, path.name)
    return (int(match.group(1)), int(match.group(2)), int(match.group(3)), path.name)


def resolve_path(path: str) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return REPO_ROOT / candidate


def relative_or_absolute(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(REPO_ROOT))
    except ValueError:
        return str(path.resolve())


def parse_combination(value: str) -> tuple[int, int]:
    parts = value.replace("/", ",").split(",")
    if len(parts) != 2:
        raise argparse.ArgumentTypeError(
            f"expected combination as S/R or S,R, got: {value}"
        )
    try:
        return (int(parts[0]), int(parts[1]))
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            f"expected integer combination as S/R or S,R, got: {value}"
        ) from exc


def query_path_for(ckb_path: Path, dataset_root: Path) -> Path:
    query_name = ckb_path.name.replace("randomTest_", "randomQueries_")
    query_name = query_name.removesuffix(".cl") + ".clq"
    return dataset_root / "queries" / query_name


def iter_cases(
    dataset_root: Path,
    limit: int | None = None,
    combinations: set[tuple[int, int]] | None = None,
) -> list[tuple[Path, Path]]:
    ckbs_dir = dataset_root / "ckbs"
    queries_dir = dataset_root / "queries"
    if not ckbs_dir.is_dir():
        raise FileNotFoundError(f"missing ckbs directory: {ckbs_dir}")
    if not queries_dir.is_dir():
        raise FileNotFoundError(f"missing queries directory: {queries_dir}")

    cases = []
    for ckb_path in sorted(ckbs_dir.glob("randomTest_*.cl"), key=natural_key):
        signature_size, conditionals_count, _, _ = natural_key(ckb_path)
        if (
            combinations is not None
            and (
                signature_size,
                conditionals_count,
            )
            not in combinations
        ):
            continue
        queries_path = query_path_for(ckb_path, dataset_root)
        if not queries_path.is_file():
            raise FileNotFoundError(
                f"missing query file for {ckb_path}: {queries_path}"
            )
        cases.append((ckb_path, queries_path))
        if limit is not None and len(cases) >= limit:
            break
    return cases


def completed_keys(output_path: Path) -> set[tuple[str, str, str]]:
    if not output_path.exists() or output_path.stat().st_size == 0:
        return set()
    df = pd.read_csv(
        output_path,
        usecols=["dataset", "belief_base_consistency", "belief_base"],
    )
    return set(
        zip(
            df["dataset"].astype(str),
            df["belief_base_consistency"].astype(str),
            df["belief_base"].astype(str),
            strict=False,
        )
    )


def run_dataset(
    *,
    dataset: str,
    consistency: str,
    dataset_root: Path,
    output_path: Path,
    total_timeout: int,
    preprocessing_timeout: int,
    inference_timeout: int,
    smt_solver: str,
    pmaxsat_solver: str,
    multi_inference: bool,
    limit: int | None,
    resume: bool,
    combinations: set[tuple[int, int]] | None,
) -> None:
    cases = iter_cases(dataset_root, limit=limit, combinations=combinations)
    done = completed_keys(output_path) if resume else set()

    for ordinal, (ckb_path, queries_path) in enumerate(cases, start=1):
        belief_base_name = ckb_path.stem
        key = (dataset, consistency, belief_base_name)
        if key in done:
            print(f"skip {dataset}/{belief_base_name} ({ordinal}/{len(cases)})")
            continue

        print(
            f"run {dataset}/{belief_base_name} "
            f"consistency={consistency} ({ordinal}/{len(cases)})"
        )
        belief_base = parse_belief_base(str(ckb_path))
        queries = parse_queries(str(queries_path))
        manager = InferenceManager(
            belief_base,
            inference_system="lex_inf",
            smt_solver=smt_solver,
            pmaxsat_solver=pmaxsat_solver,
            weakly=True,
        )
        results = manager.inference(
            queries,
            total_timeout=total_timeout,
            preprocessing_timeout=preprocessing_timeout,
            inference_timeout=inference_timeout,
            queries_name=queries_path.stem,
            result_metadata={
                "dataset": dataset,
                "belief_base_consistency": consistency,
                "belief_base_filepath": relative_or_absolute(ckb_path),
                "queries_filepath": relative_or_absolute(queries_path),
            },
            multi_inference=multi_inference,
        )

        output_path.parent.mkdir(parents=True, exist_ok=True)
        results.to_csv(
            output_path,
            mode="a",
            header=not output_path.exists() or output_path.stat().st_size == 0,
            index=False,
        )
        done.add(key)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Benchmark lex_inf on strong and weak CLKR-style datasets."
    )
    parser.add_argument(
        "--strong-root",
        default="local/CLKR-PS005",
        help="CLKR-style root containing ckbs/ and queries/ for strong bases.",
    )
    parser.add_argument(
        "--weak-root",
        default="benchmarks/generated/lexinf_ecsqaru2025/targeted_weak_clkr_format",
        help="CLKR-style root containing ckbs/ and queries/ for weak bases.",
    )
    parser.add_argument(
        "--output",
        default="local/results_lexinf_strong_vs_weak.csv",
        help="CSV output path.",
    )
    parser.add_argument("--total-timeout", type=int, default=300)
    parser.add_argument("--preprocessing-timeout", type=int, default=0)
    parser.add_argument("--inference-timeout", type=int, default=0)
    parser.add_argument("--smt-solver", default="z3")
    parser.add_argument("--pmaxsat-solver", default="z3")
    parser.add_argument("--multi-inference", action="store_true")
    parser.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Limit cases per dataset for smoke tests.",
    )
    parser.add_argument(
        "--no-resume",
        action="store_true",
        help="Do not skip already completed dataset/belief_base pairs in output CSV.",
    )
    parser.add_argument(
        "--include-extra-ps005-120-200",
        action="store_true",
        help="Include PS005's extra 120/200 combination. By default only the 27 paper combinations are used.",
    )
    parser.add_argument(
        "--exclude-combination",
        action="append",
        type=parse_combination,
        default=[],
        metavar="S/R",
        help="Exclude a signature/conditionals combination. Can be passed multiple times, e.g. --exclude-combination 100/200.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    output_path = resolve_path(args.output)
    resume = not args.no_resume
    combinations = None if args.include_extra_ps005_120_200 else PAPER_COMBINATIONS
    if args.exclude_combination:
        excluded = set(args.exclude_combination)
        combinations = (
            PAPER_COMBINATIONS | {(120, 200)}
            if combinations is None
            else set(combinations)
        )
        combinations -= excluded

    run_dataset(
        dataset="CLKR-PS005",
        consistency="strong",
        dataset_root=resolve_path(args.strong_root),
        output_path=output_path,
        total_timeout=args.total_timeout,
        preprocessing_timeout=args.preprocessing_timeout,
        inference_timeout=args.inference_timeout,
        smt_solver=args.smt_solver,
        pmaxsat_solver=args.pmaxsat_solver,
        multi_inference=args.multi_inference,
        limit=args.limit,
        resume=resume,
        combinations=combinations,
    )
    run_dataset(
        dataset="targeted-weak",
        consistency="weak",
        dataset_root=resolve_path(args.weak_root),
        output_path=output_path,
        total_timeout=args.total_timeout,
        preprocessing_timeout=args.preprocessing_timeout,
        inference_timeout=args.inference_timeout,
        smt_solver=args.smt_solver,
        pmaxsat_solver=args.pmaxsat_solver,
        multi_inference=args.multi_inference,
        limit=args.limit,
        resume=resume,
        combinations=combinations,
    )


if __name__ == "__main__":
    main()
