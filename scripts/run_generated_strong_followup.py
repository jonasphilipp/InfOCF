from __future__ import annotations

import argparse
import csv
import shutil
import subprocess
import time
from pathlib import Path

from benchmarks.benchmark_lexinf_consistency_compare import run_dataset
from benchmarks.trueRandomSampling import (
    DEFAULT_MAX_ATTEMPTS,
    DEFAULT_QUERIES_PER_BELIEF_BASE,
    MANIFEST_HEADER,
    makeCKB,
    makeQueryfile,
    read_manifest,
    sampleQueries,
    samplingConsistentCKB,
)

FOLLOWUP_COMBINATIONS = [(120, 60), (120, 80), (120, 120)]
EXCLUDED_COMBINATIONS = {(100, 200), (120, 160)}
REPO_ROOT = Path(__file__).resolve().parent.parent


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


def resolve_path(path: str) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return REPO_ROOT / candidate


def combo_from_belief_base(value: str) -> tuple[int, int] | None:
    parts = Path(value).stem.split("_")
    if len(parts) < 4 or parts[0] != "randomTest":
        return None
    try:
        return (int(parts[1]), int(parts[2]))
    except ValueError:
        return None


def count_completed_weak_bases(csv_path: Path) -> int:
    if not csv_path.exists() or csv_path.stat().st_size == 0:
        return 0

    completed = set()
    with csv_path.open(newline="") as handle:
        for row in csv.DictReader(handle):
            if row.get("dataset") != "targeted-weak":
                continue
            combo = combo_from_belief_base(row.get("belief_base", ""))
            if combo is None or combo in EXCLUDED_COMBINATIONS:
                continue
            completed.add(row["belief_base"])
    return len(completed)


def benchmark_processes() -> list[str]:
    try:
        output = subprocess.check_output(
            ["pgrep", "-af", "benchmark_lexinf_consistency_compare.py"],
            text=True,
        )
    except subprocess.CalledProcessError:
        return []
    return [
        line
        for line in output.splitlines()
        if "run_generated_strong_followup.py" not in line
    ]


def wait_for_current_weak_run(
    csv_path: Path,
    target_bases: int,
    poll_seconds: int,
) -> None:
    while True:
        completed = count_completed_weak_bases(csv_path)
        active = benchmark_processes()
        print(
            "waiting for current weak benchmark: "
            f"{completed}/{target_bases} comparable weak bases complete; "
            f"active benchmark processes={len(active)}",
            flush=True,
        )
        if completed >= target_bases and not active:
            return
        time.sleep(poll_seconds)


def generate_missing_targeted_strong(
    *,
    output_dir: Path,
    combinations: list[tuple[int, int]],
    samples_per_combination: int,
    queries_per_belief_base: int,
    max_attempts: int,
) -> None:
    manifest_path = output_dir / "manifest.csv"
    output_dir.mkdir(parents=True, exist_ok=True)
    completed, _, _ = read_manifest(manifest_path)

    write_header = not manifest_path.exists() or manifest_path.stat().st_size == 0
    with manifest_path.open("a", newline="") as manifest:
        writer = csv.writer(manifest)
        if write_header:
            writer.writerow(MANIFEST_HEADER)
            manifest.flush()

        for signature_size, conditionals_count in combinations:
            combo_dir = (
                output_dir
                / "targeted"
                / "strong"
                / f"{signature_size}_{conditionals_count}"
            )
            combo_dir.mkdir(parents=True, exist_ok=True)

            for index in range(samples_per_combination):
                manifest_key = (
                    "targeted",
                    "strong",
                    signature_size,
                    conditionals_count,
                    index,
                )
                belief_base_path = (
                    combo_dir
                    / f"randomTest_{signature_size}_{conditionals_count}_{index}.cl"
                )
                queries_path = (
                    combo_dir
                    / f"randomQueries_{signature_size}_{conditionals_count}_{index}.cl"
                )

                if belief_base_path.exists() and queries_path.exists():
                    if manifest_key not in completed:
                        writer.writerow(
                            [
                                "targeted",
                                "strong",
                                signature_size,
                                conditionals_count,
                                index,
                                belief_base_path,
                                queries_path,
                            ]
                        )
                        manifest.flush()
                        completed.add(manifest_key)
                    continue
                if manifest_key in completed:
                    continue

                print(
                    "sampling targeted/strong "
                    f"{signature_size}/{conditionals_count} #{index} "
                    f"-> {belief_base_path}, {queries_path}",
                    flush=True,
                )
                variables, conditionals, _ = samplingConsistentCKB(
                    signature_size,
                    conditionals_count,
                    consistency_mode="strong",
                    inject_bottom=False,
                    max_attempts=max_attempts,
                    verbose=False,
                )
                queries = sampleQueries(
                    variables,
                    queries_per_belief_base,
                    existing_conditionals=conditionals,
                    max_attempts=max_attempts,
                )
                makeCKB(variables, conditionals, [], str(belief_base_path))
                makeQueryfile(queries, str(queries_path))
                writer.writerow(
                    [
                        "targeted",
                        "strong",
                        signature_size,
                        conditionals_count,
                        index,
                        belief_base_path,
                        queries_path,
                    ]
                )
                manifest.flush()
                completed.add(manifest_key)


def export_targeted_strong_to_clkr(
    *,
    generated_root: Path,
    clkr_root: Path,
    combinations: list[tuple[int, int]],
) -> int:
    ckbs_dir = clkr_root / "ckbs"
    queries_dir = clkr_root / "queries"
    ckbs_dir.mkdir(parents=True, exist_ok=True)
    queries_dir.mkdir(parents=True, exist_ok=True)

    copied = 0
    for signature_size, conditionals_count in combinations:
        source_dir = (
            generated_root
            / "targeted"
            / "strong"
            / f"{signature_size}_{conditionals_count}"
        )
        for belief_base_path in sorted(source_dir.glob("randomTest_*.cl")):
            queries_path = source_dir / belief_base_path.name.replace(
                "randomTest_", "randomQueries_"
            )
            if not queries_path.exists():
                raise FileNotFoundError(f"missing query file: {queries_path}")

            shutil.copy2(belief_base_path, ckbs_dir / belief_base_path.name)
            shutil.copy2(
                queries_path,
                queries_dir / (queries_path.stem + ".clq"),
            )
            copied += 1

    return copied


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Wait for the current weak benchmark, then generate and benchmark "
            "the missing targeted-strong follow-up combinations."
        )
    )
    parser.add_argument(
        "--combination",
        action="append",
        type=parse_combination,
        default=[],
        metavar="S/R",
        help="Combination to generate and benchmark. Defaults to 120/60, 120/80, 120/120.",
    )
    parser.add_argument(
        "--generated-root",
        default="benchmarks/generated/lexinf_ecsqaru2025",
    )
    parser.add_argument(
        "--clkr-root",
        default="benchmarks/generated/lexinf_ecsqaru2025/targeted_strong_followup_clkr_format",
    )
    parser.add_argument(
        "--output",
        default="local/results_lexinf_strong_vs_weak.csv",
        help="CSV to append targeted-strong benchmark rows to.",
    )
    parser.add_argument("--samples-per-combination", type=int, default=100)
    parser.add_argument(
        "--queries-per-belief-base", type=int, default=DEFAULT_QUERIES_PER_BELIEF_BASE
    )
    parser.add_argument("--max-attempts", type=int, default=DEFAULT_MAX_ATTEMPTS)
    parser.add_argument("--total-timeout", type=int, default=300)
    parser.add_argument("--preprocessing-timeout", type=int, default=0)
    parser.add_argument("--inference-timeout", type=int, default=0)
    parser.add_argument("--smt-solver", default="z3")
    parser.add_argument("--pmaxsat-solver", default="z3")
    parser.add_argument("--multi-inference", action="store_true")
    parser.add_argument("--no-wait", action="store_true")
    parser.add_argument("--wait-target-bases", type=int, default=2500)
    parser.add_argument("--poll-seconds", type=int, default=300)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    combinations = args.combination or FOLLOWUP_COMBINATIONS
    generated_root = resolve_path(args.generated_root)
    clkr_root = resolve_path(args.clkr_root)
    output_path = resolve_path(args.output)

    if not args.no_wait:
        wait_for_current_weak_run(
            output_path,
            target_bases=args.wait_target_bases,
            poll_seconds=args.poll_seconds,
        )

    generate_missing_targeted_strong(
        output_dir=generated_root,
        combinations=combinations,
        samples_per_combination=args.samples_per_combination,
        queries_per_belief_base=args.queries_per_belief_base,
        max_attempts=args.max_attempts,
    )
    copied = export_targeted_strong_to_clkr(
        generated_root=generated_root,
        clkr_root=clkr_root,
        combinations=combinations,
    )
    print(f"exported {copied} targeted-strong bases to {clkr_root}", flush=True)

    run_dataset(
        dataset="targeted-strong",
        consistency="strong",
        dataset_root=clkr_root,
        output_path=output_path,
        total_timeout=args.total_timeout,
        preprocessing_timeout=args.preprocessing_timeout,
        inference_timeout=args.inference_timeout,
        smt_solver=args.smt_solver,
        pmaxsat_solver=args.pmaxsat_solver,
        multi_inference=args.multi_inference,
        limit=None,
        resume=True,
        combinations=set(combinations),
    )


if __name__ == "__main__":
    main()
