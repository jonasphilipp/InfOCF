from __future__ import annotations

import argparse
import csv
import random
from pathlib import Path

from benchmarks.trueRandomSampling import (
    DEFAULT_MAX_ATTEMPTS,
    DEFAULT_QUERIES_PER_BELIEF_BASE,
    createVariables,
    is_nontrivial_query,
    makeCKB,
    makeQueryfile,
)
from inference.belief_base import BeliefBase
from inference.consistency_sat import consistency
from parser.Wrappers import parseQuery

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUTPUT_DIR = Path("benchmarks/generated/lexinf_natural_repeated_vars_pilot")
DEFAULT_DATASET = "natural-repeated-vars-pilot"
DEFAULT_COMBINATIONS = [
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
    (80, 60),
    (80, 80),
    (100, 60),
    (120, 60),
]
MANIFEST_HEADER = [
    "dataset",
    "consistency",
    "signature_size",
    "conditionals",
    "index",
    "combo_total_index",
    "attempts_for_entry",
    "partition_lengths",
    "consistency_calls",
    "consistency_levels",
    "formula_max_depth",
    "belief_base_path",
    "queries_path",
]


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


def resolve_path(path: str | Path) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return REPO_ROOT / candidate


def sample_formula_repeated_vars(
    variables: list[str],
    *,
    max_depth: int,
    leaf_probability: float,
    negation_probability: float,
) -> str:
    if max_depth <= 0 or random.random() < leaf_probability:
        atom = random.choice(variables)
        if random.random() < negation_probability:
            return f"(!{atom})"
        return atom

    operation = random.choice(["and", "or", "not"])
    if operation == "not":
        inner = sample_formula_repeated_vars(
            variables,
            max_depth=max_depth - 1,
            leaf_probability=leaf_probability,
            negation_probability=negation_probability,
        )
        return f"(!{inner})"

    left = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth - 1,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    right = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth - 1,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    if operation == "and":
        return f"({left},{right})"
    return f"({left};{right})"


def sample_conditional_repeated_vars(
    variables: list[str],
    *,
    max_depth: int,
    leaf_probability: float,
    negation_probability: float,
) -> str:
    antecedent = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    consequent = sample_formula_repeated_vars(
        variables,
        max_depth=max_depth,
        leaf_probability=leaf_probability,
        negation_probability=negation_probability,
    )
    return f"({consequent} | {antecedent})"


def sample_conditionals_repeated_vars(
    signature_size: int,
    conditionals_count: int,
    *,
    formula_max_depth: int,
    leaf_probability: float,
    negation_probability: float,
) -> tuple[list[str], list]:
    variables = createVariables(signature_size)
    conditional_texts = [
        sample_conditional_repeated_vars(
            variables,
            max_depth=formula_max_depth,
            leaf_probability=leaf_probability,
            negation_probability=negation_probability,
        )
        for _ in range(conditionals_count)
    ]
    conditionals = [parseQuery(text)[1] for text in conditional_texts]
    return variables, conditionals


def classify_conditionals(variables: list[str], conditionals: list) -> tuple[str, list]:
    belief_base = BeliefBase(
        variables,
        {i: conditional for i, conditional in enumerate(conditionals, start=1)},
        "",
    )
    partition, stats = consistency(belief_base, weakly=True)
    if partition is False:
        return "inconsistent", stats
    if len(partition[-1]) == 0:
        return "strong", stats
    return "weak", stats


def sample_queries_repeated_vars(
    variables: list[str],
    amount: int,
    *,
    existing_conditionals: list,
    formula_max_depth: int,
    leaf_probability: float,
    negation_probability: float,
    max_attempts: int,
) -> list:
    existing = {conditional.textRepresentation for conditional in existing_conditionals}
    seen = set(existing)
    queries = []
    attempts = 0

    while len(queries) < amount:
        attempts += 1
        if attempts > max_attempts:
            raise RuntimeError(
                f"failed to sample {amount} non-trivial repeated-var queries "
                f"after {max_attempts} attempts"
            )

        query = parseQuery(
            sample_conditional_repeated_vars(
                variables,
                max_depth=formula_max_depth,
                leaf_probability=leaf_probability,
                negation_probability=negation_probability,
            )
        )[1]
        text = query.textRepresentation
        if text in seen:
            continue
        if not is_nontrivial_query(query):
            continue

        seen.add(text)
        queries.append(query)

    return queries


def read_manifest(manifest_path: Path) -> tuple[set[tuple], dict[tuple, int], dict]:
    completed = set()
    totals: dict[tuple[int, int], int] = {}
    consistency_counts: dict[tuple[int, int, str], int] = {}
    if not manifest_path.exists():
        return completed, totals, consistency_counts

    with manifest_path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            try:
                consistency_name = row["consistency"]
                signature_size = int(row["signature_size"])
                conditionals_count = int(row["conditionals"])
                index = int(row["index"])
                combo_total_index = int(row["combo_total_index"])
            except (KeyError, TypeError, ValueError):
                continue
            completed.add(
                (
                    consistency_name,
                    signature_size,
                    conditionals_count,
                    index,
                )
            )
            combo_key = (signature_size, conditionals_count)
            totals[combo_key] = max(totals.get(combo_key, 0), combo_total_index + 1)
            consistency_key = (
                signature_size,
                conditionals_count,
                consistency_name,
            )
            consistency_counts[consistency_key] = max(
                consistency_counts.get(consistency_key, 0), index + 1
            )

    return completed, totals, consistency_counts


def generate_natural_repeated_vars_pilot(
    *,
    output_dir: Path,
    dataset: str,
    combinations: list[tuple[int, int]],
    samples_per_combination: int,
    queries_per_belief_base: int,
    formula_max_depth: int,
    leaf_probability: float,
    negation_probability: float,
    max_attempts: int,
) -> None:
    manifest_path = output_dir / "manifest.csv"
    output_dir.mkdir(parents=True, exist_ok=True)
    completed, totals, consistency_counts = read_manifest(manifest_path)

    write_header = not manifest_path.exists() or manifest_path.stat().st_size == 0
    with manifest_path.open("a", newline="") as manifest:
        writer = csv.writer(manifest)
        if write_header:
            writer.writerow(MANIFEST_HEADER)
            manifest.flush()

        for signature_size, conditionals_count in combinations:
            combo_key = (signature_size, conditionals_count)
            attempts_for_combo = 0
            while totals.get(combo_key, 0) < samples_per_combination:
                attempts_for_entry = 0
                while True:
                    attempts_for_entry += 1
                    attempts_for_combo += 1
                    if attempts_for_entry > max_attempts:
                        raise RuntimeError(
                            "failed to sample a weak-or-strong natural-repeated-vars "
                            f"base for {signature_size}/{conditionals_count} "
                            f"after {max_attempts} attempts"
                        )
                    variables, conditionals = sample_conditionals_repeated_vars(
                        signature_size,
                        conditionals_count,
                        formula_max_depth=formula_max_depth,
                        leaf_probability=leaf_probability,
                        negation_probability=negation_probability,
                    )
                    consistency_name, stats = classify_conditionals(
                        variables, conditionals
                    )
                    if consistency_name != "inconsistent":
                        break

                combo_total_index = totals.get(combo_key, 0)
                consistency_key = (
                    signature_size,
                    conditionals_count,
                    consistency_name,
                )
                index = consistency_counts.get(consistency_key, 0)
                manifest_key = (
                    consistency_name,
                    signature_size,
                    conditionals_count,
                    index,
                )
                if manifest_key in completed:
                    consistency_counts[consistency_key] = index + 1
                    totals[combo_key] = combo_total_index + 1
                    continue

                combo_dir = (
                    output_dir
                    / "natural-repeated-vars"
                    / consistency_name
                    / f"{signature_size}_{conditionals_count}"
                )
                belief_base_path = (
                    combo_dir
                    / f"randomTest_{signature_size}_{conditionals_count}_{index}.cl"
                )
                queries_path = (
                    combo_dir
                    / f"randomQueries_{signature_size}_{conditionals_count}_{index}.cl"
                )
                print(
                    "sampling natural-repeated-vars/%s %s/%s #%s "
                    "(combo total %s/%s, attempts entry=%s combo=%s) -> %s, %s"
                    % (
                        consistency_name,
                        signature_size,
                        conditionals_count,
                        index,
                        combo_total_index + 1,
                        samples_per_combination,
                        attempts_for_entry,
                        attempts_for_combo,
                        belief_base_path,
                        queries_path,
                    ),
                    flush=True,
                )
                queries = sample_queries_repeated_vars(
                    variables,
                    queries_per_belief_base,
                    existing_conditionals=conditionals,
                    formula_max_depth=formula_max_depth,
                    leaf_probability=leaf_probability,
                    negation_probability=negation_probability,
                    max_attempts=max_attempts,
                )
                makeCKB(variables, conditionals, [], str(belief_base_path))
                makeQueryfile(queries, str(queries_path))
                partition_lengths, consistency_calls, consistency_levels = stats
                writer.writerow(
                    [
                        dataset,
                        consistency_name,
                        signature_size,
                        conditionals_count,
                        index,
                        combo_total_index,
                        attempts_for_entry,
                        ";".join(str(value) for value in partition_lengths),
                        consistency_calls,
                        consistency_levels,
                        formula_max_depth,
                        belief_base_path,
                        queries_path,
                    ]
                )
                manifest.flush()
                completed.add(manifest_key)
                consistency_counts[consistency_key] = index + 1
                totals[combo_key] = combo_total_index + 1


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate a natural pilot set with repeated variables in formulas."
    )
    parser.add_argument("--output-dir", default=str(DEFAULT_OUTPUT_DIR))
    parser.add_argument("--dataset", default=DEFAULT_DATASET)
    parser.add_argument(
        "--combination",
        action="append",
        type=parse_combination,
        default=[],
        metavar="S/R",
        help="Combination to generate. Defaults to the low/medium pilot grid.",
    )
    parser.add_argument("--samples-per-combination", type=int, default=25)
    parser.add_argument(
        "--queries-per-belief-base",
        type=int,
        default=DEFAULT_QUERIES_PER_BELIEF_BASE,
    )
    parser.add_argument("--formula-max-depth", type=int, default=4)
    parser.add_argument("--leaf-probability", type=float, default=0.35)
    parser.add_argument("--negation-probability", type=float, default=0.25)
    parser.add_argument("--max-attempts", type=int, default=DEFAULT_MAX_ATTEMPTS)
    parser.add_argument("--seed", type=int, default=None)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.seed is not None:
        random.seed(args.seed)
    generate_natural_repeated_vars_pilot(
        output_dir=resolve_path(args.output_dir),
        dataset=args.dataset,
        combinations=args.combination or DEFAULT_COMBINATIONS,
        samples_per_combination=args.samples_per_combination,
        queries_per_belief_base=args.queries_per_belief_base,
        formula_max_depth=args.formula_max_depth,
        leaf_probability=args.leaf_probability,
        negation_probability=args.negation_probability,
        max_attempts=args.max_attempts,
    )


if __name__ == "__main__":
    main()
