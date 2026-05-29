from __future__ import annotations

import argparse
from pathlib import Path

import pandas as pd

from benchmarks.benchmark_lexinf_natural_repeated_vars import DEFAULT_COMBINATIONS

REPO_ROOT = Path(__file__).resolve().parent.parent
WIDE_ROW_SPECS = [
    ("# strong bases", "strong", "belief_bases", 0),
    ("strong avg solved query ms", "strong", "avg_solved_query_time_ms", 1),
    ("strong solved %", "strong", "solved_query_percent", 1),
    ("strong timeout %", "strong", "timeout_query_percent", 1),
    ("# weak bases", "weak", "belief_bases", 0),
    ("weak avg solved query ms", "weak", "avg_solved_query_time_ms", 1),
    ("weak solved %", "weak", "solved_query_percent", 1),
    ("weak timeout %", "weak", "timeout_query_percent", 1),
]


def resolve_path(path: str) -> Path:
    candidate = Path(path)
    if candidate.is_absolute():
        return candidate
    return REPO_ROOT / candidate


def summarize(results_path: Path) -> pd.DataFrame:
    df = pd.read_csv(results_path)
    required_columns = {
        "signature_size",
        "number_conditionals",
        "belief_base_consistency",
        "belief_base",
        "preprocessing_time",
        "inference_time",
        "preprocessing_timed_out",
        "inference_timed_out",
    }
    missing = sorted(required_columns.difference(df.columns))
    if missing:
        raise ValueError(f"missing required columns in {results_path}: {missing}")

    df["query_time_ms"] = df["preprocessing_time"] + df["inference_time"]
    df["timed_out"] = df["preprocessing_timed_out"].astype(bool) | df[
        "inference_timed_out"
    ].astype(bool)
    df["solved_query_time_ms"] = df["query_time_ms"].where(~df["timed_out"])
    df["solved_inference_time_ms"] = df["inference_time"].where(~df["timed_out"])
    group_columns = [
        "signature_size",
        "number_conditionals",
        "belief_base_consistency",
    ]

    grouped = df.groupby(group_columns, dropna=False)
    summary = grouped.agg(
        belief_bases=("belief_base", "nunique"),
        queries=("belief_base", "size"),
        avg_solved_query_time_ms=("solved_query_time_ms", "mean"),
        median_solved_query_time_ms=("solved_query_time_ms", "median"),
        avg_solved_inference_time_ms=("solved_inference_time_ms", "mean"),
        median_solved_inference_time_ms=("solved_inference_time_ms", "median"),
        timeout_queries=("timed_out", "sum"),
    ).reset_index()

    bases_with_timeout = (
        df.groupby(group_columns + ["belief_base"], dropna=False)["timed_out"]
        .any()
        .groupby(group_columns, dropna=False)
        .sum()
        .rename("bases_with_timeout")
        .reset_index()
    )
    summary = summary.merge(bases_with_timeout, on=group_columns, how="left")
    summary["timeout_query_percent"] = (
        summary["timeout_queries"] / summary["queries"] * 100
    )
    summary["solved_query_percent"] = 100 - summary["timeout_query_percent"]
    summary["timeout_base_percent"] = (
        summary["bases_with_timeout"] / summary["belief_bases"] * 100
    )

    return summary.sort_values(
        ["signature_size", "number_conditionals", "belief_base_consistency"]
    )


def format_number(value: float | int | None, digits: int = 1) -> str:
    if value is None or pd.isna(value):
        return "-"
    if digits == 0:
        return f"{value:.0f}"
    return f"{value:.{digits}f}"


def included_combinations(summary: pd.DataFrame) -> list[tuple[int, int]]:
    return [
        combination
        for combination in DEFAULT_COMBINATIONS
        if (
            (summary["signature_size"] == combination[0])
            & (summary["number_conditionals"] == combination[1])
        ).any()
    ]


def build_lookup(summary: pd.DataFrame) -> dict[tuple[int, int, str], object]:
    return {
        (
            int(row.signature_size),
            int(row.number_conditionals),
            str(row.belief_base_consistency),
        ): row
        for row in summary.itertuples(index=False)
    }


def build_wide_table_csv(summary: pd.DataFrame) -> pd.DataFrame:
    combinations = included_combinations(summary)
    lookup = build_lookup(summary)

    rows = []
    for label, consistency, field, digits in WIDE_ROW_SPECS:
        row_values = {"metric": label}
        for combination in combinations:
            summary_row = lookup.get((*combination, consistency))
            row_values[f"{combination[0]}/{combination[1]}"] = format_number(
                getattr(summary_row, field, None), digits=digits
            )
        rows.append(row_values)
    return pd.DataFrame(rows)


def build_wide_table(summary: pd.DataFrame) -> str:
    combinations = included_combinations(summary)
    lookup = build_lookup(summary)

    headers = ["metric", *[f"{s}/{c}" for s, c in combinations]]
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join(["---", *["---:" for _ in combinations]]) + " |",
    ]
    for label, consistency, field, digits in WIDE_ROW_SPECS:
        cells = [label]
        for combination in combinations:
            row = lookup.get((*combination, consistency))
            cells.append(format_number(getattr(row, field, None), digits=digits))
        lines.append("| " + " | ".join(cells) + " |")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Summarize lex_inf benchmark results by consistency and combination."
    )
    parser.add_argument(
        "--input",
        default="local/results_lexinf_natural_repeated_vars.csv",
        help="Benchmark results CSV.",
    )
    parser.add_argument(
        "--summary-output",
        default="local/results_lexinf_natural_repeated_vars_summary_by_combination.csv",
        help="Long-form summary CSV output.",
    )
    parser.add_argument(
        "--table-output",
        default="local/results_lexinf_natural_repeated_vars_table.md",
        help="Paper-style wide Markdown table output.",
    )
    parser.add_argument(
        "--table-csv-output",
        default="local/results_lexinf_natural_repeated_vars_table.csv",
        help="Paper-style wide CSV table output.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    results_path = resolve_path(args.input)
    summary_output = resolve_path(args.summary_output)
    table_output = resolve_path(args.table_output)
    table_csv_output = resolve_path(args.table_csv_output)

    summary = summarize(results_path)
    summary_output.parent.mkdir(parents=True, exist_ok=True)
    table_output.parent.mkdir(parents=True, exist_ok=True)
    table_csv_output.parent.mkdir(parents=True, exist_ok=True)
    summary.to_csv(summary_output, index=False)
    table_output.write_text(build_wide_table(summary), encoding="utf-8")
    build_wide_table_csv(summary).to_csv(table_csv_output, index=False)

    print(f"wrote {summary_output}")
    print(f"wrote {table_output}")
    print(f"wrote {table_csv_output}")


if __name__ == "__main__":
    main()
