import argparse
import os
from typing import List

import pandas as pd


def build_small_set(
    df: pd.DataFrame,
    target_rows: int = 100,
    systems: List[str] | None = None,
    seed: int = 42,
) -> pd.DataFrame:
    """
    Create a smaller correctness CSV by sampling rows evenly across
    inference systems and both result classes (True/False), avoiding timeouts.

    Strategy:
    - Filter out rows with preprocessing_timed_out or inference_timed_out
    - For each inference system and result in {True, False}, sample
      target_rows // (len(systems)*2) rows (or as many as available)
    - Fill any remaining budget with random rows from the remaining pool
    """

    # Keep only stable rows
    filt = (df["preprocessing_timed_out"] == False) & (
        df["inference_timed_out"] == False
    )
    df = df[filt].copy()

    if systems is None:
        systems = [
            "p-entailment",
            "system-z",
            "system-w",
            "lex_inf",
            "c-inference",
        ]

    # Deterministic shuffles
    rng = pd.Series(range(len(df)), index=df.index).sample(frac=1.0, random_state=seed)
    df = df.loc[rng.index]

    # Compute per-bucket target
    per_bucket = max(1, target_rows // (len(systems) * 2))

    selected_idx: list[int] = []
    remaining = df

    for sys_name in systems:
        for res in [True, False]:
            bucket = remaining[
                (remaining["inference_system"] == sys_name)
                & (remaining["result"] == res)
            ]
            if len(bucket) == 0:
                continue
            take = min(per_bucket, len(bucket))
            sampled = bucket.sample(n=take, random_state=seed)
            selected_idx.extend(sampled.index.tolist())
            remaining = remaining.drop(index=sampled.index)

    # Fill up to target_rows if we have budget left
    if len(selected_idx) < target_rows and len(remaining) > 0:
        deficit = target_rows - len(selected_idx)
        fill_take = min(deficit, len(remaining))
        filler = remaining.sample(n=fill_take, random_state=seed)
        selected_idx.extend(filler.index.tolist())

    small_df = df.loc[selected_idx]

    # Keep a stable, readable order by KB then system then index
    cols_for_sort = [
        "belief_base",
        "queries",
        "inference_system",
        "index",
    ]
    small_df = small_df.sort_values(
        by=[c for c in cols_for_sort if c in small_df.columns]
    )
    return small_df


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Create a small correctness CSV subset"
    )
    parser.add_argument(
        "--input",
        default=os.path.join(os.path.dirname(__file__), "example_testing_results.csv"),
        help="Path to the full correctness CSV (default: unittests/example_testing_results.csv)",
    )
    parser.add_argument(
        "--output",
        default=os.path.join(
            os.path.dirname(__file__), "example_testing_results_small.csv"
        ),
        help="Path to write the small CSV (default: unittests/example_testing_results_small.csv)",
    )
    parser.add_argument(
        "--rows", type=int, default=100, help="Target number of rows (default: 100)"
    )
    parser.add_argument(
        "--seed", type=int, default=42, help="Random seed for deterministic sampling"
    )
    args = parser.parse_args()

    if not os.path.isfile(args.input):
        raise FileNotFoundError(f"Input CSV not found: {args.input}")

    df = pd.read_csv(args.input)

    # Ensure booleans are proper dtype
    # If CSV read result as strings, coerce common forms
    if df["result"].dtype == object:
        df["result"] = df["result"].map(
            lambda x: True if str(x).strip().lower() == "true" else False
        )

    for col in ("preprocessing_timed_out", "inference_timed_out"):
        if df[col].dtype == object:
            df[col] = df[col].map(
                lambda x: True if str(x).strip().lower() == "true" else False
            )

    small = build_small_set(df, target_rows=args.rows, seed=args.seed)

    # Write with the same column order as input
    small = small[df.columns]
    small.to_csv(args.output, index=False)
    print(f"Wrote {len(small)} rows to {args.output}")


if __name__ == "__main__":
    main()
