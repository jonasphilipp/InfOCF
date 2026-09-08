"""
CSV-driven correctness tests for standard (strict) semantics.

Inputs
------
CSV files: `unittests/example_testing_results_small.csv` (preferred if present)
          or `unittests/example_testing_results.csv`.

Required CSV columns (per row):
- index: expected sequential position of the test case (used for ordering checks)
- result: True/False expected outcome
- belief_base_filepath: path to the belief base file (repo-relative)
- queries_filepath: path to the queries file (repo-relative)
- query: the single query (string) within the batch to validate
- inference_system: one of {"p-entailment","system-z","system-w","lex_inf","c-inference"}

Optional CSV columns:
- smt_solver: SMT backend (default: z3)
- pmaxsat_solver: variant for systems supporting it (e.g., rc2|z3)

Environment variables
---------------------
- INFOCF_CORRECTNESS_SIZE: small|large|both
  Controls which CSV(s) are used; by default the test prefers the small file if present.

Behavior
--------
- Rows are grouped by (belief base file, queries file) to avoid redundant computation.
- For each group, results are computed for all configured systems and variants.
- For the row's system, all registered variants must match the expected result.
- The `index` column is used to ensure sequential ordering of rows.
"""

import os
import sys
import unittest
from typing import Any, cast

try:
    import pandas as pd  # type: ignore
except Exception:  # pragma: no cover - gracefully handle missing pandas in env
    pd = cast(Any, None)

from inference.inference_operator import InferenceOperator
from parser.Wrappers import parse_belief_base, parse_queries


@unittest.skipIf(
    pd is None, "pandas not installed; run 'uv sync' or include testing extras"
)
class InferenceCorrectnessTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Set base directory relative to the test file’s location
        cls.BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        sys.path.append(cls.BASE_DIR)

        # Optional settings for pandas display (if needed when debugging)
        pd.set_option("display.max_columns", None)
        pd.set_option("display.max_rows", None)
        pd.set_option("display.width", 0)

        # Configuration for inference testing
        cls.inference_systems = [
            "p-entailment",
            "system-z",
            "system-w",
            "lex_inf",
            "c-inference",
        ]
        # Registry: map semantic systems to concrete implementations/variants
        # Each variant may override pmaxsat_solver; smt_solver and weakly are kept from class settings
        cls.IMPLEMENTATIONS = {
            "p-entailment": [{"label": "default"}],
            "system-z": [{"label": "default"}],
            "system-w": [
                {"label": "rc2", "pmaxsat_solver": "rc2"},
                {"label": "z3", "pmaxsat_solver": "z3"},
            ],
            "lex_inf": [
                {"label": "rc2", "pmaxsat_solver": "rc2"},
                {"label": "z3", "pmaxsat_solver": "z3"},
            ],
            "c-inference": [{"label": "rc2", "pmaxsat_solver": "rc2"}],
        }
        cls.excluded_systems = []  # list any inference systems that should be excluded

        # Prefer a small curated CSV if available; fall back to the large one
        env_size = os.environ.get("INFOCF_CORRECTNESS_SIZE", "").lower()
        small_csv = os.path.join(
            os.path.dirname(__file__), "example_testing_results_small.csv"
        )
        large_csv = os.path.join(
            os.path.dirname(__file__), "example_testing_results.csv"
        )

        if env_size in {"large", "big"}:
            cls.test_sets = ["example_testing_results.csv"]
        elif env_size in {"small", "tiny"}:
            # If explicitly small is requested but the file is missing, fall back to large
            cls.test_sets = (
                ["example_testing_results_small.csv"]
                if os.path.isfile(small_csv)
                else ["example_testing_results.csv"]
            )
        elif env_size in {"both", "all"}:
            # Run both when available, small first for quicker feedback
            sets = []
            if os.path.isfile(small_csv):
                sets.append("example_testing_results_small.csv")
            if os.path.isfile(large_csv):
                sets.append("example_testing_results.csv")
            # If neither exists (unlikely), default to large name and let the test assert existence later
            cls.test_sets = sets or ["example_testing_results.csv"]
        else:
            # Default behavior preserved: prefer small if present, otherwise large
            if os.path.isfile(small_csv):
                cls.test_sets = ["example_testing_results_small.csv"]
            else:
                cls.test_sets = ["example_testing_results.csv"]
        cls.SKIP_CONDITIONS = ["inconsistent", "empty"]

        # Timeouts in seconds (0 means no timeout)
        cls.total_timeout = 300
        cls.preprocessing_timeout = 0
        cls.inference_timeout = 0

        # Solver settings
        cls.smt_solver = "z3"
        cls.pmaxsat_solver = "rc2"
        cls.multi_inference = False
        env_multi = os.environ.get("INFOCF_MULTI", "").lower()
        if env_multi in {"1", "true", "yes", "on"}:
            cls.multi_inference = True

    def test_inference_correctness(self):
        for test_set in self.test_sets:
            test_set_path = os.path.join(os.path.dirname(__file__), test_set)
            self.assertTrue(
                os.path.isfile(test_set_path),
                f"Test set file not found: {test_set_path}",
            )
            df = pd.read_csv(test_set_path)
            collected_results = pd.DataFrame()
            belief_base_filepath = ""
            queries_filepath = ""
            last_index = -1

            for index, row in df.iterrows():
                with self.subTest(row=index):
                    # When either belief base or queries file changes, re-run inference.
                    if (
                        row["belief_base_filepath"] != belief_base_filepath
                        or row["queries_filepath"] != queries_filepath
                    ):
                        collected_results = pd.DataFrame()
                        belief_base_filepath = str(row["belief_base_filepath"])
                        queries_filepath = str(row["queries_filepath"])
                        belief_base_filepath_full = os.path.join(
                            self.BASE_DIR, belief_base_filepath
                        )
                        queries_filepath_full = os.path.join(
                            self.BASE_DIR, queries_filepath
                        )

                        self.assertTrue(
                            os.path.isfile(belief_base_filepath_full),
                            f"{belief_base_filepath} is not a valid file",
                        )
                        self.assertTrue(
                            os.path.isfile(queries_filepath_full),
                            f"{queries_filepath} is not a valid file",
                        )

                        # Skip files based on defined conditions
                        if any(
                            cond in belief_base_filepath
                            for cond in self.SKIP_CONDITIONS
                        ):
                            continue

                        belief_base = parse_belief_base(belief_base_filepath_full)
                        queries = parse_queries(queries_filepath_full)

                        # For each inference system, run all registered implementation variants
                        for inference_system in self.inference_systems:
                            variants = self.IMPLEMENTATIONS.get(
                                inference_system, [{"label": "default"}]
                            )
                            for variant in variants:
                                pmaxsat_solver = variant.get(
                                    "pmaxsat_solver", self.pmaxsat_solver
                                )

                                inference_operator = InferenceOperator(
                                    belief_base,
                                    inference_system=inference_system,
                                    smt_solver=self.smt_solver,
                                    pmaxsat_solver=pmaxsat_solver,
                                    weakly=False,
                                )

                                print(
                                    f"{inference_system:<12} variant={variant.get('label', 'default'):<6} pmaxsat={pmaxsat_solver or '-':<3} on {belief_base_filepath}, {queries_filepath}"
                                )
                                results = inference_operator.inference(
                                    queries,
                                    total_timeout=self.total_timeout,
                                    preprocessing_timeout=self.preprocessing_timeout,
                                    inference_timeout=self.inference_timeout,
                                    multi_inference=self.multi_inference,
                                )
                                collected_results = pd.concat(
                                    [collected_results, results], ignore_index=True
                                )

                    # Filter the collected results for the current test case
                    current_result = collected_results[
                        (collected_results["belief_base"] == row["belief_base"])
                        & (collected_results["query"] == row["query"])
                    ]
                    self.assertFalse(
                        current_result.empty,
                        f"No result found for belief_base: {row['belief_base']} and query: {row['query']}",
                    )

                    for inference_system in self.inference_systems:
                        system_results = current_result[
                            current_result["inference_system"] == inference_system
                        ]
                        self.assertFalse(
                            system_results.empty,
                            f"No result found for inference_system: {inference_system}",
                        )

                        # Only compare results for the inference system that is expected per the row.
                        if inference_system == row["inference_system"]:
                            # Check index order for sequential test cases.
                            self.assertEqual(
                                index,
                                last_index + 1,
                                f"Index mismatch: {index} != {last_index + 1}",
                            )
                            if inference_system in self.excluded_systems:
                                print("Result not compared, inference system excluded")
                            else:
                                # Validate that ALL registered variants for this system match the expected result
                                mismatches = system_results[
                                    system_results["result"] != row["result"]
                                ]
                                self.assertTrue(
                                    mismatches.empty,
                                    (
                                        f"At least one variant mismatched for belief_base: {row['belief_base']}, "
                                        f"query: {row['query']}, inference_system: {inference_system}. "
                                        f"Expected: {row['result']}. Mismatches (pmaxsat_solver -> result): "
                                        f"{mismatches[['pmaxsat_solver', 'result']].to_dict('records')}"
                                    ),
                                )
                            last_index = index


if __name__ == "__main__":
    unittest.main()
