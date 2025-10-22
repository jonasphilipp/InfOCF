"""
Weakly semantics CSV-driven correctness tests.

CSV schema (one row per system+query):
- inference_system (required): e.g., system-z, system-w, lex_inf, c-inference
- belief_base_str | belief_base_filepath (exactly one required)
- queries_str | queries_filepath (exactly one required)
- query (required unless index is provided): the single query string to validate from the batch
- index (alternative to query): integer index of the query within the operator output
- result (required): True/False expected outcome
- pmaxsat_solver (optional): rc2|z3; if omitted, all registered variants must match
- weakly (optional): True|False (default True)
- smt_solver (optional): default z3
- case_id, skip, notes (optional): free text / control flags

Environment variables:
- INFOCF_WEAKLY_CSV: comma-separated CSV paths (abs or repo-relative)
- INFOCF_WEAKLY_SIZE: small|large|both (defaults: prefer small if present)
- INFOCF_WEAKLY_EXCLUDE: comma-separated systems to exclude from comparison

Behavior:
- Groups by (belief base, queries, weakly, smt_solver) to compute once, reuse many.
- If pmaxsat_solver is specified, only that variant is asserted; otherwise, all variants
  registered for the system must match the expected result.
"""

import hashlib
import os
import sys
import unittest

import pandas as pd

from inference.inference_manager import InferenceManager
from parser.Wrappers import parse_belief_base, parse_queries


class WeaklyInferenceCSVTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Base project directory (repo root)
        cls.BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        sys.path.append(cls.BASE_DIR)

        # Default solver / execution settings
        cls.smt_solver_default = "z3"
        cls.total_timeout = 0
        cls.preprocessing_timeout = 0
        cls.inference_timeout = 0
        cls.multi_inference = False

        # Systems and variant registry (extendable)
        cls.DEFAULT_SYSTEMS = [
            "system-z",
            "system-w",
            "lex_inf",
            "c-inference",
        ]
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
            # Keep c-inference variants minimal by default; extend as implementation evolves.
            "c-inference": [
                {"label": "rc2", "pmaxsat_solver": "rc2"},
            ],
        }

        # Optional exclusions: comma-separated env (e.g., "system-w,lex_inf")
        exclude_env = os.environ.get("INFOCF_WEAKLY_EXCLUDE", "").strip()
        cls.excluded_systems = (
            [s.strip() for s in exclude_env.split(",") if s.strip()]
            if exclude_env
            else []
        )

        # File-name substrings that should be skipped quickly (matches original style)
        cls.SKIP_CONDITIONS = ["inconsistent", "empty"]

    def _paths_from_env_or_default(self) -> list[str]:
        """
        Select CSV(s) to run from environment overrides or default small/large convention.

        Env overrides:
          - INFOCF_WEAKLY_CSV=/abs/a.csv,/abs/b.csv (absolute or relative to repo root)
          - INFOCF_WEAKLY_SIZE=small|large|both
        Defaults to prefer small if present, else large.
        """
        override = os.environ.get("INFOCF_WEAKLY_CSV", "").strip()
        if override:
            result: list[str] = []
            for part in override.split(","):
                p = part.strip()
                if not p:
                    continue
                if not os.path.isabs(p):
                    p = os.path.join(self.BASE_DIR, p)
                result.append(p)
            return result

        env_size = os.environ.get("INFOCF_WEAKLY_SIZE", "").lower()
        small_csv = os.path.join(
            os.path.dirname(__file__), "weakly_testing_results_small.csv"
        )
        large_csv = os.path.join(
            os.path.dirname(__file__), "weakly_testing_results.csv"
        )

        if env_size in {"large", "big"}:
            return [large_csv]
        if env_size in {"small", "tiny"}:
            return [small_csv] if os.path.isfile(small_csv) else [large_csv]
        if env_size in {"both", "all"}:
            paths: list[str] = []
            if os.path.isfile(small_csv):
                paths.append(small_csv)
            if os.path.isfile(large_csv):
                paths.append(large_csv)
            return paths or [large_csv]

        # Default behavior: prefer small if present, otherwise large
        return [small_csv] if os.path.isfile(small_csv) else [large_csv]

    @staticmethod
    def _truthy(value) -> bool:
        if isinstance(value, bool):
            return value
        if value is None:
            return False
        s = str(value).strip().lower()
        return s in {"1", "true", "t", "yes", "y"}

    @staticmethod
    def _nonstr_empty(row, col) -> bool:
        return col in row and isinstance(row[col], str) and row[col].strip() != ""

    @staticmethod
    def _md5_of(text: str) -> str:
        return hashlib.md5(text.encode("utf-8")).hexdigest()

    def _resolve_belief_base(self, row: dict) -> tuple[str, object]:
        """
        Return (group_key_component, belief_base_object).
        group_key_component identifies the BB so we can cache per BB+Q+settings.
        """
        # Inline takes precedence if provided
        if self._nonstr_empty(row, "belief_base_str"):
            bb_str = row["belief_base_str"]
            key = f"bb:inline:{self._md5_of(bb_str)}"
            return key, parse_belief_base(bb_str)

        # Else fallback to file path
        bb_path = row.get("belief_base_filepath", "").strip()
        if not os.path.isabs(bb_path):
            bb_path = os.path.join(self.BASE_DIR, bb_path)
        # Fast skip on file-name conditions
        if any(cond in os.path.basename(bb_path) for cond in self.SKIP_CONDITIONS):
            self.skipTest(f"Belief base skipped by condition: {bb_path}")
        self.assertTrue(os.path.isfile(bb_path), f"Belief base not found: {bb_path}")
        return f"bb:file:{os.path.abspath(bb_path)}", parse_belief_base(bb_path)

    def _resolve_queries(self, row: dict) -> tuple[str, object]:
        # Inline takes precedence if provided
        if self._nonstr_empty(row, "queries_str"):
            qs_str = row["queries_str"]
            key = f"qs:inline:{self._md5_of(qs_str)}"
            return key, parse_queries(qs_str)

        # Else fallback to file path
        qs_path = row.get("queries_filepath", "").strip()
        if not os.path.isabs(qs_path):
            qs_path = os.path.join(self.BASE_DIR, qs_path)
        self.assertTrue(os.path.isfile(qs_path), f"Queries file not found: {qs_path}")
        return f"qs:file:{os.path.abspath(qs_path)}", parse_queries(qs_path)

    def test_weakly_csv_correctness(self):
        csv_paths = self._paths_from_env_or_default()
        self.assertTrue(csv_paths, "No CSV files selected for weakly tests")

        for csv_path in csv_paths:
            self.assertTrue(os.path.isfile(csv_path), f"Test CSV not found: {csv_path}")
            df = pd.read_csv(csv_path)

            # Normalize column names (lowercase) for flexible CSVs
            df.columns = [c.strip() for c in df.columns]

            # Systems to run = defaults ∪ those requested in CSV
            csv_systems = (
                {
                    s.strip().lower()
                    for s in df.get("inference_system", pd.Series([], dtype=str))
                    .astype(str)
                    .tolist()
                    if s.strip()
                }
                if "inference_system" in df.columns
                else set()
            )
            systems_to_run = sorted(set(self.DEFAULT_SYSTEMS) | csv_systems)

            # Cache results per (bb_key, qs_key, weakly, smt)
            results_cache: dict[tuple[str, str, bool, str], pd.DataFrame] = {}

            for index, row in df.iterrows():
                with self.subTest(row=index):
                    # Optional per-row skip
                    if "skip" in row and self._truthy(row["skip"]):
                        continue

                    # Required row fields
                    self.assertIn(
                        "inference_system",
                        row,
                        "CSV row must include 'inference_system'",
                    )
                    has_query = (
                        "query" in row
                        and isinstance(row["query"], str)
                        and row["query"].strip() != ""
                    )
                    has_index = "index" in row and str(row["index"]).strip() != ""
                    self.assertTrue(
                        has_query or has_index,
                        "CSV row must include either 'query' (string) or 'index' (integer)",
                    )
                    self.assertIn(
                        "result",
                        row,
                        "CSV row must include expected 'result' (True/False)",
                    )

                    # Resolve BB and Q (keys used for caching)
                    bb_key, belief_base = self._resolve_belief_base(row)
                    qs_key, queries = self._resolve_queries(row)

                    # Row-level execution settings
                    weakly = (
                        True
                        if "weakly" not in row or str(row["weakly"]).strip() == ""
                        else self._truthy(row["weakly"])
                    )
                    smt_solver = (
                        row["smt_solver"].strip().lower()
                        if "smt_solver" in row
                        and isinstance(row["smt_solver"], str)
                        and row["smt_solver"].strip() != ""
                        else self.smt_solver_default
                    )
                    cache_key = (bb_key, qs_key, weakly, smt_solver)

                    # Compute and cache results if needed
                    if cache_key not in results_cache:
                        collected = pd.DataFrame()
                        for system in systems_to_run:
                            # Skip excluded systems for comparison, but still compute to fill cache
                            variants = self.IMPLEMENTATIONS.get(
                                system, [{"label": "default"}]
                            )
                            for variant in variants:
                                pmaxsat_solver = variant.get("pmaxsat_solver", "")
                                manager = InferenceManager(
                                    belief_base,
                                    inference_system=system,
                                    smt_solver=smt_solver,
                                    pmaxsat_solver=pmaxsat_solver,
                                    weakly=weakly,
                                )
                                print(
                                    f"{system:<12} variant={variant.get('label', 'default'):<6} "
                                    f"pmaxsat={pmaxsat_solver or '-':<3} weakly={weakly} "
                                    f"on {bb_key}, {qs_key}"
                                )
                                res = manager.inference(
                                    queries,
                                    total_timeout=self.total_timeout,
                                    preprocessing_timeout=self.preprocessing_timeout,
                                    inference_timeout=self.inference_timeout,
                                    multi_inference=self.multi_inference,
                                )
                                collected = pd.concat(
                                    [collected, res], ignore_index=True
                                )
                        results_cache[cache_key] = collected

                    collected_results = results_cache[cache_key]

                    # Filter down to the current query either by string or by numeric index
                    if has_query:
                        query_str = str(row["query"]).strip()
                        current_result = collected_results[
                            collected_results["query"].astype(str) == query_str
                        ]
                        selector_desc = f"query='{query_str}'"
                    else:
                        try:
                            idx_val = int(str(row["index"]).strip())
                        except Exception:
                            self.fail(
                                f"Invalid 'index' value in CSV row: {row['index']}"
                            )
                        # 'index' column in results comes from operator; it may be floats after concat → cast
                        current_result = collected_results[
                            collected_results["index"].astype(int) == idx_val
                        ]
                        selector_desc = f"index={idx_val}"
                    self.assertFalse(
                        current_result.empty,
                        (
                            f"No result found for selector: {selector_desc}. "
                            f"BB={bb_key}, QS={qs_key}"
                        ),
                    )

                    # Now check the specific system from the row
                    system = str(row["inference_system"]).strip().lower()
                    system_results = current_result[
                        current_result["inference_system"].astype(str) == system
                    ]
                    self.assertFalse(
                        system_results.empty,
                        f"No result found for inference_system: {system}",
                    )

                    expected = self._truthy(row["result"])  # normalize to bool

                    # Optional: if pmaxsat_solver specified in row, only check that variant
                    row_pmax = (
                        str(row["pmaxsat_solver"]).strip().lower()
                        if "pmaxsat_solver" in row
                        and isinstance(row["pmaxsat_solver"], str)
                        else ""
                    )

                    # Exclusion rule: if system is excluded, don't compare values
                    if system in self.excluded_systems:
                        print(
                            f"Result not compared (system excluded): {system}, query={query_str}"
                        )
                        continue

                    if row_pmax:
                        variant_results = system_results[
                            system_results["pmaxsat_solver"].astype(str) == row_pmax
                        ]
                        self.assertFalse(
                            variant_results.empty,
                            (
                                f"No result found for specified pmaxsat_solver='{row_pmax}' "
                                f"on system={system}, {selector_desc}"
                            ),
                        )
                        mismatches = variant_results[
                            variant_results["result"].astype(bool) != expected
                        ]
                        self.assertTrue(
                            mismatches.empty,
                            (
                                f"Mismatch for system={system}, pmaxsat={row_pmax}, "
                                f"{selector_desc}. Expected: {expected}. "
                                f"Got: {variant_results[['pmaxsat_solver', 'result']].to_dict('records')}"
                            ),
                        )
                    else:
                        # Check all registered variants for this system
                        mismatches = system_results[
                            system_results["result"].astype(bool) != expected
                        ]
                        self.assertTrue(
                            mismatches.empty,
                            (
                                f"At least one variant mismatched for {selector_desc}, "
                                f"inference_system={system}. Expected: {expected}. "
                                f"Mismatches: {mismatches[['pmaxsat_solver', 'result']].to_dict('records')}"
                            ),
                        )


if __name__ == "__main__":
    unittest.main()
