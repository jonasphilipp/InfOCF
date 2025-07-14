import os
import sys
import unittest

import pandas as pd

from inference.inference_operator import InferenceOperator
from parser.Wrappers import parse_belief_base, parse_queries


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
        cls.excluded_systems = []  # list any inference systems that should be excluded
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

                        # For each inference system, run the inference operator and collect results.
                        for inference_system in self.inference_systems:
                            inference_operator = InferenceOperator(
                                belief_base,
                                inference_system=inference_system,
                                smt_solver=self.smt_solver,
                                pmaxsat_solver=self.pmaxsat_solver,
                                weakly=True,
                            )

                            print(
                                f"{inference_system:<20} on {belief_base_filepath}, {queries_filepath}"
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
                                self.assertEqual(
                                    system_results.iloc[0]["result"],
                                    row["result"],
                                    f"Result mismatch for belief_base: {row['belief_base']}, query: {row['query']}, "
                                    f"inference_system: {inference_system}. Expected: {row['result']}, "
                                    f"Got: {system_results.iloc[0]['result']}",
                                )
                            last_index = index


if __name__ == "__main__":
    unittest.main()
