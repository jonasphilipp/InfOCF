"""End-to-end tests for the ``/api/pareto_minimal_c_representations/``
endpoints on weakly consistent belief bases.

Covers the wiring added in Phase 3:

- The compute endpoint (``/api/pareto_minimal_c_representations/``)
  and the prepare endpoint (``/api/pareto_minimal_c_representations/prepare/``)
  both accept weakly consistent belief bases — the Phase 2 extended
  c-representation pipeline (KER 2024 / NMR 2023) replaces the former
  ``error 332`` refusal.
- The JSON response encodes ``math.inf`` impact and rank values as the
  string ``"infinity"`` so the payload is standards-compliant JSON.
- The CSV download endpoints stream ``"infinity"`` for infinite
  impacts and ranks, not the Python ``inf`` literal.
- ``consistency`` / ``j_delta`` / ``infinity_indices`` /
  ``infinity_reasons`` metadata is surfaced in both the inline
  response and the cached ``metadata`` block of the prepared result.

Run:
    cd infocfweb2.0
    ../venv/bin/python -m unittest \\
        InfOCF.unittests.test_pareto_endpoint_weakly
"""

from __future__ import annotations

import os
import sys
import unittest

# Keep this file importable both as ``unittests.test_pareto_endpoint_weakly``
# (when run from inside ``InfOCF``) and as ``InfOCF.unittests.
# test_pareto_endpoint_weakly`` (when run from ``infocfweb2.0``).  The
# Flask app lives in ``infocfweb2.0/app.py``, one directory up from
# the ``InfOCF/`` checkout.
BASE_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WEBAPP_DIR = os.path.dirname(BASE_DIR)
for path in (BASE_DIR, WEBAPP_DIR):
    if path not in sys.path:
        sys.path.insert(0, path)

try:
    from app import app  # noqa: E402
except ModuleNotFoundError as exc:
    if exc.name != "app":
        raise
    raise unittest.SkipTest(
        "webapp endpoint tests require infocfweb2.0/app.py next to the InfOCF checkout"
    ) from exc

PENGUINS_WEAKLY_CKB = """signature
    b, f, p, w
conditionals
birds_weakly{
    (f | b),
    (!f | p),
    (Bottom | p, !b),
    (w | b)
}"""

STRONGLY_CONSISTENT_CKB = """signature
    b, f, p
conditionals
pf{
    (f | b),
    (!f | p),
    (b | p)
}"""


class ParetoWeaklyEndpointTest(unittest.TestCase):
    def setUp(self) -> None:
        self.client = app.test_client()

    # ------------------------------------------------------------------
    # compute endpoint: /api/pareto_minimal_c_representations/
    # ------------------------------------------------------------------

    def test_compute_endpoint_accepts_weakly_consistent(self) -> None:
        resp = self.client.post(
            "/api/pareto_minimal_c_representations/",
            json={"belief_base": PENGUINS_WEAKLY_CKB, "backend": "c_revision"},
        )
        self.assertEqual(resp.status_code, 200)
        payload = resp.get_json()
        self.assertEqual(payload["consistency"], "weakly_consistent")
        # The Phase 1/2 pipeline must not produce any error codes —
        # in particular no 332 refusal any more.
        self.assertEqual(
            payload["errors"],
            [],
            f"expected empty errors, got {payload['errors']!r}",
        )
        pareto = payload["pareto_minimal_c_representations"]
        self.assertIsNotNone(pareto)
        self.assertEqual(pareto["solution_count"], 1)
        self.assertEqual(pareto["infinity_indices"], [3])
        self.assertEqual(pareto["infinity_reasons"], {"3": "strict"})

    def test_compute_endpoint_emits_infinity_as_string(self) -> None:
        resp = self.client.post(
            "/api/pareto_minimal_c_representations/",
            json={"belief_base": PENGUINS_WEAKLY_CKB, "backend": "c_revision"},
        )
        pareto = resp.get_json()["pareto_minimal_c_representations"]
        (solution,) = pareto["solutions"]
        # impact_vector: exactly one "infinity" at the strict index
        # (idx 3, i.e. zero-based position 2), all others finite ints.
        vec = solution["impact_vector"]
        self.assertEqual(vec[2], "infinity")
        self.assertTrue(all(isinstance(v, int) for i, v in enumerate(vec) if i != 2))
        # Per-impact entries carry infinity_reason metadata.
        for impact in solution["impacts"]:
            if impact["index"] == 3:
                self.assertEqual(impact["value"], "infinity")
                self.assertEqual(impact["infinity_reason"], "strict")
            else:
                self.assertIsInstance(impact["value"], int)
                self.assertIsNone(impact["infinity_reason"])

    def test_compute_endpoint_induced_ocf_marks_infeasible_worlds(self) -> None:
        resp = self.client.post(
            "/api/pareto_minimal_c_representations/",
            json={"belief_base": PENGUINS_WEAKLY_CKB, "backend": "c_revision"},
        )
        pareto = resp.get_json()["pareto_minimal_c_representations"]
        (solution,) = pareto["solutions"]
        ocf = solution["ocf"]
        self.assertEqual(ocf["signature"], ["b", "f", "p", "w"])
        # Signature order b,f,p,w → world bit i corresponds to variable
        # ocf.signature[i]; the strict rule (⊥ | p ∧ ¬b) is falsified
        # iff p=1 and b=0 → 4 out of 16 worlds infeasible.
        infeasible = [w for w in ocf["worlds"] if w["rank"] == "infinity"]
        finite = [w for w in ocf["worlds"] if w["rank"] != "infinity"]
        self.assertEqual(len(infeasible), 4)
        self.assertEqual(len(finite), 12)
        for w in infeasible:
            assignment = dict(zip(ocf["signature"], w["assignment"], strict=False))
            self.assertEqual(assignment["p"], 1)
            self.assertEqual(assignment["b"], 0)
        for w in finite:
            self.assertIsInstance(w["rank"], int)
            self.assertGreaterEqual(w["rank"], 0)

    def test_compute_endpoint_strongly_consistent_regression(self) -> None:
        resp = self.client.post(
            "/api/pareto_minimal_c_representations/",
            json={"belief_base": STRONGLY_CONSISTENT_CKB, "backend": "c_revision"},
        )
        self.assertEqual(resp.status_code, 200)
        payload = resp.get_json()
        self.assertEqual(payload["consistency"], "consistent")
        pareto = payload["pareto_minimal_c_representations"]
        self.assertEqual(pareto["infinity_indices"], [])
        self.assertEqual(pareto["infinity_reasons"], {})
        (solution,) = pareto["solutions"]
        self.assertTrue(all(isinstance(v, int) for v in solution["impact_vector"]))

    # ------------------------------------------------------------------
    # prepare endpoint: /api/pareto_minimal_c_representations/prepare/
    # ------------------------------------------------------------------

    def test_prepare_endpoint_surfaces_partition_metadata(self) -> None:
        resp = self.client.post(
            "/api/pareto_minimal_c_representations/prepare/",
            json={"belief_base": PENGUINS_WEAKLY_CKB, "backend": "c_revision"},
        )
        self.assertEqual(resp.status_code, 200)
        payload = resp.get_json()
        self.assertEqual(payload["consistency"], "weakly_consistent")
        self.assertEqual(payload["errors"], [])
        result = payload["result"]
        self.assertEqual(result["status"], "ready")
        metadata = result["metadata"]
        self.assertEqual(metadata["consistency"], "weakly_consistent")
        self.assertEqual(metadata["infinity_indices"], [3])
        self.assertEqual(metadata["infinity_reasons"], {"3": "strict"})
        self.assertEqual(metadata["j_delta"], [1, 2, 4])
        self.assertIsNotNone(result.get("download_token"))

    def test_prepare_download_csv_renders_infinity_token(self) -> None:
        prepare_resp = self.client.post(
            "/api/pareto_minimal_c_representations/prepare/",
            json={"belief_base": PENGUINS_WEAKLY_CKB, "backend": "c_revision"},
        )
        token = prepare_resp.get_json()["result"]["download_token"]

        # Impact-vectors CSV: the strict conditional's row has value "infinity".
        vectors_resp = self.client.post(
            "/api/pareto_minimal_c_representations/download_vectors_csv/",
            json={"download_token": token},
        )
        self.assertEqual(vectors_resp.status_code, 200)
        text = vectors_resp.data.decode()
        self.assertIn("infinity", text)
        self.assertIn("eta_3", text)
        strict_rows = [
            line for line in text.splitlines() if line.startswith("1,eta_3,")
        ]
        self.assertEqual(len(strict_rows), 1)
        self.assertTrue(strict_rows[0].endswith(",infinity"))
        # The finite conditionals must NOT render as "infinity".
        for eta_label in ("eta_1", "eta_2", "eta_4"):
            for line in text.splitlines():
                if line.startswith(f"1,{eta_label},"):
                    self.assertFalse(
                        line.endswith(",infinity"),
                        f"{eta_label} should be finite, got: {line!r}",
                    )

        # Induced-OCF CSV: infeasible worlds have rank "infinity".
        ocf_resp = self.client.post(
            "/api/pareto_minimal_c_representations/download_ocf_csv/",
            json={"download_token": token},
        )
        self.assertEqual(ocf_resp.status_code, 200)
        ocf_text = ocf_resp.data.decode()
        rank_inf_rows = [
            line for line in ocf_text.splitlines() if line.endswith(",infinity")
        ]
        self.assertEqual(
            len(rank_inf_rows),
            4,
            "expected exactly 4 infeasible worlds in the penguins-weakly OCF CSV",
        )

    def test_prepare_download_ignores_weakly_consistency_at_boundary(self) -> None:
        """Verify no stray ``Infinity`` literal escapes into JSON even
        when the response is re-decoded by a strict parser."""
        import json as json_mod

        resp = self.client.post(
            "/api/pareto_minimal_c_representations/prepare/",
            json={"belief_base": PENGUINS_WEAKLY_CKB, "backend": "c_revision"},
        )
        # Re-parse with strict JSON (allow_nan=False) — would raise if
        # the payload contained a bare ``Infinity`` / ``NaN``.
        text = resp.data.decode()
        json_mod.loads(text, parse_constant=_reject_non_standard)


def _reject_non_standard(token):  # pragma: no cover - defensive only
    raise ValueError(
        f"non-standard JSON constant {token!r} in response; "
        "the encoder should have replaced math.inf with 'infinity'"
    )


if __name__ == "__main__":
    unittest.main()
