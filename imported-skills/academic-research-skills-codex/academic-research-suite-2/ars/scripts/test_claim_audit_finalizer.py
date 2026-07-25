"""Finalizer integration tests for v3.8 claim_ref_alignment_audit_agent (T-F1a..h + T-F2..T-F5).

Per spec §7.5 in
docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md.

These tests pin the contract of `scripts/claim_audit_finalizer.py`, the
Python module that implements the §5 orchestrator §3.6 8-row matrix and
the Stage 6 reflection-report histogram. The matrix discriminates the
three `(RETRIEVAL_FAILED, not_applicable)` paths by `ref_retrieval_method`
— anchorless (not_attempted) is HIGH-WARN gate-refuse defense-in-depth,
paywall (failed) is LOW-WARN advisory pass, audit_tool_failure is
MED-WARN advisory pass. A test keyed only on (judgment, defect_stage)
would let an implementation collapse these three into one and apply the
wrong gate behavior.

In addition to T-F1..T-F5, this file pins the four Step 7 carry-over
fixes that ride the Step 8 commit cluster (per memory
`project_ars_v3_8_103_design_shipped`):

- T-CO-1: uncited sentence_text == manifest claim_text MUST suppress the
  companion INTENDED_NOT_EMITTED drift row (D-INV-4).
- T-CO-2: drifted-cited claim (EMITTED_NOT_INTENDED with `<!--ref:slug-->`)
  whose `claim_id` is not in any manifest MUST carry
  `scoped_manifest_id=SENTINEL_MANIFEST_ID` in the claim_audit_result row
  so INV-15 passes.
- T-CO-3: uncited sentence with MNC scope but no `manifest_claim_id` MUST
  emit `scoped_manifest_id=None` on its uncited_assertion entry (U-INV-4
  pair rule) while the companion constraint_violation row carries the
  manifest pointer.
- T-CO-4: under sampling, `_detect_drifts` MUST use the full
  `citations` set as the emitted side, not the sampled `audited_citations`
  subset.

Spec §7 names the file `tests/test_claim_audit_finalizer.py`. Repo
convention places tests under `scripts/test_*.py` (CI uses
`python -m unittest scripts.test_*`); the spec-named stem is preserved.

Run:
    python -m unittest scripts.test_claim_audit_finalizer -v
"""
from __future__ import annotations

import unittest
from typing import Any, Callable

try:
    from scripts.claim_audit_finalizer import (
        TIER_NONE,
        TIER_LOW_WARN,
        TIER_MED_WARN,
        TIER_HIGH_WARN,
        classify_claim_audit_result,
        classify_uncited_assertion,
        classify_constraint_violation,
        classify_claim_drift,
        classify_audit_sampling_summary,
        apply_finalizer,
        render_stage6_histogram,
        ars_mark_read_clears,
    )

    _FINALIZER_IMPORT_ERR: Exception | None = None
# Step 8 codex R2 P2-2 closure: narrow the except clause to the genuine
# RED-phase signal (`ModuleNotFoundError` on the module itself). Once
# `claim_audit_finalizer` ships, an ImportError caused by a missing
# export (e.g. a renamed function in the module) or a dependency import
# failure SHOULD surface as a test-time error rather than silently
# skipping every test in this file. The annotation-sync lint covers
# constant-name drift; this except handles only the absent-module case.
except ModuleNotFoundError as exc:  # pragma: no cover — RED phase only
    _FINALIZER_IMPORT_ERR = exc

    TIER_NONE = TIER_LOW_WARN = TIER_MED_WARN = TIER_HIGH_WARN = None  # type: ignore[assignment]

    def _stub(*args: Any, **kwargs: Any) -> Any:  # pragma: no cover
        raise _FINALIZER_IMPORT_ERR  # type: ignore[misc]

    classify_claim_audit_result = _stub  # type: ignore[assignment]
    classify_uncited_assertion = _stub  # type: ignore[assignment]
    classify_constraint_violation = _stub  # type: ignore[assignment]
    classify_claim_drift = _stub  # type: ignore[assignment]
    classify_audit_sampling_summary = _stub  # type: ignore[assignment]
    apply_finalizer = _stub  # type: ignore[assignment]
    render_stage6_histogram = _stub  # type: ignore[assignment]
    ars_mark_read_clears = _stub  # type: ignore[assignment]

try:
    from scripts.claim_audit_pipeline import run_audit_pipeline
    from scripts._claim_audit_constants import SENTINEL_MANIFEST_ID

    _PIPELINE_IMPORT_ERR: Exception | None = None
except Exception as exc:  # pragma: no cover
    _PIPELINE_IMPORT_ERR = exc
    SENTINEL_MANIFEST_ID = "M-0000-00-00T00:00:00Z-0000"

    def run_audit_pipeline(*args: Any, **kwargs: Any) -> Any:
        raise _PIPELINE_IMPORT_ERR  # type: ignore[misc]


MANIFEST_ID = "M-2026-05-15T10:00:00Z-a1b2"
AUDIT_RUN_ID = "2026-05-15T10:10:00Z-9f8e"
NOW = "2026-05-15T10:11:00Z"


def _result(
    *,
    judgment: str,
    defect_stage: str | None,
    ref_retrieval_method: str,
    audit_status: str = "completed",
    violated_constraint_id: str | None = None,
    claim_id: str = "C-001",
    scoped_manifest_id: str = MANIFEST_ID,
    rationale: str = "test rationale",
) -> dict[str, Any]:
    """Build a synthetic claim_audit_result row for matrix-row tests."""
    entry: dict[str, Any] = {
        "claim_id": claim_id,
        "scoped_manifest_id": scoped_manifest_id,
        "claim_text": "Test claim.",
        "ref_slug": "smith2024",
        "anchor_kind": "page",
        "anchor_value": "12",
        "judgment": judgment,
        "audit_status": audit_status,
        "defect_stage": defect_stage,
        "rationale": rationale,
        "judge_model": "gpt-5.5-xhigh",
        "judge_run_at": NOW,
        "ref_retrieval_method": ref_retrieval_method,
        "upstream_owner_agent": None,
        "audit_run_id": AUDIT_RUN_ID,
    }
    if violated_constraint_id is not None:
        entry["violated_constraint_id"] = violated_constraint_id
    return entry


class _FinalizerTestBase(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if _FINALIZER_IMPORT_ERR is not None:
            raise unittest.SkipTest(
                f"scripts.claim_audit_finalizer not importable yet: {_FINALIZER_IMPORT_ERR!r} "
                "(expected during RED phase — implementation lands in spec §13 step 8)"
            )


# ---------------------------------------------------------------------------
# T-F1a — SUPPORTED + null + any → no annotation, pass.
# ---------------------------------------------------------------------------


class TF1aSupported(_FinalizerTestBase):
    def test_supported_emits_no_annotation(self) -> None:
        for method in ("api", "manual_pdf"):
            with self.subTest(ref_retrieval_method=method):
                out = classify_claim_audit_result(
                    _result(judgment="SUPPORTED", defect_stage=None, ref_retrieval_method=method)
                )
                self.assertIsNone(out["annotation"])
                self.assertEqual(out["tier"], TIER_NONE)
                self.assertFalse(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1b — AMBIGUOUS + {source_description, citation_anchor, synthesis_overclaim, null}
#         + any → [CLAIM-AUDIT-AMBIGUOUS], LOW-WARN, pass.
# ---------------------------------------------------------------------------


class TF1bAmbiguous(_FinalizerTestBase):
    def test_ambiguous_emits_low_warn_advisory(self) -> None:
        for ds in ("source_description", "citation_anchor", "synthesis_overclaim", None):
            with self.subTest(defect_stage=ds):
                out = classify_claim_audit_result(
                    _result(judgment="AMBIGUOUS", defect_stage=ds, ref_retrieval_method="api")
                )
                self.assertEqual(out["annotation"], "[CLAIM-AUDIT-AMBIGUOUS]")
                self.assertEqual(out["tier"], TIER_LOW_WARN)
                self.assertFalse(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1c — UNSUPPORTED + {source_description, metadata, citation_anchor, synthesis_overclaim}
#         + any → [HIGH-WARN-CLAIM-NOT-SUPPORTED], HIGH-WARN, gate-refuse.
# ---------------------------------------------------------------------------


class TF1cUnsupportedSourceLevel(_FinalizerTestBase):
    def test_unsupported_source_level_gate_refuses(self) -> None:
        for ds in ("source_description", "metadata", "citation_anchor", "synthesis_overclaim"):
            with self.subTest(defect_stage=ds):
                out = classify_claim_audit_result(
                    _result(judgment="UNSUPPORTED", defect_stage=ds, ref_retrieval_method="api")
                )
                self.assertEqual(out["annotation"], "[HIGH-WARN-CLAIM-NOT-SUPPORTED]")
                self.assertEqual(out["tier"], TIER_HIGH_WARN)
                self.assertTrue(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1d — UNSUPPORTED + negative_constraint_violation + any
#         → [HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION (id)], HIGH-WARN, gate-refuse.
# ---------------------------------------------------------------------------


class TF1dUnsupportedConstraintViolation(_FinalizerTestBase):
    def test_unsupported_constraint_violation_gate_refuses(self) -> None:
        out = classify_claim_audit_result(
            _result(
                judgment="UNSUPPORTED",
                defect_stage="negative_constraint_violation",
                ref_retrieval_method="api",
                violated_constraint_id="MNC-1",
            )
        )
        self.assertEqual(
            out["annotation"],
            "[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION (MNC-1)]",
        )
        self.assertEqual(out["tier"], TIER_HIGH_WARN)
        self.assertTrue(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1e — RETRIEVAL_FAILED + retrieval_existence + not_found
#         → [HIGH-WARN-FABRICATED-REFERENCE], HIGH-WARN, gate-refuse.
# ---------------------------------------------------------------------------


class TF1eFabricated(_FinalizerTestBase):
    def test_fabricated_reference_gate_refuses(self) -> None:
        out = classify_claim_audit_result(
            _result(
                judgment="RETRIEVAL_FAILED",
                defect_stage="retrieval_existence",
                ref_retrieval_method="not_found",
                audit_status="completed",
            )
        )
        self.assertEqual(out["annotation"], "[HIGH-WARN-FABRICATED-REFERENCE]")
        self.assertEqual(out["tier"], TIER_HIGH_WARN)
        self.assertTrue(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1f — RETRIEVAL_FAILED + not_applicable + not_attempted
#         → [HIGH-WARN-CLAIM-AUDIT-ANCHORLESS], HIGH-WARN, gate-refuse.
# ---------------------------------------------------------------------------


class TF1fAnchorless(_FinalizerTestBase):
    def test_anchorless_defense_in_depth_gate_refuses(self) -> None:
        out = classify_claim_audit_result(
            _result(
                judgment="RETRIEVAL_FAILED",
                defect_stage="not_applicable",
                ref_retrieval_method="not_attempted",
                audit_status="inconclusive",
            )
        )
        self.assertEqual(
            out["annotation"],
            "[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS — v3.7.3 R-L3-1-A VIOLATION REACHED AUDIT]",
        )
        self.assertEqual(out["tier"], TIER_HIGH_WARN)
        self.assertTrue(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1g — RETRIEVAL_FAILED + not_applicable + failed → LOW-WARN, pass (paywall).
# ---------------------------------------------------------------------------


class TF1gPaywall(_FinalizerTestBase):
    def test_paywall_low_warn_passes(self) -> None:
        out = classify_claim_audit_result(
            _result(
                judgment="RETRIEVAL_FAILED",
                defect_stage="not_applicable",
                ref_retrieval_method="failed",
                audit_status="inconclusive",
            )
        )
        self.assertEqual(
            out["annotation"],
            "[CLAIM-AUDIT-UNVERIFIED — REFERENCE FULL-TEXT NOT RETRIEVABLE]",
        )
        self.assertEqual(out["tier"], TIER_LOW_WARN)
        self.assertFalse(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F1h — RETRIEVAL_FAILED + not_applicable + audit_tool_failure → MED-WARN, pass.
# ---------------------------------------------------------------------------


class TF1hAuditToolFailure(_FinalizerTestBase):
    def test_audit_tool_failure_med_warn_passes(self) -> None:
        out = classify_claim_audit_result(
            _result(
                judgment="RETRIEVAL_FAILED",
                defect_stage="not_applicable",
                ref_retrieval_method="audit_tool_failure",
                audit_status="inconclusive",
                rationale="judge_timeout: judge model failed to respond within 60s",
            )
        )
        self.assertEqual(
            out["annotation"],
            "[CLAIM-AUDIT-TOOL-FAILURE — judge_timeout]",
        )
        self.assertEqual(out["tier"], TIER_MED_WARN)
        self.assertFalse(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-F2 — HIGH-WARN-CLAIM-NOT-SUPPORTED triggers terminal gate refuse.
# ---------------------------------------------------------------------------


class TF2TerminalGateRefuse(_FinalizerTestBase):
    def test_high_warn_propagates_to_apply_finalizer(self) -> None:
        passport = {
            "claim_audit_results": [
                _result(
                    judgment="UNSUPPORTED",
                    defect_stage="source_description",
                    ref_retrieval_method="api",
                ),
                _result(
                    judgment="SUPPORTED",
                    defect_stage=None,
                    ref_retrieval_method="api",
                    claim_id="C-002",
                ),
            ],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
        }
        out = apply_finalizer(passport)
        self.assertTrue(
            out["gate_refuse"],
            "any HIGH-WARN row must flip passport-level gate_refuse",
        )
        self.assertIn("[HIGH-WARN-CLAIM-NOT-SUPPORTED]", out["gate_refuse_reasons"])


# ---------------------------------------------------------------------------
# T-F3 — /ars-mark-read does NOT clear HIGH-WARN-CLAIM-NOT-SUPPORTED (asymmetry).
# ---------------------------------------------------------------------------


class TF3MarkReadAsymmetry(_FinalizerTestBase):
    def test_mark_read_cannot_clear_high_warn_not_supported(self) -> None:
        # HIGH-WARN-CLAIM-NOT-SUPPORTED is a structural verdict, not an
        # acknowledgement-eligible trust state. Mirrors v3.7.3 R-L3-1-A.
        self.assertFalse(
            ars_mark_read_clears(
                annotation="[HIGH-WARN-CLAIM-NOT-SUPPORTED]",
                tier=TIER_HIGH_WARN,
            )
        )
        self.assertFalse(
            ars_mark_read_clears(
                annotation="[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION (MNC-1)]",
                tier=TIER_HIGH_WARN,
            )
        )

    def test_mark_read_clears_low_warn_advisory(self) -> None:
        # LOW-WARN paywall is acknowledgement-eligible (the user has
        # accepted the unverifiable state and chosen to ship).
        self.assertTrue(
            ars_mark_read_clears(
                annotation="[CLAIM-AUDIT-UNVERIFIED — REFERENCE FULL-TEXT NOT RETRIEVABLE]",
                tier=TIER_LOW_WARN,
            )
        )


# ---------------------------------------------------------------------------
# T-F4 — LOW-WARN-CLAIM-AUDIT-UNVERIFIED passes gate.
# ---------------------------------------------------------------------------


class TF4LowWarnPasses(_FinalizerTestBase):
    def test_low_warn_only_passport_passes_gate(self) -> None:
        passport = {
            "claim_audit_results": [
                _result(
                    judgment="RETRIEVAL_FAILED",
                    defect_stage="not_applicable",
                    ref_retrieval_method="failed",
                    audit_status="inconclusive",
                ),
            ],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
        }
        out = apply_finalizer(passport)
        self.assertFalse(
            out["gate_refuse"],
            "paywall LOW-WARN-only passport must pass the gate",
        )
        self.assertEqual(out["gate_refuse_reasons"], [])


# ---------------------------------------------------------------------------
# T-F5 — Stage 6 reflection report renders histogram when ≥5 completed entries.
# ---------------------------------------------------------------------------


class TF5Stage6Histogram(_FinalizerTestBase):
    def test_histogram_renders_when_five_or_more_completed(self) -> None:
        results = [
            _result(
                judgment="UNSUPPORTED",
                defect_stage="source_description",
                ref_retrieval_method="api",
                claim_id=f"C-{i:03d}",
            )
            for i in range(3)
        ]
        results += [
            _result(
                judgment="UNSUPPORTED",
                defect_stage="citation_anchor",
                ref_retrieval_method="api",
                claim_id=f"C-{i+3:03d}",
            )
            for i in range(2)
        ]
        report = render_stage6_histogram(results)
        self.assertIsNotNone(report, "≥5 completed entries MUST render histogram")
        self.assertIn("source_description", report)
        self.assertIn("citation_anchor", report)
        self.assertIn("3", report, "source_description count = 3")
        self.assertIn("2", report, "citation_anchor count = 2")

    def test_histogram_suppressed_below_threshold(self) -> None:
        results = [
            _result(
                judgment="UNSUPPORTED",
                defect_stage="source_description",
                ref_retrieval_method="api",
                claim_id=f"C-{i:03d}",
            )
            for i in range(4)
        ]
        report = render_stage6_histogram(results)
        self.assertIsNone(report, "<5 completed entries MUST suppress histogram")

    def test_histogram_renders_for_all_supported_papers(self) -> None:
        # Step 8 codex R4 P2-1 closure: spec literal is "≥5 completed
        # entries". A mostly-SUPPORTED paper (5 completed citations,
        # zero defect_stages) MUST still emit the histogram block so the
        # Stage 6 appendix stays consistent. Prior implementation filtered
        # to completed-with-defect rows, suppressing this common case.
        results = [
            _result(
                judgment="SUPPORTED",
                defect_stage=None,
                ref_retrieval_method="api",
                claim_id=f"C-{i:03d}",
            )
            for i in range(5)
        ]
        report = render_stage6_histogram(results)
        self.assertIsNotNone(
            report,
            "5 SUPPORTED completed entries MUST emit histogram per spec "
            "literal '≥5 completed entries'",
        )
        self.assertIn("n=5", report)
        self.assertIn("No defect stages recorded", report)

    def test_histogram_excludes_inconclusive_rows(self) -> None:
        # 5 inconclusive + 0 completed → still suppressed (spec: "≥5 completed").
        results = [
            _result(
                judgment="RETRIEVAL_FAILED",
                defect_stage="not_applicable",
                ref_retrieval_method="failed",
                audit_status="inconclusive",
                claim_id=f"C-{i:03d}",
            )
            for i in range(5)
        ]
        report = render_stage6_histogram(results)
        self.assertIsNone(
            report,
            "histogram threshold counts completed rows only, not inconclusive",
        )


# ---------------------------------------------------------------------------
# T-F6 — MANIFEST-MISSING fallback emits a paper-level advisory annotation.
# ---------------------------------------------------------------------------


class TF6ManifestMissingAdvisory(_FinalizerTestBase):
    """T-F6 (Step 8 codex R1 P2 closure): apply_finalizer surfaces the
    MANIFEST-MISSING advisory when claim_intent_manifests is empty AND any
    claim_audit_result row carries the sentinel scoped_manifest_id.

    Spec §9 acceptance bullet: `claim_intent_manifest absent →
    MANIFEST-MISSING advisory + fallback flow exercised in test`. Step 7
    T-M2 pinned the pipeline-side invariants (sentinel propagation, all
    six defect_stage paths still emit); the advisory surface itself lives
    in the finalizer per spec §13 step 8 deliverable. Before this row, an
    all-SUPPORTED MANIFEST-MISSING passport produced zero annotations —
    the user lost the required warning that the audit ran without
    pre-commitment baseline.
    """

    def test_empty_manifests_with_sentinel_rows_emits_advisory(self) -> None:
        passport = {
            "claim_intent_manifests": [],
            "claim_audit_results": [
                _result(
                    judgment="SUPPORTED",
                    defect_stage=None,
                    ref_retrieval_method="api",
                    scoped_manifest_id=SENTINEL_MANIFEST_ID,
                )
            ],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
        }
        out = apply_finalizer(passport)
        manifest_missing_advisories = [
            a for a in out["annotations"] if "MANIFEST-MISSING" in a["annotation"]
        ]
        self.assertEqual(
            len(manifest_missing_advisories),
            1,
            "MANIFEST-MISSING fallback MUST emit exactly one paper-level advisory "
            "when no manifests are present and at least one audit row carries the "
            "sentinel scope (spec §9 acceptance criterion)",
        )
        advisory = manifest_missing_advisories[0]
        self.assertEqual(advisory["tier"], TIER_LOW_WARN)
        self.assertFalse(
            out["gate_refuse"],
            "MANIFEST-MISSING is advisory only — never gate-refuses",
        )

    def test_present_manifests_suppress_advisory(self) -> None:
        # When manifests are present, the audit ran with a pre-commitment
        # baseline — no MANIFEST-MISSING advisory should fire even if
        # individual rows happen to carry sentinel scope (drifted-cited
        # claims that the CO-2 fix sentinel-normalizes per row).
        passport = {
            "claim_intent_manifests": [
                {
                    "manifest_version": "1.0",
                    "manifest_id": "M-2026-05-15T10:00:00Z-a1b2",
                    "emitted_by": "synthesis_agent",
                    "emitted_at": "2026-05-15T09:55:00Z",
                    "claims": [],
                    "manifest_negative_constraints": [],
                }
            ],
            "claim_audit_results": [
                _result(
                    judgment="SUPPORTED",
                    defect_stage=None,
                    ref_retrieval_method="api",
                    scoped_manifest_id=SENTINEL_MANIFEST_ID,
                )
            ],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
        }
        out = apply_finalizer(passport)
        manifest_missing_advisories = [
            a for a in out["annotations"] if "MANIFEST-MISSING" in a["annotation"]
        ]
        self.assertEqual(
            manifest_missing_advisories,
            [],
            "MANIFEST-MISSING advisory MUST NOT fire when manifests are present "
            "(even with individual sentinel rows from CO-2 normalization)",
        )

    def test_empty_manifests_no_results_no_advisory(self) -> None:
        # MANIFEST-MISSING fires on the (empty manifests + sentinel rows
        # exist) pair. If there are no audit rows at all, there's nothing
        # to surface a warning about — the gate just sees an empty
        # passport.
        passport = {
            "claim_intent_manifests": [],
            "claim_audit_results": [],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
        }
        out = apply_finalizer(passport)
        self.assertEqual(out["annotations"], [])
        self.assertFalse(out["gate_refuse"])


# ---------------------------------------------------------------------------
# T-CO-1 — uncited sentence_text == manifest claim_text suppresses INTENDED_NOT_EMITTED.
# ---------------------------------------------------------------------------


class _PipelineCarryoverTestBase(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        if _PIPELINE_IMPORT_ERR is not None:
            raise unittest.SkipTest(
                f"scripts.claim_audit_pipeline not importable yet: {_PIPELINE_IMPORT_ERR!r}"
            )

    def _config(self, **overrides: Any) -> dict[str, Any]:
        base = {"max_claims_per_paper": 100, "judge_model": "gpt-5.5-xhigh"}
        base.update(overrides)
        return base


class TCO1UncitedSuppressesIntendedDrift(_PipelineCarryoverTestBase):
    def test_uncited_text_matches_manifest_claim_no_companion_drift(self) -> None:
        text = "Sample preprints accounted for 67% of corpus."
        manifest = {
            "manifest_version": "1.0",
            "manifest_id": MANIFEST_ID,
            "emitted_by": "synthesis_agent",
            "emitted_at": "2026-05-15T09:55:00Z",
            "claims": [
                {
                    "claim_id": "C-001",
                    "claim_text": text,
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            "manifest_negative_constraints": [],
        }
        uncited = [
            {
                "sentence_text": text,
                "section_path": "3. Results",
                "trigger_tokens": ["67%"],
                "manifest_claim_id": "C-001",
                "scoped_manifest_id": MANIFEST_ID,
            }
        ]
        out = run_audit_pipeline(
            citations=[],
            manifests=[manifest],
            corpus=[],
            config=self._config(),
            retrieve_fn=lambda c: {},  # never called — no citations
            judge_fn=lambda **k: {"judgment": "SUPPORTED", "rationale": "x"},
            audit_run_id=AUDIT_RUN_ID,
            now_iso=NOW,
            uncited_sentences=uncited,
        )
        self.assertEqual(len(out["uncited_assertions"]), 1, "uncited entry MUST emit")
        companion = [
            d
            for d in out["claim_drifts"]
            if d["drift_kind"] == "INTENDED_NOT_EMITTED" and d["claim_text"] == text
        ]
        self.assertEqual(
            companion,
            [],
            "INTENDED_NOT_EMITTED drift MUST be suppressed when uncited sentence shares the text "
            "(D-INV-4 cross-aggregate exclusivity, Step 7 codex R1 carry-over CO-1)",
        )


# ---------------------------------------------------------------------------
# T-CO-2 — drifted cited claim emits with scoped_manifest_id=SENTINEL.
# ---------------------------------------------------------------------------


class TCO2DriftedCitedScopedToSentinel(_PipelineCarryoverTestBase):
    def test_drifted_cited_claim_uses_sentinel_scope(self) -> None:
        manifest = {
            "manifest_version": "1.0",
            "manifest_id": MANIFEST_ID,
            "emitted_by": "synthesis_agent",
            "emitted_at": "2026-05-15T09:55:00Z",
            "claims": [
                {
                    "claim_id": "C-001",
                    "claim_text": "Original manifest claim text.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                }
            ],
            "manifest_negative_constraints": [],
        }
        # Drifted cited claim — has a ref marker but claim_id (C-100) is
        # NOT in manifest. The pipeline currently writes scoped_manifest_id
        # = MANIFEST_ID to the row; INV-15 then rejects the resulting
        # passport because (MANIFEST_ID, C-100) is not in the manifest index.
        drifted_citation = {
            "claim_id": "C-100",
            "scoped_manifest_id": MANIFEST_ID,
            "claim_text": "Drifted prose introduced a new claim.",
            "ref_slug": "smith2024",
            "anchor_kind": "page",
            "anchor_value": "14",
            "section_path": "3. Results",
        }
        out = run_audit_pipeline(
            citations=[drifted_citation],
            manifests=[manifest],
            corpus=[],
            config=self._config(),
            retrieve_fn=lambda c: {"ref_retrieval_method": "api", "retrieved_excerpt": "ok"},
            judge_fn=lambda **k: {"judgment": "SUPPORTED", "rationale": "supported"},
            audit_run_id=AUDIT_RUN_ID,
            now_iso=NOW,
        )
        self.assertEqual(len(out["claim_audit_results"]), 1)
        entry = out["claim_audit_results"][0]
        self.assertEqual(
            entry["scoped_manifest_id"],
            SENTINEL_MANIFEST_ID,
            "drifted cited claim (claim_id not in manifest) MUST carry sentinel scope "
            "so INV-15 dangling check passes (Step 7 codex R1 carry-over CO-2)",
        )


# ---------------------------------------------------------------------------
# T-CO-3 — MNC-only uncited sentence emits scoped_manifest_id=None on uncited row.
# ---------------------------------------------------------------------------


class TCO3MncOnlyUncitedScope(_PipelineCarryoverTestBase):
    def test_mnc_only_uncited_drops_manifest_scope(self) -> None:
        manifest = {
            "manifest_version": "1.0",
            "manifest_id": MANIFEST_ID,
            "emitted_by": "synthesis_agent",
            "emitted_at": "2026-05-15T09:55:00Z",
            "claims": [],  # no claim-level entries
            "manifest_negative_constraints": [
                {"constraint_id": "MNC-1", "rule": "No unqualified causal language."}
            ],
        }
        uncited = [
            {
                "sentence_text": "Treatment caused outcome.",
                "section_path": "3. Results",
                "trigger_tokens": ["caused"],
                "manifest_claim_id": None,
                "scoped_manifest_id": MANIFEST_ID,
            }
        ]
        out = run_audit_pipeline(
            citations=[],
            manifests=[manifest],
            corpus=[],
            config=self._config(),
            retrieve_fn=lambda c: {},
            judge_fn=lambda **k: {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": "constraint violated",
            },
            audit_run_id=AUDIT_RUN_ID,
            now_iso=NOW,
            uncited_sentences=uncited,
        )
        self.assertEqual(len(out["uncited_assertions"]), 1)
        ua = out["uncited_assertions"][0]
        self.assertIsNone(
            ua["scoped_manifest_id"],
            "uncited_assertion MUST drop manifest scope when manifest_claim_id is None "
            "(U-INV-4 pair rule, Step 7 codex R1 carry-over CO-3)",
        )
        self.assertIsNone(ua["manifest_claim_id"])

        # Companion constraint_violation row still carries the manifest pointer.
        self.assertEqual(len(out["constraint_violations"]), 1)
        cv = out["constraint_violations"][0]
        self.assertEqual(cv["scoped_manifest_id"], MANIFEST_ID)
        self.assertEqual(cv["violated_constraint_id"], "MNC-1")


# ---------------------------------------------------------------------------
# T-CO-4 — sampling does not truncate the emitted set used for drift detection.
# ---------------------------------------------------------------------------


class TCO4SamplingPreservesEmittedSet(_PipelineCarryoverTestBase):
    def test_unsampled_citations_not_flagged_as_dropped_from_manifest(self) -> None:
        N = 30
        CAP = 10
        claims = [
            {
                "claim_id": f"C-{i:03d}",
                "claim_text": f"Manifest claim {i}.",
                "intended_evidence_kind": "empirical",
                "planned_refs": [f"ref{i}"],
            }
            for i in range(N)
        ]
        manifest = {
            "manifest_version": "1.0",
            "manifest_id": MANIFEST_ID,
            "emitted_by": "synthesis_agent",
            "emitted_at": "2026-05-15T09:55:00Z",
            "claims": claims,
            "manifest_negative_constraints": [],
        }
        citations = [
            {
                "claim_id": f"C-{i:03d}",
                "scoped_manifest_id": MANIFEST_ID,
                "claim_text": f"Manifest claim {i}.",
                "ref_slug": f"ref{i}",
                "anchor_kind": "page",
                "anchor_value": str(i),
                "section_path": "s",
            }
            for i in range(N)
        ]
        out = run_audit_pipeline(
            citations=citations,
            manifests=[manifest],
            corpus=[],
            config=self._config(max_claims_per_paper=CAP),
            retrieve_fn=lambda c: {
                "ref_retrieval_method": "api",
                "retrieved_excerpt": "ok",
            },
            judge_fn=lambda **k: {"judgment": "SUPPORTED", "rationale": "ok"},
            audit_run_id=AUDIT_RUN_ID,
            now_iso=NOW,
        )
        intended_not_emitted = [
            d for d in out["claim_drifts"] if d["drift_kind"] == "INTENDED_NOT_EMITTED"
        ]
        self.assertEqual(
            intended_not_emitted,
            [],
            "drift detection MUST see the full emitted set, not the sampled subset "
            f"(Step 7 codex R1 carry-over CO-4); got {len(intended_not_emitted)} false "
            f"INTENDED_NOT_EMITTED rows for N={N} cap={CAP}",
        )
        # Sampling MUST still produce a summary row.
        self.assertEqual(len(out["audit_sampling_summaries"]), 1)
        self.assertEqual(out["audit_sampling_summaries"][0]["audited_count"], CAP)


# ---------------------------------------------------------------------------
# T-UAF-F1 — v3.8.2 / #118 finalizer wiring for uncited_audit_failures[].
# Codex cross-model review (2026-05-17) flagged that the UAF aggregate was
# emitted by the pipeline but never surfaced by apply_finalizer, so the
# operational signal stayed silent in the final output. This test pins the
# routing entry + classifier + annotation so a future refactor cannot
# accidentally drop the UAF row from the finalizer dispatch table.
# ---------------------------------------------------------------------------


class TUAFFinalizerRouting(unittest.TestCase):
    def test_uaf_row_emits_med_warn_annotation(self) -> None:
        passport = {
            "claim_audit_results": [],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
            "uncited_audit_failures": [
                {
                    "finding_id": "UAF-001",
                    "claim_text": "Uncited sentence under MNC scope.",
                    "section_path": "3. Results > 3.1",
                    "scoped_manifest_id": "M-2026-05-15T10:00:00Z-a1b2",
                    "manifest_claim_id": None,
                    "fault_class": "judge_timeout",
                    "rationale": "judge_timeout: judge timed out after 30s",
                    "judge_model": "gpt-5.5-xhigh",
                    "judge_run_at": "2026-05-15T10:14:00Z",
                    "rule_version": "D4-c-v1-uaf-v1",
                }
            ],
        }
        out = apply_finalizer(passport)
        annotations = [a["annotation"] for a in out["annotations"]]
        self.assertIn(
            "[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — judge_timeout]",
            annotations,
            "UAF row must produce a MED-WARN annotation via apply_finalizer; "
            "without the routing entry the operational signal stays silent.",
        )
        self.assertFalse(
            out["gate_refuse"],
            "UAF is MED-WARN advisory; gate must NOT refuse on it.",
        )

    def test_uaf_row_each_fault_class_renders(self) -> None:
        """Every INV14 fault-class value must render through the annotation template."""
        from scripts._claim_audit_constants import INV14_FAULT_CLASS_TAGS

        for fault_class in INV14_FAULT_CLASS_TAGS:
            with self.subTest(fault_class=fault_class):
                passport = {
                    "claim_audit_results": [],
                    "uncited_assertions": [],
                    "claim_drifts": [],
                    "constraint_violations": [],
                    "audit_sampling_summaries": [],
                    "uncited_audit_failures": [
                        {
                            "finding_id": "UAF-001",
                            "claim_text": "Uncited sentence.",
                            "section_path": "3. Results",
                            "scoped_manifest_id": "M-2026-05-15T10:00:00Z-a1b2",
                            "manifest_claim_id": None,
                            "fault_class": fault_class,
                            "rationale": f"{fault_class}: synthetic",
                            "judge_model": "gpt-5.5-xhigh",
                            "judge_run_at": "2026-05-15T10:14:00Z",
                            "rule_version": "D4-c-v1-uaf-v1",
                        }
                    ],
                }
                out = apply_finalizer(passport)
                expected = f"[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — {fault_class}]"
                annotations = [a["annotation"] for a in out["annotations"]]
                self.assertIn(expected, annotations)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
