"""End-to-end claim-faithfulness audit test (spec §7.6 + §13 step 9).

Wires `detect_uncited_assertions` → `run_audit_pipeline` → `apply_finalizer`
against a synthetic 5-citation paper per the spec §7.6 contract:

| Cit | Type                                    | Pipeline outcome                                  | Finalizer       |
| --- | --------------------------------------- | ------------------------------------------------- | --------------- |
| c1  | real, SUPPORTED                         | judgment=SUPPORTED                                | no annotation   |
| c2  | real, AMBIGUOUS                         | judgment=AMBIGUOUS                                | LOW-WARN        |
| c3  | real but misused (source says inverse)  | judgment=UNSUPPORTED, defect=source_description   | HIGH-WARN refuse |
| c4  | paywall (retrieval fails)               | judgment=RETRIEVAL_FAILED, method=failed          | LOW-WARN pass   |
| c5  | violates declared negative constraint   | judge VIOLATED → row judgment=UNSUPPORTED, defect=negative_constraint_violation | HIGH-WARN refuse |

Acceptance:
  - Scenario A (all 5 untouched): gate refuses; reasons are exactly
    `[HIGH-WARN-CLAIM-NOT-SUPPORTED]` (c3) and
    `[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION (MNC-1)]` (c5); c1/c2/c4 do not
    contribute to gate_refuse_reasons.
  - Scenario B (c3 corrected to SUPPORTED + c5 rewritten with hedged
    language so the judge returns SUPPORTED instead of VIOLATED): gate
    passes with no HIGH-WARN reasons. c2/c4 advisory annotations may
    remain. The fixture keeps c5 as a cited claim — Scenario B
    exercises the in-place-rewrite remediation path, not the
    drop-from-prose path (which would invoke the manifest drift surface
    pinned by scripts/test_claim_audit_pipeline.py T-P10).

DEFERRED-CROSS-SENTENCE closure: this test also wires
`detect_uncited_assertions` with the new `adjacent_text` field — a sentence
whose `adjacent_text` carries a `<!--ref:...-->` marker is filtered out
before reaching the pipeline. The agent prompt's DEFERRED-CROSS-SENTENCE
Step-9 acceptance note in
`academic-pipeline/agents/claim_ref_alignment_audit_agent.md` is cleared by
the regression test below.

Spec: docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md §7.6 + §13 step 9.
Repo convention places tests under `scripts/test_*.py` (CI runs
`python -m unittest scripts.test_*`); the spec name `tests/test_e2e_claim_audit.py`
maps to this file unchanged.

Run:
    python -m unittest scripts.test_e2e_claim_audit -v
"""
from __future__ import annotations

import unittest
from typing import Any, Callable

# Step 9 RED → GREEN transition is complete: all three modules below now
# exist. Per R3 codex P2 closure, removing the prior try/except-skip wrapper
# means an import-time failure (transitive dependency, renamed symbol,
# module-level statement raising) surfaces as a real test failure instead
# of a silently green "skip". The earlier scripts/test_claim_audit_*.py
# files keep their RED-phase skip because some of them shipped before the
# pipeline module existed; this e2e file landed in the same commit that
# completed the chain, so the skip wrapper was always transitional.
from scripts.claim_audit_pipeline import run_audit_pipeline
from scripts.claim_audit_finalizer import (
    ANNOTATION_CLAIM_AUDIT_AMBIGUOUS,
    ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED,
    ANNOTATION_LOW_WARN_UNVERIFIED,
    ANNOTATION_UNCITED_ASSERTION,
    apply_finalizer,
)
from scripts.uncited_assertion_detector import detect_uncited_assertions


MANIFEST_ID = "M-2026-05-16T09:00:00Z-e2e1"
AUDIT_RUN_ID = "2026-05-16T09:10:00Z-e2e1"
NOW = "2026-05-16T09:11:00Z"

# Pre-formatted constraint-violation annotation; the format-string template
# lives in claim_audit_finalizer.ANNOTATION_HIGH_WARN_NEGATIVE_CONSTRAINT_VIOLATION.
ANNOTATION_C5_GATE = "[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION (MNC-1)]"


# ---------------------------------------------------------------------------
# Synthetic 5-citation paper fixture (inline; matches scripts/test_claim_audit_*
# unit-test idiom rather than introducing an out-of-band fixture dir).
# ---------------------------------------------------------------------------

# Citation claim texts are chosen so the judge stub can dispatch by
# claim_text prefix without inspecting the full body. Anchors are populated
# so INV-6 never fires — anchor=none short-circuit is exercised in T-P1, not here.
_C1_TEXT = "C1: Sample preprints accounted for 67% of corpus."
_C2_TEXT = "C2: Adoption ratios trended upward across the 2022 cohort."
_C3_TEXT = "C3: Intervention X reduced error rates by 40%."
_C4_TEXT = "C4: Latency improved on the deployed nodes."
_C5_TEXT = "C5: Treatment caused recovery within two weeks."

# Fixture-drift guard (/simplify quality advisory Q-P2-2). The judge stub
# dispatches by `claim_text.startswith("Cn:")`; a rename of any _Cn_TEXT
# constant that drops the leading `Cn:` would silently fall through to the
# `raise AssertionError` branch in production fixtures (not just CI). Assert
# at import time so the violation surfaces immediately.
_CLAIM_PREFIXES = (
    ("C1:", _C1_TEXT),
    ("C2:", _C2_TEXT),
    ("C3:", _C3_TEXT),
    ("C4:", _C4_TEXT),
    ("C5:", _C5_TEXT),
)
for _prefix, _text in _CLAIM_PREFIXES:
    assert _text.startswith(_prefix), (
        f"fixture drift: {_text!r} must start with {_prefix!r} so judge_fn "
        "dispatch stays consistent with the 5-citation contract"
    )


def _citation(claim_id: str, claim_text: str, ref_slug: str) -> dict[str, Any]:
    return {
        "claim_id": claim_id,
        "scoped_manifest_id": MANIFEST_ID,
        "claim_text": claim_text,
        "ref_slug": ref_slug,
        "anchor_kind": "page",
        "anchor_value": "12",
        "section_path": "3. Results",
    }


def _five_citations() -> list[dict[str, Any]]:
    return [
        _citation("C-001", _C1_TEXT, "smith2024preprints"),
        _citation("C-002", _C2_TEXT, "doe2024cohort"),
        _citation("C-003", _C3_TEXT, "khan2024intervention"),
        _citation("C-004", _C4_TEXT, "lin2024latency"),
        _citation("C-005", _C5_TEXT, "wei2024treatment"),
    ]


def _manifest_with_5_claims_and_mnc() -> dict[str, Any]:
    """Manifest matches each citation's (manifest_id, claim_id) pair so no
    rows fall back to the sentinel scope. MNC-1 forbids unqualified causal
    language; the c5 judge stub returns VIOLATED with MNC-1 as the binder."""
    return {
        "manifest_version": "1.0",
        "manifest_id": MANIFEST_ID,
        "emitted_by": "synthesis_agent",
        "emitted_at": "2026-05-16T08:55:00Z",
        "claims": [
            {
                "claim_id": "C-001",
                "claim_text": _C1_TEXT,
                "intended_evidence_kind": "empirical",
                "planned_refs": ["smith2024preprints"],
            },
            {
                "claim_id": "C-002",
                "claim_text": _C2_TEXT,
                "intended_evidence_kind": "empirical",
                "planned_refs": ["doe2024cohort"],
            },
            {
                "claim_id": "C-003",
                "claim_text": _C3_TEXT,
                "intended_evidence_kind": "empirical",
                "planned_refs": ["khan2024intervention"],
            },
            {
                "claim_id": "C-004",
                "claim_text": _C4_TEXT,
                "intended_evidence_kind": "empirical",
                "planned_refs": ["lin2024latency"],
            },
            {
                "claim_id": "C-005",
                "claim_text": _C5_TEXT,
                "intended_evidence_kind": "empirical",
                "planned_refs": ["wei2024treatment"],
            },
        ],
        "manifest_negative_constraints": [
            {
                "constraint_id": "MNC-1",
                "rule": "Do not assert unqualified causal claims; use hedged language.",
            }
        ],
    }


def _make_retrieve_fn(
    *,
    paywall_claim_ids: tuple[str, ...] = ("C-004",),
) -> Callable[[dict[str, Any]], dict[str, Any]]:
    """Dispatch retrieval by claim_id. c4 paywalls; others succeed via api."""

    def fn(citation: dict[str, Any]) -> dict[str, Any]:
        cid = citation["claim_id"]
        if cid in paywall_claim_ids:
            return {"ref_retrieval_method": "failed", "retrieved_excerpt": None}
        return {
            "ref_retrieval_method": "api",
            "retrieved_excerpt": f"Excerpt for {cid} from the retrieved reference.",
        }

    return fn


def _make_judge_fn(
    *,
    c3_judgment: str = "UNSUPPORTED",
    c5_judgment: str = "VIOLATED",
) -> Callable[..., dict[str, Any]]:
    """Dispatch judge by claim_text prefix.

    c3_judgment / c5_judgment let scenario B override the misuse + violation
    to clean SUPPORTED rows without changing the rest of the fixture.
    """

    def fn(**kwargs: Any) -> dict[str, Any]:
        claim_text = kwargs.get("claim_text", "")
        if claim_text.startswith("C1:"):
            return {
                "judgment": "SUPPORTED",
                "rationale": "Source excerpt verbatim confirms 67% figure.",
            }
        if claim_text.startswith("C2:"):
            return {
                "judgment": "AMBIGUOUS",
                "rationale": "Source describes adoption but ratio direction is unclear.",
                "defect_stage_hint": "source_description",
            }
        if claim_text.startswith("C3:"):
            if c3_judgment == "SUPPORTED":
                return {
                    "judgment": "SUPPORTED",
                    "rationale": "Corrected: source reports the 40% reduction.",
                }
            return {
                "judgment": "UNSUPPORTED",
                "rationale": "Source reports a 40% INCREASE, not reduction; misused.",
                "defect_stage_hint": "source_description",
            }
        if claim_text.startswith("C5:"):
            # R4 codex P2 closure: pin the negative-constraint contract
            # end-to-end. The c5 path REQUIRES `run_audit_pipeline` to
            # resolve MNC-1 from the manifest's
            # `manifest_negative_constraints[]` and pass it through to the
            # judge via `active_constraints`. Without this assertion the
            # stub would return VIOLATED regardless of whether the
            # pipeline actually delivered the constraint, and a
            # regression that silently dropped constraint resolution
            # would still see e2e PASS because the row mapping
            # (judgment=UNSUPPORTED + defect=negative_constraint_violation)
            # is downstream of the stub.
            active = kwargs.get("active_constraints", [])
            active_ids = {c.get("constraint_id") for c in active if isinstance(c, dict)}
            assert "MNC-1" in active_ids, (
                "e2e contract: pipeline must pass MNC-1 to the c5 judge call "
                f"via active_constraints; got {active!r}"
            )
            if c5_judgment == "NOT_VIOLATED":
                return {
                    "judgment": "SUPPORTED",
                    "rationale": "Rewritten with hedged language; no violation.",
                }
            return {
                "judgment": "VIOLATED",
                "violated_constraint_id": "MNC-1",
                "rationale": "Sentence asserts unqualified causation, violating MNC-1.",
            }
        raise AssertionError(
            f"unexpected claim_text dispatched to judge stub: {claim_text!r}"
        )

    return fn


def _run_e2e(
    *,
    c3_judgment: str = "UNSUPPORTED",
    c5_judgment: str = "VIOLATED",
    paywall_claim_ids: tuple[str, ...] = ("C-004",),
    extra_sentences: list[dict[str, Any]] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Drive detector → pipeline → finalizer; return (passport, finalizer_out).

    Returning both surfaces lets row-level contract assertions inspect the
    underlying `claim_audit_results[]` while finalizer-level assertions
    inspect the matrix outcome (codex Round-1 P2 contract-pinning closure).
    """
    citations = _five_citations()
    manifests = [_manifest_with_5_claims_and_mnc()]
    retrieve_fn = _make_retrieve_fn(paywall_claim_ids=paywall_claim_ids)
    judge_fn = _make_judge_fn(c3_judgment=c3_judgment, c5_judgment=c5_judgment)

    # Spec §13 step 9 contract: every e2e scenario exercises the full
    # detector → pipeline → finalizer chain. Always invoke the detector even
    # when there are no extra sentences — passing through `[]` keeps Scenario
    # A/B pinned to the wired path (/simplify advisory Q-P2-1).
    raw_sentences = list(extra_sentences or [])
    uncited_sentences = detect_uncited_assertions(raw_sentences)

    passport = run_audit_pipeline(
        citations=citations,
        manifests=manifests,
        corpus=[],
        config={"max_claims_per_paper": 100, "judge_model": "gpt-5.5-xhigh"},
        retrieve_fn=retrieve_fn,
        judge_fn=judge_fn,
        audit_run_id=AUDIT_RUN_ID,
        now_iso=NOW,
        uncited_sentences=uncited_sentences,
    )
    # apply_finalizer reads from the passport-shaped dict; the pipeline's
    # output is exactly that shape (claim_audit_results / uncited_assertions /
    # claim_drifts / constraint_violations / audit_sampling_summaries).
    return passport, apply_finalizer(passport)


class _E2ETestBase(unittest.TestCase):
    """Shared base for Step 9 e2e scenarios.

    The earlier RED-phase skip protocol (matched in
    scripts/test_claim_audit_pipeline.py::_PipelineTestBase) is removed
    here per R3 codex P2 closure: Step 9 landed in the same commit that
    made the detector / pipeline / finalizer modules importable, so the
    skip wrapper was transitional and now masks GREEN-state regressions.
    Import failures surface at module load and fail the suite instead.
    """


# ---------------------------------------------------------------------------
# Scenario A — gate refuses with exactly the c3 + c5 reasons.
# ---------------------------------------------------------------------------


class E2EScenarioARefuses(_E2ETestBase):
    def test_gate_refuses_when_c3_misused_and_c5_violates(self) -> None:
        _, out = _run_e2e()

        self.assertTrue(
            out["gate_refuse"],
            "5-citation fixture with c3 misuse + c5 constraint violation MUST flip gate_refuse",
        )

    def test_blockers_are_exactly_c3_and_c5(self) -> None:
        _, out = _run_e2e()
        reasons = out["gate_refuse_reasons"]

        # c3 surfaces as [HIGH-WARN-CLAIM-NOT-SUPPORTED]; c5 as the
        # constraint-violation literal with MNC-1 substituted.
        self.assertIn(ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED, reasons)
        self.assertIn(ANNOTATION_C5_GATE, reasons)
        self.assertEqual(
            len(reasons),
            2,
            f"only c3 + c5 should block; got {reasons!r}",
        )

    def test_c1_emits_no_annotation_c2_and_c4_pass_gate(self) -> None:
        _, out = _run_e2e()
        annotations = [a["annotation"] for a in out["annotations"]]

        # c1 SUPPORTED → no annotation row at all.
        # c2 AMBIGUOUS → LOW-WARN advisory present but not in gate reasons.
        self.assertIn(ANNOTATION_CLAIM_AUDIT_AMBIGUOUS, annotations)
        self.assertNotIn(ANNOTATION_CLAIM_AUDIT_AMBIGUOUS, out["gate_refuse_reasons"])

        # c4 paywall → LOW-WARN-UNVERIFIED present but not in gate reasons.
        self.assertIn(ANNOTATION_LOW_WARN_UNVERIFIED, annotations)
        self.assertNotIn(ANNOTATION_LOW_WARN_UNVERIFIED, out["gate_refuse_reasons"])

        # Round-1 codex P2 + Gemini P1 closure: pin the exact annotation
        # count so a regression that emits an extra row for c1 SUPPORTED
        # (or duplicates c2/c4 advisories) cannot pass this test silently.
        # Expected 4 annotations: c2 AMBIGUOUS + c3 NOT-SUPPORTED +
        # c4 UNVERIFIED + c5 NEGATIVE-CONSTRAINT.
        self.assertEqual(
            len(annotations),
            4,
            f"c1 SUPPORTED must emit zero annotations; got {annotations!r}",
        )

    def test_citation_row_contracts_match_spec_7_6_matrix(self) -> None:
        """Round-1 codex P2 closure: pin each citation's underlying row.

        Annotation-string parity is necessary but not sufficient — `C-003`
        could regress from `defect_stage=source_description` to another
        source-level UNSUPPORTED defect and still emit the same
        `[HIGH-WARN-CLAIM-NOT-SUPPORTED]` annotation. Assert the row
        shape directly so the spec §7.6 (judgment, defect_stage,
        ref_retrieval_method, violated_constraint_id) tuple is pinned
        per-citation.
        """
        passport, _ = _run_e2e()
        rows = {r["claim_id"]: r for r in passport["claim_audit_results"]}

        self.assertEqual(set(rows), {"C-001", "C-002", "C-003", "C-004", "C-005"})

        self.assertEqual(rows["C-001"]["judgment"], "SUPPORTED")
        self.assertIsNone(rows["C-001"]["defect_stage"])
        self.assertEqual(rows["C-001"]["ref_retrieval_method"], "api")

        self.assertEqual(rows["C-002"]["judgment"], "AMBIGUOUS")
        self.assertEqual(rows["C-002"]["defect_stage"], "source_description")
        self.assertEqual(rows["C-002"]["ref_retrieval_method"], "api")

        self.assertEqual(rows["C-003"]["judgment"], "UNSUPPORTED")
        self.assertEqual(rows["C-003"]["defect_stage"], "source_description")
        self.assertEqual(rows["C-003"]["ref_retrieval_method"], "api")

        self.assertEqual(rows["C-004"]["judgment"], "RETRIEVAL_FAILED")
        self.assertEqual(rows["C-004"]["defect_stage"], "not_applicable")
        self.assertEqual(rows["C-004"]["ref_retrieval_method"], "failed")

        self.assertEqual(rows["C-005"]["judgment"], "UNSUPPORTED")
        self.assertEqual(rows["C-005"]["defect_stage"], "negative_constraint_violation")
        self.assertEqual(rows["C-005"]["ref_retrieval_method"], "api")
        self.assertEqual(rows["C-005"]["violated_constraint_id"], "MNC-1")


# ---------------------------------------------------------------------------
# Scenario B — corrected fixture passes the gate.
# ---------------------------------------------------------------------------


class E2EScenarioBPasses(_E2ETestBase):
    def test_correcting_c3_and_c5_clears_refusal(self) -> None:
        _, out = _run_e2e(c3_judgment="SUPPORTED", c5_judgment="NOT_VIOLATED")

        self.assertFalse(
            out["gate_refuse"],
            "after c3 corrected + c5 rewritten the gate MUST pass; "
            f"got reasons={out['gate_refuse_reasons']!r}",
        )
        self.assertEqual(out["gate_refuse_reasons"], [])

    def test_corrected_run_keeps_c2_advisory_and_c4_unverified(self) -> None:
        _, out = _run_e2e(c3_judgment="SUPPORTED", c5_judgment="NOT_VIOLATED")
        annotations = [a["annotation"] for a in out["annotations"]]

        # c2 AMBIGUOUS + c4 paywall persist independently of c3/c5 fixes —
        # the corrections only touch c3 + c5 judgments.
        self.assertIn(ANNOTATION_CLAIM_AUDIT_AMBIGUOUS, annotations)
        self.assertIn(ANNOTATION_LOW_WARN_UNVERIFIED, annotations)

        # Round-1 Gemini P1 closure: pin the exact annotation count so a
        # regression that re-emits c3/c5 annotations after correction (or
        # spuriously adds rows for c1) cannot pass silently. After
        # correction Scenario B carries exactly 2 annotations: c2
        # AMBIGUOUS + c4 UNVERIFIED. c1/c3/c5 SUPPORTED → zero annotations.
        self.assertEqual(
            len(annotations),
            2,
            f"corrected fixture must emit exactly 2 advisory annotations; got {annotations!r}",
        )
        self.assertNotIn(ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED, annotations)
        self.assertNotIn(ANNOTATION_C5_GATE, annotations)


# ---------------------------------------------------------------------------
# DEFERRED-CROSS-SENTENCE Step-9 closure: detector accepts an optional
# `adjacent_text` field; when that adjacent window carries a `<!--ref:slug-->`
# marker, the candidate is filtered out before reaching the pipeline.
# ---------------------------------------------------------------------------


class E2EAdjacentClauseFilter(_E2ETestBase):
    def test_sentence_with_adjacent_ref_marker_is_filtered_out(self) -> None:
        # Token-rule fires on "67%" but the adjacent clause already carries
        # the ref marker. Per spec line 251 + the DEFERRED-CROSS-SENTENCE
        # note, this sentence MUST NOT become an uncited_assertion candidate.
        sentence = {
            "sentence_text": "Of the corpus, 67% were preprints.",
            "section_path": "3. Results > 3.1 Overview",
            "adjacent_text": "Smith et al. report this ratio <!--ref:smith2024preprints-->.",
        }
        candidates = detect_uncited_assertions([sentence])
        self.assertEqual(
            candidates,
            [],
            "adjacent ref marker MUST suppress the candidate (spec line 251 / Step 9 closure)",
        )

    def test_sentence_without_adjacent_ref_marker_still_a_candidate(self) -> None:
        # Same token-rule trigger but no adjacent ref marker — the standard
        # T-U1 detector behavior should still fire.
        sentence = {
            "sentence_text": "Of the corpus, 67% were preprints.",
            "section_path": "3. Results > 3.1 Overview",
            "adjacent_text": "The next paragraph discusses methodology.",
        }
        candidates = detect_uncited_assertions([sentence])
        self.assertEqual(len(candidates), 1)
        self.assertIn("67", "".join(candidates[0]["trigger_tokens"]))

    def test_e2e_pipeline_runs_through_filtered_sentences_cleanly(self) -> None:
        # Smoke test the detector → pipeline → finalizer path with one
        # filtered + one surviving sentence. The surviving uncited
        # assertion adds an advisory row but does not gate-refuse on its own;
        # c3 + c5 still drive the gate. This confirms detector wiring does
        # not regress the 5-citation contract.
        filtered_text = "Of the corpus, 67% were preprints."
        surviving_text = "Several teams reported similar gains."
        extra = [
            {
                "sentence_text": filtered_text,
                "section_path": "3. Results > 3.1 Overview",
                "adjacent_text": "Smith et al. <!--ref:smith2024preprints-->.",
            },
            {
                "sentence_text": surviving_text,
                "section_path": "3. Results > 3.2 Replication",
            },
        ]
        passport, out = _run_e2e(extra_sentences=extra)
        self.assertTrue(out["gate_refuse"])  # c3 + c5 still drive the gate
        # Exactly two HIGH-WARN reasons — uncited advisory does not promote
        # to gate-refuse.
        self.assertEqual(len(out["gate_refuse_reasons"]), 2)

        # Round-1 codex P2 closure: pin that the detector → pipeline wiring
        # actually consumed the surviving sentence and the finalizer emitted
        # an [UNCITED-ASSERTION] row keyed off the right aggregate. Without
        # these the test would still pass if `run_audit_pipeline` silently
        # stopped processing `uncited_sentences` or `apply_finalizer`
        # dropped its `classify_uncited_assertion` routing.
        self.assertEqual(
            len(passport["uncited_assertions"]),
            1,
            f"surviving sentence must produce exactly 1 uncited_assertion row; "
            f"got {passport['uncited_assertions']!r}",
        )
        self.assertEqual(passport["uncited_assertions"][0]["sentence_text"], surviving_text)
        # Filtered sentence MUST NOT appear in the passport.
        for row in passport["uncited_assertions"]:
            self.assertNotEqual(row["sentence_text"], filtered_text)
        # Finalizer routes the row through classify_uncited_assertion with
        # aggregate="uncited_assertions" and annotation [UNCITED-ASSERTION].
        uncited_anns = [
            a for a in out["annotations"]
            if a.get("aggregate") == "uncited_assertions"
        ]
        self.assertEqual(len(uncited_anns), 1)
        self.assertEqual(uncited_anns[0]["annotation"], ANNOTATION_UNCITED_ASSERTION)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
