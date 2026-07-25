"""Schema-validation tests for v3.8 claim_ref_alignment_audit_agent (T-S1..T-S8).

Per spec §7.1 in
docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md.

The test plan section §7.1 lists T-S1..T-S8 keyed to claim_audit_result
(§3.1) and claim_intent_manifest (§3.2) and uncited_assertion (§3.3).
§6 lint coverage is broader: it includes claim_drift D-INV-1..4 (§3.4),
constraint_violation CV-INV-1..4 (§3.5) and audit_sampling_summary
S-INV-1..4 (§4 step 3). This file follows §6 because that is the lint
contract under test — drift / constraint-violation / sampling
invariants get their own pos/neg fixtures alongside INV / M-INV / U-INV
so the lint's full 38-invariant surface is covered before the agent
prompt ships in Step 5.

Spec §7 names the test file `tests/test_claim_audit_schema.py`. This
repo's CI workflows discover tests under `scripts/test_*.py` and the
30+ existing test files all live there; we honor the repo convention
and keep the spec name's stem (`test_claim_audit_schema`) so anyone
greppping the spec lands at the right file.

Run:
    python -m unittest scripts.test_claim_audit_schema -v
"""
from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path
from typing import Any

from tests.test_helpers import (
    build_schema_validator,
    load_json_schema,
    run_script,
)

REPO = Path(__file__).resolve().parent.parent
PASSPORT = REPO / "shared/contracts/passport"
LINT = REPO / "scripts/check_claim_audit_consistency.py"

SCHEMA_PATHS: dict[str, Path] = {
    "claim_audit_result": PASSPORT / "claim_audit_result.schema.json",
    "claim_intent_manifest": PASSPORT / "claim_intent_manifest.schema.json",
    "uncited_assertion": PASSPORT / "uncited_assertion.schema.json",
    "claim_drift": PASSPORT / "claim_drift.schema.json",
    "constraint_violation": PASSPORT / "constraint_violation.schema.json",
    "uncited_audit_failure": PASSPORT / "uncited_audit_failure.schema.json",
}


# ---------------------------------------------------------------------------
# Canonical fixture builders. Each helper returns a fresh dict so individual
# tests can mutate one field without leaking to siblings.
# ---------------------------------------------------------------------------

MANIFEST_ID = "M-2026-05-15T10:00:00Z-a1b2"
MANIFEST_ID_OTHER = "M-2026-05-15T10:05:00Z-c3d4"
SENTINEL_MANIFEST_ID = "M-0000-00-00T00:00:00Z-0000"
AUDIT_RUN_ID = "2026-05-15T10:10:00Z-9f8e"


def supported_entry() -> dict[str, Any]:
    """Minimal SUPPORTED row — INV-1 positive baseline."""
    return {
        "claim_id": "C-001",
        "scoped_manifest_id": MANIFEST_ID,
        "claim_text": "Sample preprints accounted for 67% of corpus.",
        "ref_slug": "smith2024preprints",
        "anchor_kind": "page",
        "anchor_value": "12",
        "judgment": "SUPPORTED",
        "audit_status": "completed",
        "defect_stage": None,
        "rationale": "The cited page reports the 67% figure verbatim.",
        "judge_model": "gpt-5.5-xhigh",
        "judge_run_at": "2026-05-15T10:11:00Z",
        "ref_retrieval_method": "api",
        "audit_run_id": AUDIT_RUN_ID,
    }


def manifest_entry(
    manifest_id: str = MANIFEST_ID,
    *,
    emitted_by: str = "synthesis_agent",
    claims: list[dict[str, Any]] | None = None,
    mncs: list[dict[str, str]] | None = None,
) -> dict[str, Any]:
    """Build a minimal claim_intent_manifest entry."""
    return {
        "manifest_version": "1.0",
        "manifest_id": manifest_id,
        "emitted_by": emitted_by,
        "emitted_at": "2026-05-15T09:55:00Z",
        "claims": claims
        if claims is not None
        else [
            {
                "claim_id": "C-001",
                "claim_text": "Sample preprints accounted for 67% of corpus.",
                "intended_evidence_kind": "empirical",
                "planned_refs": ["smith2024preprints"],
            }
        ],
        "manifest_negative_constraints": mncs or [],
    }


def uncited_assertion_entry() -> dict[str, Any]:
    """Minimal U-INV-* positive baseline."""
    return {
        "finding_id": "UA-001",
        "sentence_text": "Half of all submissions showed positive results.",
        "section_path": "3. Results > 3.1 Overview",
        "trigger_tokens": ["50%", "showed"],
        "detected_at": "2026-05-15T10:12:00Z",
        "rule_version": "D4-c-v1",
    }


def claim_drift_entry(*, drift_kind: str = "EMITTED_NOT_INTENDED") -> dict[str, Any]:
    """Minimal D-INV-* positive baseline."""
    base: dict[str, Any] = {
        "finding_id": "CD-001",
        "drift_kind": drift_kind,
        "claim_text": "Drifted prose sentence the writer added without manifesting.",
        "detected_at": "2026-05-15T10:13:00Z",
        "rule_version": "D4-a-v1",
    }
    if drift_kind == "EMITTED_NOT_INTENDED":
        base["section_path"] = "4. Discussion > 4.2 Implications"
        base["manifest_claim_id"] = None
        base["scoped_manifest_id"] = None
    else:  # INTENDED_NOT_EMITTED
        base["manifest_claim_id"] = "C-001"
        base["scoped_manifest_id"] = MANIFEST_ID
    return base


def constraint_violation_entry(
    *,
    constraint_id: str = "MNC-1",
    manifest_claim_id: str | None = None,
) -> dict[str, Any]:
    """Minimal CV-INV-* positive baseline."""
    return {
        "finding_id": "CV-001",
        "claim_text": "We observed causality between A and B.",
        "section_path": "4. Discussion > 4.3 Limitations",
        "violated_constraint_id": constraint_id,
        "scoped_manifest_id": MANIFEST_ID,
        "manifest_claim_id": manifest_claim_id,
        "judge_verdict": "VIOLATED",
        "rationale": "The MNC bars causal language without RCT evidence.",
        "judge_model": "gpt-5.5-xhigh",
        "judge_run_at": "2026-05-15T10:14:00Z",
        "rule_version": "D4-a-v1",
    }


def sampling_summary_entry(
    *,
    total: int = 150,
    cap: int = 100,
) -> dict[str, Any]:
    """Minimal S-INV-* positive baseline (sampled run)."""
    audited = list(range(0, total, max(1, total // cap)))[:cap]
    return {
        "audit_run_id": AUDIT_RUN_ID,
        "max_claims_per_paper": cap,
        "total_citation_count": total,
        "audited_count": len(audited),
        "audited_indices": audited,
        "sampling_strategy": "stratified_buckets_v1",
        "emitted_at": "2026-05-15T10:15:00Z",
    }


def uncited_audit_failure_entry(
    *,
    finding_id: str = "UAF-001",
    fault_class: str = "judge_timeout",
    manifest_claim_id: str | None = None,
) -> dict[str, Any]:
    """Minimal UAF-INV-* positive baseline (v3.8.2 / #118)."""
    return {
        "finding_id": finding_id,
        "claim_text": "We observed causality between A and B.",
        "section_path": "4. Discussion > 4.3 Limitations",
        "scoped_manifest_id": MANIFEST_ID,
        "manifest_claim_id": manifest_claim_id,
        "fault_class": fault_class,
        "rationale": f"{fault_class}: judge invocation failed after 30s",
        "judge_model": "gpt-5.5-xhigh",
        "judge_run_at": "2026-05-15T10:14:00Z",
        "rule_version": "D4-c-v1-uaf-v1",
    }


def build_passport(
    *,
    manifests: list[dict[str, Any]] | None = None,
    results: list[dict[str, Any]] | None = None,
    uncited: list[dict[str, Any]] | None = None,
    drifts: list[dict[str, Any]] | None = None,
    violations: list[dict[str, Any]] | None = None,
    samplings: list[dict[str, Any]] | None = None,
    uaf: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build a minimal passport JSON wrapping the seven aggregates the lint reads (six pre-v3.8.2 + uncited_audit_failures[])."""
    return {
        "claim_intent_manifests": manifests if manifests is not None else [manifest_entry()],
        "claim_audit_results": results or [],
        "uncited_assertions": uncited or [],
        "claim_drifts": drifts or [],
        "constraint_violations": violations or [],
        "audit_sampling_summaries": samplings or [],
        "uncited_audit_failures": uaf or [],
    }


def write_passport(tmp: Path, body: dict[str, Any]) -> Path:
    path = tmp / "passport.json"
    path.write_text(json.dumps(body, ensure_ascii=False, indent=2), encoding="utf-8")
    return path


def run_lint(passport: Path) -> tuple[int, str, str]:
    """Invoke the lint subprocess; returns (exit_code, stdout, stderr)."""
    proc = run_script(
        LINT,
        "--passport",
        str(passport),
        extra_env={"PYTHONPATH": str(REPO)},
    )
    return proc.returncode, proc.stdout, proc.stderr


# ---------------------------------------------------------------------------
# T-S1: Schema-shape only — minimal SUPPORTED entry validates against the
# claim_audit_result schema. No lint invocation; pure Draft 2020-12 validate.
# ---------------------------------------------------------------------------

class TS1ValidMinimalEntry(unittest.TestCase):
    """T-S1: Valid minimal entry validates (SUPPORTED, all required fields)."""

    def test_supported_entry_validates(self) -> None:
        schema = load_json_schema(SCHEMA_PATHS["claim_audit_result"])
        validator = build_schema_validator(schema)
        errors = list(validator.iter_errors(supported_entry()))
        self.assertEqual(errors, [], msg=f"unexpected validation errors: {errors}")

    def test_all_five_schemas_parse_as_draft_2020_12(self) -> None:
        for name, path in SCHEMA_PATHS.items():
            with self.subTest(schema=name):
                load_json_schema(path)

    def test_subclaim_breakdown_optional_field_validates(self) -> None:
        """T-S9 (#213): sub_claim_breakdown is an additive optional field."""
        schema = load_json_schema(SCHEMA_PATHS["claim_audit_result"])
        validator = build_schema_validator(schema)
        entry = supported_entry()
        entry["judgment"] = "UNSUPPORTED"
        entry["defect_stage"] = "source_description"
        entry["sub_claim_breakdown"] = [
            {
                "sub_claim_text": "n-values are reported",
                "sub_verdict": "SUPPORTED",
                "evidence_pointer": "p.4 Table 1",
            },
            {
                "sub_claim_text": "reporting is consistent across models",
                "sub_verdict": "UNSUPPORTED",
                "evidence_pointer": None,
            },
        ]
        errors = list(validator.iter_errors(entry))
        self.assertEqual(errors, [], msg=f"unexpected validation errors: {errors}")

    def test_subclaim_breakdown_rejects_unknown_subfield(self) -> None:
        """additionalProperties:false holds inside each breakdown item.

        Two valid items satisfy minItems:2 so the ONLY violation is the bogus
        subfield — this isolates additionalProperties:false from the array-length
        constraint (round-2 review #2: a one-item fixture also tripped minItems,
        so it would still pass even if additionalProperties were removed).
        """
        schema = load_json_schema(SCHEMA_PATHS["claim_audit_result"])
        validator = build_schema_validator(schema)
        entry = supported_entry()
        entry["judgment"] = "UNSUPPORTED"
        entry["defect_stage"] = "source_description"
        entry["sub_claim_breakdown"] = [
            {"sub_claim_text": "x", "sub_verdict": "SUPPORTED", "bogus": 1},
            {"sub_claim_text": "y", "sub_verdict": "UNSUPPORTED"},
        ]
        errors = list(validator.iter_errors(entry))
        self.assertNotEqual(errors, [], msg="expected unknown subfield to be rejected")
        self.assertTrue(
            any(e.validator == "additionalProperties" for e in errors),
            msg=f"expected an additionalProperties error, got: {[e.validator for e in errors]}",
        )


# ---------------------------------------------------------------------------
# Lint-driven invariant tests share a base that writes a tmp passport,
# invokes the lint subprocess, and asserts findings.
# ---------------------------------------------------------------------------

class _LintTestBase(unittest.TestCase):
    def setUp(self) -> None:
        # Each test owns its tmpdir so concurrent unittest runners don't collide.
        import tempfile

        self._tmp_obj = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp_obj.cleanup)
        self.tmp = Path(self._tmp_obj.name)

    def assertLintFinds(
        self,
        passport_body: dict[str, Any],
        *,
        invariant: str,
        msg: str | None = None,
    ) -> tuple[int, str]:
        """Assert lint exits non-zero AND stdout contains `invariant` tag."""
        path = write_passport(self.tmp, passport_body)
        code, out, err = run_lint(path)
        full_msg = (
            f"\nexpected lint to flag {invariant}\n"
            f"--- exit={code} ---\nstdout:\n{out}\nstderr:\n{err}\n"
        )
        self.assertEqual(code, 1, msg=full_msg)
        self.assertIn(invariant, out, msg=full_msg)
        return code, out

    def assertLintClean(
        self,
        passport_body: dict[str, Any],
        *,
        msg: str | None = None,
    ) -> None:
        """Assert lint exits 0 (no findings) on a passport that should pass."""
        path = write_passport(self.tmp, passport_body)
        code, out, err = run_lint(path)
        self.assertEqual(
            code,
            0,
            msg=(msg or "")
            + f"\nexpected lint clean\nexit={code}\nstdout:\n{out}\nstderr:\n{err}\n",
        )


# ---------------------------------------------------------------------------
# T-S2: INV-1..INV-19 paired positive + negative fixtures (claim_audit_result).
# Each invariant is one subTest; baseline = SUPPORTED entry, negative cases
# mutate the field combination the invariant forbids.
# ---------------------------------------------------------------------------

class TS2ClaimAuditInvariants(_LintTestBase):
    """T-S2: each INV-N paired positive/negative fixture."""

    # ----- Positive: every INV holds when the canonical SUPPORTED row stands.
    def test_inv_baseline_positive(self) -> None:
        self.assertLintClean(build_passport(results=[supported_entry()]))

    # ----- Negative cases per invariant.
    def test_inv_1_supported_with_non_null_defect(self) -> None:
        # INV-1: SUPPORTED -> defect_stage=null AND violated_constraint_id=null
        e = supported_entry()
        e["defect_stage"] = "source_description"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-1")

    def test_inv_2_unsupported_with_null_defect(self) -> None:
        # INV-2: UNSUPPORTED -> defect_stage != null
        e = supported_entry()
        e["judgment"] = "UNSUPPORTED"
        e["defect_stage"] = None
        e["rationale"] = "Mismatch found in source description."
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-2")

    def test_inv_3_ambiguous_with_disallowed_defect(self) -> None:
        # INV-3: AMBIGUOUS -> defect_stage NOT in {metadata, negative_constraint_violation}
        e = supported_entry()
        e["judgment"] = "AMBIGUOUS"
        e["defect_stage"] = "metadata"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-3")

    def test_inv_4_retrieval_failed_inconclusive_wrong_defect(self) -> None:
        # INV-4: RETRIEVAL_FAILED + inconclusive -> defect_stage=not_applicable
        e = supported_entry()
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "retrieval_existence"
        e["ref_retrieval_method"] = "failed"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-4")

    def test_inv_5_retrieval_failed_completed_wrong_defect(self) -> None:
        # INV-5: RETRIEVAL_FAILED + completed -> defect_stage=retrieval_existence
        e = supported_entry()
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "completed"
        e["defect_stage"] = "source_description"
        e["ref_retrieval_method"] = "not_found"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-5")

    def test_inv_6_anchor_none_without_rationale_prefix(self) -> None:
        # INV-6: anchor_kind=none -> rationale starts with the canonical prefix
        e = supported_entry()
        e["anchor_kind"] = "none"
        e["anchor_value"] = ""
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "not_applicable"
        e["ref_retrieval_method"] = "not_attempted"
        e["rationale"] = "anchor missing for this claim"  # no v3.7.3 prefix
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-6")

    def test_inv_6_anchor_none_with_non_empty_anchor_value(self) -> None:
        # INV-6: anchor_kind=none MUST carry empty sentinel anchor_value.
        # A stale residual value (e.g. "123") violates the schema contract.
        # Step 13 R1 Gemini finding (a832d3f).
        e = supported_entry()
        e["anchor_kind"] = "none"
        e["anchor_value"] = "123"  # stale residual — must be rejected
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "not_applicable"
        e["ref_retrieval_method"] = "not_attempted"
        e["rationale"] = (
            "v3.7.3 R-L3-1-A violation: cited claim C-001 carries anchor=none; "
            "v3.7.3 finalizer should have gate-refused upstream."
        )
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-6")

    def test_inv_7_constraint_violation_without_violated_id(self) -> None:
        # INV-7: negative_constraint_violation -> violated_constraint_id != null
        e = supported_entry()
        e["judgment"] = "UNSUPPORTED"
        e["defect_stage"] = "negative_constraint_violation"
        e["rationale"] = "Violated declared negative constraint."
        e["violated_constraint_id"] = None
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-7")

    def test_inv_8_constraint_violation_wrong_judgment(self) -> None:
        # INV-8: negative_constraint_violation -> judgment=UNSUPPORTED
        e = supported_entry()
        e["judgment"] = "AMBIGUOUS"
        e["defect_stage"] = "negative_constraint_violation"
        e["violated_constraint_id"] = "MNC-1"
        e["rationale"] = "Ambiguous violation of MNC-1."
        # INV-3 also fires here; we assert INV-8 specifically.
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-8")

    def test_inv_9_dispute_on_not_applicable(self) -> None:
        # INV-9: upstream_dispute != null -> defect_stage NOT in {null, not_applicable}
        e = supported_entry()
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "not_applicable"
        e["ref_retrieval_method"] = "failed"
        e["rationale"] = "Paywalled."
        e["upstream_dispute"] = "Author disputes this paywall classification."
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-9")

    def test_inv_10_failed_method_wrong_state(self) -> None:
        # INV-10: ref_retrieval_method=failed -> RETRIEVAL_FAILED + inconclusive + not_applicable
        e = supported_entry()
        e["ref_retrieval_method"] = "failed"
        # judgment still SUPPORTED -> INV-10 violation
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-10")

    def test_inv_11_not_attempted_without_anchor_none(self) -> None:
        # INV-11: ref_retrieval_method=not_attempted iff anchor_kind=none
        e = supported_entry()
        e["ref_retrieval_method"] = "not_attempted"
        # anchor_kind still page -> INV-11 violation
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-11")

    def test_inv_12_not_found_wrong_state(self) -> None:
        # INV-12: ref_retrieval_method=not_found iff fabricated-reference triple
        e = supported_entry()
        e["ref_retrieval_method"] = "not_found"
        # judgment still SUPPORTED -> INV-12 violation
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-12")

    def test_inv_13_metadata_wrong_method(self) -> None:
        # INV-13: defect_stage=metadata -> ref_retrieval_method in {api, manual_pdf}
        e = supported_entry()
        e["judgment"] = "UNSUPPORTED"
        e["defect_stage"] = "metadata"
        e["rationale"] = "Author/year mismatch."
        e["ref_retrieval_method"] = "failed"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-13")

    def test_inv_14_audit_tool_failure_without_fault_class_prefix(self) -> None:
        # INV-14: ref_retrieval_method=audit_tool_failure -> rationale begins with fault-class tag
        e = supported_entry()
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "not_applicable"
        e["ref_retrieval_method"] = "audit_tool_failure"
        e["rationale"] = "Something went wrong."  # missing tag
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-14")

    def test_inv_15_dangling_scoped_manifest_id(self) -> None:
        # INV-15: (scoped_manifest_id, claim_id) must resolve in some manifest entry
        e = supported_entry()
        e["scoped_manifest_id"] = "M-2099-01-01T00:00:00Z-dead"  # not in manifests
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-15")

    def test_inv_15_sentinel_manifest_permitted(self) -> None:
        # INV-15 sentinel positive case — MANIFEST-MISSING fallback row.
        e = supported_entry()
        e["scoped_manifest_id"] = SENTINEL_MANIFEST_ID
        passport = build_passport(manifests=[], results=[e])
        self.assertLintClean(
            passport,
            msg="sentinel scoped_manifest_id must be accepted in MANIFEST-MISSING fallback",
        )

    def test_inv_16_empty_anchor_value_with_non_none_kind(self) -> None:
        # INV-16: anchor_kind != none -> anchor_value non-empty after strip
        e = supported_entry()
        e["anchor_value"] = "   "  # whitespace only
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-16")

    def test_inv_16_url_encoded_whitespace_does_not_bypass(self) -> None:
        # INV-16: URL-encoded whitespace (%20, %09) must NOT bypass the firm
        # rule — docstring + schema both require non-empty *after* URL-decode.
        # Step 13 R1 Gemini finding (a832d3f).
        e = supported_entry()
        e["anchor_value"] = "%20%20%09"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-16")

    def test_inv_16_url_encoded_non_whitespace_passes(self) -> None:
        # INV-16: URL-encoded printable content must still satisfy the rule.
        e = supported_entry()
        e["anchor_kind"] = "quote"
        e["anchor_value"] = "ten%20cited%20words"  # 'ten cited words' after decode
        self.assertLintClean(build_passport(results=[e]))

    def test_inv_17_constraint_id_inner_hyphen_form(self) -> None:
        # INV-17: NC-C{n}-{m} parse rule — NO inner hyphen between C and digits
        manifest = manifest_entry(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Causal claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {
                            # malformed: NC-C-001-1 instead of NC-C001-1
                            "constraint_id": "NC-C-001-1",
                            "rule": "Must not claim causality without RCT.",
                        }
                    ],
                }
            ],
        )
        # Schema pattern itself rejects this — lint surfaces INV-17 explicitly.
        passport = build_passport(manifests=[manifest], results=[])
        self.assertLintFinds(passport, invariant="INV-17")

    def test_inv_18_inconclusive_not_applicable_wrong_method(self) -> None:
        # INV-18: (RETRIEVAL_FAILED, inconclusive, not_applicable) -> method in
        # {not_attempted, failed, audit_tool_failure}. `api` is forbidden.
        e = supported_entry()
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "not_applicable"
        e["ref_retrieval_method"] = "api"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-18")

    # ----- INV-19 (#213): sub_claim_breakdown pins the normalized-PARTIAL shape.
    def _partial_entry(self) -> dict[str, Any]:
        """True-partial UNSUPPORTED row: the INV-19 positive baseline."""
        e = supported_entry()
        e["judgment"] = "UNSUPPORTED"
        e["audit_status"] = "completed"
        e["defect_stage"] = "source_description"
        e["sub_claim_breakdown"] = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "b", "sub_verdict": "UNSUPPORTED"},
        ]
        return e

    def test_inv_19_valid_partial_breakdown_passes(self) -> None:
        # INV-19 positive baseline: a true-partial row is clean.
        self.assertLintClean(build_passport(results=[self._partial_entry()]))

    def test_inv_19_breakdown_on_supported_row_flagged(self) -> None:
        # INV-19: a sub_claim_breakdown on a non-UNSUPPORTED row is illegal.
        e = supported_entry()  # judgment=SUPPORTED, defect_stage=None
        e["sub_claim_breakdown"] = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "b", "sub_verdict": "UNSUPPORTED"},
        ]
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")

    def test_inv_19_breakdown_wrong_defect_stage_flagged(self) -> None:
        # INV-19: breakdown row must carry defect_stage=source_description.
        e = self._partial_entry()
        e["defect_stage"] = "synthesis_overclaim"
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")

    def test_inv_19_all_unsupported_breakdown_flagged(self) -> None:
        # INV-19: not true-partial — needs >=1 SUPPORTED (round-1 review #2).
        e = self._partial_entry()
        e["sub_claim_breakdown"] = [
            {"sub_claim_text": "a", "sub_verdict": "UNSUPPORTED"},
            {"sub_claim_text": "b", "sub_verdict": "UNSUPPORTED"},
        ]
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")

    def test_inv_19_all_supported_breakdown_flagged(self) -> None:
        # INV-19: not true-partial — needs >=1 non-SUPPORTED.
        e = self._partial_entry()
        e["sub_claim_breakdown"] = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "b", "sub_verdict": "SUPPORTED"},
        ]
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")

    def test_inv_19_single_item_breakdown_flagged(self) -> None:
        # INV-19: a decomposition with <2 items is not a true partial.
        e = self._partial_entry()
        e["sub_claim_breakdown"] = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
        ]
        # schema minItems:2 also rejects this; lint must independently flag it
        # so a future schema relaxation can't silently admit a 1-item breakdown.
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")

    def test_inv_19_breakdown_on_ambiguous_row_flagged(self) -> None:
        # INV-19 judgment-pin isolation: AMBIGUOUS + completed + source_description
        # passes INV-3 AND is in ALLOWED_MATRIX, so the ONLY invariant that can
        # fire is INV-19's judgment check. This catches a partially-broken guard
        # that forgets the judgment pin but keeps the defect_stage pin — which the
        # SUPPORTED-row case can't catch (it also has defect_stage=None).
        # (round-2 review #3.)
        e = self._partial_entry()
        e["judgment"] = "AMBIGUOUS"  # defect_stage stays source_description
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")

    def test_inv_19_missing_sub_verdict_not_counted_as_non_supported(self) -> None:
        # INV-19 must NOT read a missing/out-of-enum sub_verdict as "non-SUPPORTED"
        # (round-2 review #1). [SUPPORTED, <missing>] is NOT true-partial: it has no
        # valid non-SUPPORTED verdict. A guard using `v != "SUPPORTED"` would wrongly
        # accept it. The schema also rejects the missing required key, but INV-19 must
        # independently flag the not-true-partial shape with its own tag.
        e = self._partial_entry()
        e["sub_claim_breakdown"] = [
            {"sub_claim_text": "a", "sub_verdict": "SUPPORTED"},
            {"sub_claim_text": "b"},  # sub_verdict missing -> not a valid non-SUPPORTED
        ]
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-19")


# ---------------------------------------------------------------------------
# T-S3: anchor_kind=none + INV-6 violation paths.
# ---------------------------------------------------------------------------

class TS3AnchorNoneInv6(_LintTestBase):
    """T-S3: anchor=none entries that miss rationale prefix or use wrong method."""

    def _none_entry(self) -> dict[str, Any]:
        e = supported_entry()
        e["anchor_kind"] = "none"
        e["anchor_value"] = ""
        e["judgment"] = "RETRIEVAL_FAILED"
        e["audit_status"] = "inconclusive"
        e["defect_stage"] = "not_applicable"
        e["ref_retrieval_method"] = "not_attempted"
        e["rationale"] = "v3.7.3 R-L3-1-A violation: no anchor on cited claim."
        return e

    def test_anchor_none_positive_baseline(self) -> None:
        # Canonical INV-6 compliant row should pass.
        self.assertLintClean(build_passport(results=[self._none_entry()]))

    def test_anchor_none_missing_rationale_prefix(self) -> None:
        e = self._none_entry()
        e["rationale"] = "anchor missing"  # no prefix
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-6")

    def test_anchor_none_wrong_retrieval_method(self) -> None:
        e = self._none_entry()
        e["ref_retrieval_method"] = "failed"  # should be not_attempted
        # INV-11 ↔ INV-6 mismatch — either fires; spec couples the firm rule via INV-6/11.
        self.assertLintFinds(build_passport(results=[e]), invariant="INV-6")


# ---------------------------------------------------------------------------
# T-S4: M-INV-1 duplicate claim_id within ONE manifest.
# ---------------------------------------------------------------------------

class TS4ManifestInv1(_LintTestBase):
    """T-S4: duplicate claim_id within one manifest is rejected; cross-manifest collision permitted."""

    def test_duplicate_claim_id_within_one_manifest_rejected(self) -> None:
        manifest = manifest_entry(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "First claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                },
                {
                    "claim_id": "C-001",  # duplicate within ONE manifest
                    "claim_text": "Second collision.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                },
            ],
        )
        self.assertLintFinds(
            build_passport(manifests=[manifest]),
            invariant="M-INV-1",
        )

    def test_cross_manifest_claim_id_collision_permitted(self) -> None:
        manifest_a = manifest_entry(manifest_id=MANIFEST_ID)
        manifest_b = manifest_entry(
            manifest_id=MANIFEST_ID_OTHER,
            emitted_by="draft_writer_agent",
        )
        self.assertLintClean(
            build_passport(manifests=[manifest_a, manifest_b]),
            msg="cross-manifest C-001 collision MUST be permitted (joinable pair)",
        )

    def test_m_inv_4_duplicate_manifest_id_across_passport_rejected(self) -> None:
        manifest_a = manifest_entry(manifest_id=MANIFEST_ID)
        manifest_b = manifest_entry(
            manifest_id=MANIFEST_ID,  # collides with manifest_a
            emitted_by="draft_writer_agent",
        )
        self.assertLintFinds(
            build_passport(manifests=[manifest_a, manifest_b]),
            invariant="M-INV-4",
        )


# ---------------------------------------------------------------------------
# T-S5: M-INV-2 dangling NC-C{n}-{m} (no parent claim with C-{n}).
# ---------------------------------------------------------------------------

class TS5ManifestInv2(_LintTestBase):
    """T-S5: NC-C{n}-{m} must scope under a claims[] entry with claim_id=C-{n}."""

    def test_dangling_claim_level_nc(self) -> None:
        manifest = manifest_entry(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "First claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {
                            # NC scoped to C-002, but no C-002 claim exists.
                            "constraint_id": "NC-C002-1",
                            "rule": "Mismatched parent.",
                        }
                    ],
                }
            ],
        )
        self.assertLintFinds(
            build_passport(manifests=[manifest]),
            invariant="M-INV-2",
        )


# ---------------------------------------------------------------------------
# T-S6: M-INV-3 claim-level NC attempting to override MNC.
# ---------------------------------------------------------------------------

class TS6ManifestInv3(_LintTestBase):
    """T-S6: claim-level NC cannot DROP a global MNC; ADD is permitted."""

    def test_claim_level_nc_collides_with_mnc_id(self) -> None:
        # M-INV-3 — claim-level constraint reusing an MNC-* id is the override
        # signature the lint must reject (claim level can ADD via fresh NC-C{n}-{m}
        # ids, never via re-using an MNC-* id).
        manifest = manifest_entry(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Causal claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {
                            "constraint_id": "MNC-1",  # disallowed at claim level
                            "rule": "Trying to override.",
                        }
                    ],
                }
            ],
            mncs=[
                {
                    "constraint_id": "MNC-1",
                    "rule": "Must not claim causality.",
                }
            ],
        )
        self.assertLintFinds(
            build_passport(manifests=[manifest]),
            invariant="M-INV-3",
        )


# ---------------------------------------------------------------------------
# T-S7: U-INV-1..U-INV-4 paired positive/negative.
# ---------------------------------------------------------------------------

class TS7UncitedAssertionInvariants(_LintTestBase):
    """T-S7: U-INV-1..U-INV-4 paired pos/neg fixtures."""

    def test_u_baseline_positive(self) -> None:
        self.assertLintClean(build_passport(uncited=[uncited_assertion_entry()]))

    def test_u_inv_1_duplicate_finding_id(self) -> None:
        a = uncited_assertion_entry()
        b = uncited_assertion_entry()  # same UA-001
        self.assertLintFinds(
            build_passport(uncited=[a, b]),
            invariant="U-INV-1",
        )

    def test_u_inv_2_empty_trigger_tokens(self) -> None:
        e = uncited_assertion_entry()
        e["trigger_tokens"] = []
        # Schema also rejects (minItems=1); lint surfaces U-INV-2 specifically.
        self.assertLintFinds(
            build_passport(uncited=[e]),
            invariant="U-INV-2",
        )

    def test_u_inv_3_wrong_rule_version(self) -> None:
        e = uncited_assertion_entry()
        e["rule_version"] = "D4-c-v0"
        # Schema const rejects; lint surfaces U-INV-3 specifically.
        self.assertLintFinds(
            build_passport(uncited=[e]),
            invariant="U-INV-3",
        )

    def test_u_inv_4_orphan_manifest_pointer(self) -> None:
        # manifest_claim_id set without matching manifest entry -> U-INV-4
        e = uncited_assertion_entry()
        e["manifest_claim_id"] = "C-999"
        e["scoped_manifest_id"] = MANIFEST_ID
        self.assertLintFinds(
            build_passport(uncited=[e]),
            invariant="U-INV-4",
        )

    def test_u_inv_4_null_manifest_id_with_set_claim_id(self) -> None:
        # manifest_claim_id != null requires scoped_manifest_id != null.
        e = uncited_assertion_entry()
        e["manifest_claim_id"] = "C-001"
        e["scoped_manifest_id"] = None
        self.assertLintFinds(
            build_passport(uncited=[e]),
            invariant="U-INV-4",
        )


# ---------------------------------------------------------------------------
# T-S8: (judgment, audit_status, defect_stage) matrix exhaustive coverage.
# Spec §3.1 table: 9 positive rows, lint rejects every (j, a, d) triple
# outside the table; ≥5 disallowed combinations exercised explicitly.
# ---------------------------------------------------------------------------

class TS8AllowedMatrix(_LintTestBase):
    """T-S8: every allowed triple validates; ≥5 disallowed combinations rejected."""

    # Positive matrix rows — each is a self-contained passport fragment.
    ALLOWED_ROWS = [
        # (judgment, audit_status, defect_stage, ref_retrieval_method overrides)
        ("SUPPORTED", "completed", None, {"ref_retrieval_method": "api"}),
        ("AMBIGUOUS", "completed", "source_description", {"ref_retrieval_method": "api"}),
        ("AMBIGUOUS", "completed", "citation_anchor", {"ref_retrieval_method": "api"}),
        ("AMBIGUOUS", "completed", "synthesis_overclaim", {"ref_retrieval_method": "api"}),
        ("AMBIGUOUS", "completed", None, {"ref_retrieval_method": "api"}),
        ("UNSUPPORTED", "completed", "source_description", {"ref_retrieval_method": "api"}),
        ("UNSUPPORTED", "completed", "metadata", {"ref_retrieval_method": "api"}),
        ("UNSUPPORTED", "completed", "citation_anchor", {"ref_retrieval_method": "api"}),
        ("UNSUPPORTED", "completed", "synthesis_overclaim", {"ref_retrieval_method": "api"}),
        (
            "UNSUPPORTED",
            "completed",
            "negative_constraint_violation",
            {
                "ref_retrieval_method": "api",
                "violated_constraint_id": "MNC-1",
            },
        ),
        (
            "RETRIEVAL_FAILED",
            "completed",
            "retrieval_existence",
            {"ref_retrieval_method": "not_found"},
        ),
        (
            "RETRIEVAL_FAILED",
            "inconclusive",
            "not_applicable",
            {"ref_retrieval_method": "failed"},
        ),
    ]

    # Negative cases — ≥5 representative disallowed combinations.
    DISALLOWED_ROWS = [
        # (judgment, audit_status, defect_stage, overrides, expected_invariant)
        (
            "SUPPORTED",
            "completed",
            "source_description",
            {"ref_retrieval_method": "api"},
            "INV-1",
        ),
        (
            "UNSUPPORTED",
            "completed",
            None,
            {"ref_retrieval_method": "api"},
            "INV-2",
        ),
        (
            "RETRIEVAL_FAILED",
            "completed",
            "not_applicable",
            {"ref_retrieval_method": "api"},
            "matrix",
        ),
        (
            "SUPPORTED",
            "inconclusive",
            None,
            {"ref_retrieval_method": "api"},
            "matrix",
        ),
        (
            "AMBIGUOUS",
            "completed",
            "metadata",
            {"ref_retrieval_method": "api"},
            "INV-3",
        ),
        (
            "AMBIGUOUS",
            "inconclusive",
            None,
            {"ref_retrieval_method": "api"},
            "matrix",
        ),
    ]

    def _build_row(self, j: str, a: str, d: Any, overrides: dict[str, Any]) -> dict[str, Any]:
        e = supported_entry()
        e["judgment"] = j
        e["audit_status"] = a
        e["defect_stage"] = d
        if d == "negative_constraint_violation":
            e["rationale"] = "Violated declared negative constraint."
        elif d == "retrieval_existence":
            e["rationale"] = "Reference does not exist."
        elif d == "not_applicable":
            e["rationale"] = "Paywall — full text not retrievable."
        elif d is not None:
            e["rationale"] = f"Defect at {d}."
        e.update(overrides)
        return e

    def test_every_allowed_row_passes(self) -> None:
        for j, a, d, overrides in self.ALLOWED_ROWS:
            with self.subTest(judgment=j, audit_status=a, defect_stage=d):
                e = self._build_row(j, a, d, overrides)
                self.assertLintClean(
                    build_passport(results=[e]),
                    msg=f"row ({j}, {a}, {d}) should pass",
                )

    def test_disallowed_rows_rejected(self) -> None:
        for j, a, d, overrides, invariant in self.DISALLOWED_ROWS:
            with self.subTest(judgment=j, audit_status=a, defect_stage=d):
                e = self._build_row(j, a, d, overrides)
                self.assertLintFinds(
                    build_passport(results=[e]),
                    invariant=invariant,
                )


# ---------------------------------------------------------------------------
# Spec §6 lint 4a — D-INV-1..D-INV-4 claim_drift cross-array integrity.
# Not labelled T-Sx in spec §7.1 but mandatory per §6.4a. Paired pos/neg.
# ---------------------------------------------------------------------------

class TSDDriftInvariants(_LintTestBase):
    """Spec §6.4a: claim_drift D-INV-1..D-INV-4."""

    def test_d_baseline_emitted_not_intended(self) -> None:
        self.assertLintClean(build_passport(drifts=[claim_drift_entry()]))

    def test_d_baseline_intended_not_emitted(self) -> None:
        drift = claim_drift_entry(drift_kind="INTENDED_NOT_EMITTED")
        self.assertLintClean(build_passport(drifts=[drift]))

    def test_d_inv_1_duplicate_finding_id(self) -> None:
        a = claim_drift_entry()
        b = claim_drift_entry()  # CD-001 collides
        self.assertLintFinds(build_passport(drifts=[a, b]), invariant="D-INV-1")

    def test_d_inv_2_intended_not_emitted_missing_manifest_pointer(self) -> None:
        drift = claim_drift_entry(drift_kind="INTENDED_NOT_EMITTED")
        drift["manifest_claim_id"] = None  # MUST be non-null for INTENDED_NOT_EMITTED
        drift["scoped_manifest_id"] = None
        self.assertLintFinds(build_passport(drifts=[drift]), invariant="D-INV-2")

    def test_d_inv_2_emitted_not_intended_with_manifest_pointer(self) -> None:
        drift = claim_drift_entry(drift_kind="EMITTED_NOT_INTENDED")
        drift["manifest_claim_id"] = "C-001"  # MUST be null for EMITTED_NOT_INTENDED
        drift["scoped_manifest_id"] = MANIFEST_ID
        self.assertLintFinds(build_passport(drifts=[drift]), invariant="D-INV-2")

    def test_d_inv_2_dangling_intended_not_emitted_pair(self) -> None:
        drift = claim_drift_entry(drift_kind="INTENDED_NOT_EMITTED")
        drift["manifest_claim_id"] = "C-999"  # no such claim in manifest
        drift["scoped_manifest_id"] = MANIFEST_ID
        self.assertLintFinds(build_passport(drifts=[drift]), invariant="D-INV-2")

    def test_d_inv_3_wrong_rule_version(self) -> None:
        drift = claim_drift_entry()
        drift["rule_version"] = "D4-a-v0"
        self.assertLintFinds(build_passport(drifts=[drift]), invariant="D-INV-3")

    def test_d_inv_4_uncited_and_drift_collision(self) -> None:
        # A single sentence appears in both uncited_assertions[] and claim_drifts[].
        sentence = "Half of submissions showed positive results."
        uncited = uncited_assertion_entry()
        uncited["sentence_text"] = sentence
        drift = claim_drift_entry()
        drift["claim_text"] = sentence
        self.assertLintFinds(
            build_passport(uncited=[uncited], drifts=[drift]),
            invariant="D-INV-4",
        )


# ---------------------------------------------------------------------------
# Spec §6.4b — CV-INV-1..CV-INV-4 constraint_violation cross-array integrity.
# ---------------------------------------------------------------------------

class TSCVConstraintViolationInvariants(_LintTestBase):
    """Spec §6.4b: constraint_violation CV-INV-1..CV-INV-4."""

    def _manifest_with_mnc_and_nc(self) -> dict[str, Any]:
        return manifest_entry(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Causal claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {
                            "constraint_id": "NC-C001-1",
                            "rule": "No causal language without RCT.",
                        }
                    ],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "Global rule."}],
        )

    def test_cv_baseline_mnc_violation(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[constraint_violation_entry()],
        )
        self.assertLintClean(passport)

    def test_cv_baseline_nc_violation(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[
                constraint_violation_entry(
                    constraint_id="NC-C001-1",
                    manifest_claim_id="C-001",
                )
            ],
        )
        self.assertLintClean(passport)

    def test_cv_inv_1_duplicate_finding_id(self) -> None:
        a = constraint_violation_entry()
        b = constraint_violation_entry()
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[a, b],
        )
        self.assertLintFinds(passport, invariant="CV-INV-1")

    def test_cv_inv_2_dangling_mnc(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[constraint_violation_entry(constraint_id="MNC-99")],
        )
        self.assertLintFinds(passport, invariant="CV-INV-2")

    def test_cv_inv_2_dangling_nc(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[
                constraint_violation_entry(
                    constraint_id="NC-C999-1",
                    manifest_claim_id="C-999",
                )
            ],
        )
        self.assertLintFinds(passport, invariant="CV-INV-2")

    def test_cv_inv_3_mnc_with_set_manifest_claim_id(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[
                constraint_violation_entry(
                    constraint_id="MNC-1",
                    manifest_claim_id="C-001",  # MUST be null for MNC
                )
            ],
        )
        self.assertLintFinds(passport, invariant="CV-INV-3")

    def test_cv_inv_3_nc_polarity_mismatch(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[
                constraint_violation_entry(
                    constraint_id="NC-C001-1",
                    manifest_claim_id="C-002",  # MUST match the C-001 in NC id
                )
            ],
        )
        self.assertLintFinds(passport, invariant="CV-INV-3")

    def test_cv_inv_4_duplicate_per_constraint(self) -> None:
        # Two violations for (same sentence, same constraint) -> dedup rule.
        a = constraint_violation_entry()
        b = constraint_violation_entry()
        b["finding_id"] = "CV-002"  # avoid CV-INV-1 collision
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[a, b],
        )
        self.assertLintFinds(passport, invariant="CV-INV-4")


# ---------------------------------------------------------------------------
# Step 13 R8 codex P2-1 — CV-INV-4 dedupe key extension. Two manifests in
# the same passport can carry colliding MNC-* / NC-* ids; the same sentence
# text may legitimately violate both. The pre-fix dedupe key
# (section_path, claim_text_hash, violated_constraint_id) false-positives
# these as duplicates. Extend the key to scope by manifest_id as well.
# ---------------------------------------------------------------------------


class TSCVDedupeManifestScope(_LintTestBase):
    """T-SCV-DEDUPE: CV-INV-4 dedupe must scope by scoped_manifest_id."""

    def _two_manifests_with_colliding_mnc(self) -> list[dict[str, Any]]:
        # Two manifests each carrying the SAME constraint_id "MNC-1" but
        # bound to different manifests (M-INV-4 permits — manifest_id is
        # the joinable scope). Schema requires claims[] non-empty so we
        # add a minimal claim to each manifest; the claim itself is not
        # under test.
        return [
            manifest_entry(
                manifest_id=MANIFEST_ID,
                mncs=[{"constraint_id": "MNC-1", "rule": "No comparative claim."}],
            ),
            manifest_entry(
                manifest_id=MANIFEST_ID_OTHER,
                mncs=[{"constraint_id": "MNC-1", "rule": "No temporal claim."}],
            ),
        ]

    def test_same_constraint_id_across_manifests_not_deduped(self) -> None:
        # Two CV rows on the same sentence text + same constraint_id (MNC-1)
        # but DIFFERENT scoped_manifest_id. Legitimate per M-INV-4 +
        # manifest_negative_constraints scoping — dedupe must keep both.
        a = constraint_violation_entry(constraint_id="MNC-1")
        a["scoped_manifest_id"] = MANIFEST_ID
        b = constraint_violation_entry(constraint_id="MNC-1")
        b["finding_id"] = "CV-002"
        b["scoped_manifest_id"] = MANIFEST_ID_OTHER
        passport = build_passport(
            manifests=self._two_manifests_with_colliding_mnc(),
            violations=[a, b],
        )
        # Pre-fix: CV-INV-4 false-positives → lint reports CV-INV-4 line.
        # Post-fix: lint MUST NOT fire CV-INV-4 on cross-manifest collision.
        self.assertLintClean(passport)

    def test_same_constraint_id_same_manifest_still_deduped(self) -> None:
        # Negative test: dedupe still catches true within-manifest duplicates.
        a = constraint_violation_entry(constraint_id="MNC-1")
        b = constraint_violation_entry(constraint_id="MNC-1")
        b["finding_id"] = "CV-002"
        # Both rows reference the same manifest_id (default MANIFEST_ID).
        passport = build_passport(
            manifests=[self._two_manifests_with_colliding_mnc()[0]],  # single manifest
            violations=[a, b],
        )
        self.assertLintFinds(passport, invariant="CV-INV-4")


# ---------------------------------------------------------------------------
# Spec §6.4c — S-INV-1..S-INV-4 audit_sampling_summary invariants.
# ---------------------------------------------------------------------------

class TSSamplingInvariants(_LintTestBase):
    """Spec §6.4c: audit_sampling_summary S-INV-1..S-INV-4."""

    def test_s_baseline(self) -> None:
        self.assertLintClean(build_passport(samplings=[sampling_summary_entry()]))

    def test_s_inv_1_count_vs_indices_mismatch(self) -> None:
        e = sampling_summary_entry()
        e["audited_count"] = e["audited_count"] - 1  # off-by-one
        self.assertLintFinds(build_passport(samplings=[e]), invariant="S-INV-1")

    def test_s_inv_2_count_exceeds_cap(self) -> None:
        e = sampling_summary_entry(total=50, cap=10)
        e["audited_count"] = 20
        e["audited_indices"] = list(range(20))
        self.assertLintFinds(build_passport(samplings=[e]), invariant="S-INV-2")

    def test_s_inv_2_count_exceeds_total(self) -> None:
        e = sampling_summary_entry(total=10, cap=100)
        e["audited_count"] = 20
        e["audited_indices"] = list(range(20))
        self.assertLintFinds(build_passport(samplings=[e]), invariant="S-INV-2")

    def test_s_inv_4_non_ascending_indices(self) -> None:
        e = sampling_summary_entry(total=20, cap=10)
        e["audited_indices"] = [5, 3, 7, 9, 11, 13, 15, 17, 19, 2]
        e["audited_count"] = 10
        self.assertLintFinds(build_passport(samplings=[e]), invariant="S-INV-4")

    def test_s_inv_4_duplicate_indices(self) -> None:
        e = sampling_summary_entry(total=20, cap=10)
        e["audited_indices"] = [0, 1, 1, 3, 4, 5, 6, 7, 8, 9]
        e["audited_count"] = 10
        self.assertLintFinds(build_passport(samplings=[e]), invariant="S-INV-4")


# ---------------------------------------------------------------------------
# Spec §6.4d (v3.8.2 / #118) — UAF-INV-1..UAF-INV-5 uncited_audit_failure
# cross-array integrity and dedup. Mirrors CV-INV pattern.
# ---------------------------------------------------------------------------


class TSUAFUncitedAuditFailureInvariants(_LintTestBase):
    """Spec §6.4d: uncited_audit_failure UAF-INV-1..UAF-INV-5 (v3.8.2 / #118)."""

    def _manifest_with_mnc_and_nc(self) -> dict[str, Any]:
        return manifest_entry(
            claims=[
                {
                    "claim_id": "C-001",
                    "claim_text": "Causal claim.",
                    "intended_evidence_kind": "empirical",
                    "planned_refs": [],
                    "negative_constraints": [
                        {
                            "constraint_id": "NC-C001-1",
                            "rule": "No causal language without RCT.",
                        }
                    ],
                }
            ],
            mncs=[{"constraint_id": "MNC-1", "rule": "Global rule."}],
        )

    # ----- Schema-shape only.
    def test_uaf_schema_valid_minimal_entry(self) -> None:
        schema = load_json_schema(SCHEMA_PATHS["uncited_audit_failure"])
        validator = build_schema_validator(schema)
        errors = list(validator.iter_errors(uncited_audit_failure_entry()))
        self.assertEqual(errors, [], msg=f"unexpected validation errors: {errors}")

    def test_uaf_schema_fault_class_enum_matches_constants(self) -> None:
        """The schema's fault_class enum MUST match INV14_FAULT_CLASS_TAGS exactly.

        Without this guard, extending INV14_FAULT_CLASS_TAGS in the Python
        constants module would silently produce UAF rows that fail schema
        validation (the pipeline maps a new exception class to a new tag,
        but the schema's closed enum hasn't been bumped). Per Gemini cross-
        model review R2 P2 (2026-05-17): both surfaces must move together,
        and a rule_version bump (D4-c-v1-uaf-v2 or later) should accompany
        any enum extension.
        """
        from scripts._claim_audit_constants import INV14_FAULT_CLASS_TAGS

        schema = load_json_schema(SCHEMA_PATHS["uncited_audit_failure"])
        schema_enum = set(schema["properties"]["fault_class"]["enum"])
        constants_set = set(INV14_FAULT_CLASS_TAGS)
        self.assertEqual(
            schema_enum,
            constants_set,
            msg=(
                "uncited_audit_failure.schema.json `fault_class` enum drifted "
                "from INV14_FAULT_CLASS_TAGS. Either align the schema with the "
                "python constant, or if intentionally extending the taxonomy "
                "bump `rule_version` (e.g., D4-c-v1-uaf-v2) and document the "
                "ramp in spec §3.6."
            ),
        )

    def test_uaf_schema_rejects_missing_fault_class(self) -> None:
        schema = load_json_schema(SCHEMA_PATHS["uncited_audit_failure"])
        validator = build_schema_validator(schema)
        e = uncited_audit_failure_entry()
        del e["fault_class"]
        errors = list(validator.iter_errors(e))
        self.assertNotEqual(errors, [], msg="missing fault_class must fail schema validation")

    def test_uaf_schema_rejects_unknown_fault_class(self) -> None:
        schema = load_json_schema(SCHEMA_PATHS["uncited_audit_failure"])
        validator = build_schema_validator(schema)
        e = uncited_audit_failure_entry()
        e["fault_class"] = "made_up_class"
        errors = list(validator.iter_errors(e))
        self.assertNotEqual(errors, [], msg="unknown fault_class must fail schema validation")

    # ----- Lint baseline: clean passport with one UAF row passes.
    def test_uaf_baseline_mnc_failure(self) -> None:
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[uncited_audit_failure_entry()],
        )
        self.assertLintClean(passport)

    def test_uaf_baseline_nc_failure(self) -> None:
        # NC-C path: judge failed on a claim-level constraint check; manifest_claim_id set.
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[uncited_audit_failure_entry(manifest_claim_id="C-001")],
        )
        self.assertLintClean(passport)

    # ----- UAF-INV-1: finding_id uniqueness.
    def test_uaf_inv_1_duplicate_finding_id(self) -> None:
        a = uncited_audit_failure_entry()
        b = uncited_audit_failure_entry()  # same finding_id "UAF-001"
        # Per Gemini cross-model review P2 (2026-05-17): keep this test
        # isolated to UAF-INV-1 by giving b a different claim_text so the
        # passport does NOT simultaneously trip UAF-INV-4 (per-(sentence,
        # manifest) dedup). One test should target one invariant cleanly.
        b["claim_text"] = "Different text so UAF-INV-4 dedup does not fire."
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[a, b],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-1")

    # ----- UAF-INV-2: scoped_manifest_id must resolve in claim_intent_manifests[].
    def test_uaf_inv_2_dangling_manifest_id(self) -> None:
        e = uncited_audit_failure_entry()
        e["scoped_manifest_id"] = SENTINEL_MANIFEST_ID  # not in manifests
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[e],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-2")

    # ----- UAF-INV-3: (scoped_manifest_id, manifest_claim_id) pair integrity.
    def test_uaf_inv_3_dangling_claim_id(self) -> None:
        e = uncited_audit_failure_entry(manifest_claim_id="C-999")  # no such claim in manifest
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[e],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-3")

    def test_uaf_inv_3_null_claim_id_allowed_when_mnc_only(self) -> None:
        # manifest_claim_id=null is legitimate when the failure was against MNCs only.
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[uncited_audit_failure_entry(manifest_claim_id=None)],
        )
        self.assertLintClean(passport)

    # ----- UAF-INV-4: per-(sentence, manifest) dedup.
    def test_uaf_inv_4_same_sentence_same_manifest_dup(self) -> None:
        a = uncited_audit_failure_entry()
        b = uncited_audit_failure_entry(finding_id="UAF-002")
        # b shares (scoped_manifest_id, section_path, claim_text) with a.
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[a, b],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-4")

    def test_uaf_inv_4_same_sentence_different_manifests_not_deduped(self) -> None:
        # Two manifests both failing on the same sentence text emit two rows
        # legitimately (mirrors CV-INV-4 cross-manifest reasoning).
        other_manifest = manifest_entry(
            manifest_id=MANIFEST_ID_OTHER,
            mncs=[{"constraint_id": "MNC-1", "rule": "Different rule."}],
        )
        a = uncited_audit_failure_entry()
        a["scoped_manifest_id"] = MANIFEST_ID
        b = uncited_audit_failure_entry(finding_id="UAF-002")
        b["scoped_manifest_id"] = MANIFEST_ID_OTHER
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc(), other_manifest],
            uaf=[a, b],
        )
        self.assertLintClean(passport)

    # ----- UAF-INV-5: rationale fault_class prefix.
    def test_uaf_inv_5_rationale_missing_fault_prefix(self) -> None:
        e = uncited_audit_failure_entry()
        e["rationale"] = "Some narrative without the fault_class prefix"
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[e],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-5")

    def test_uaf_inv_5_rationale_wrong_fault_prefix(self) -> None:
        # Rationale starts with "made_up_class:" — schema rejected via fault_class
        # enum, but UAF-INV-5 also flags rationale prefix mismatch independently.
        # Here we keep fault_class valid but flip rationale to a different valid
        # tag — should still trip UAF-INV-5 (prefix must match the row's
        # fault_class, not just any known tag).
        e = uncited_audit_failure_entry(fault_class="judge_timeout")
        e["rationale"] = "judge_api_error: wrong tag for this row"
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[e],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-5")

    # ----- Cross-aggregate exclusivity: UAF vs constraint_violation.
    def test_uaf_cross_aggregate_exclusive_with_cv(self) -> None:
        # Same (sentence, manifest) MUST NOT have both an audit_tool_failure (UAF)
        # and a VIOLATED row (CV). They are mutually exclusive verdict states.
        cv = constraint_violation_entry()
        uaf = uncited_audit_failure_entry()
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            violations=[cv],
            uaf=[uaf],
        )
        self.assertLintFinds(passport, invariant="UAF-INV-6")

    # ----- Malformed-payload hardening (Codex R2 P2-2 + P2-3, 2026-05-17).
    def test_uaf_malformed_manifest_claim_id_does_not_crash_lint(self) -> None:
        # Schema validator flags type errors separately; lint walker must
        # skip cleanly on unhashable values rather than raise TypeError.
        e = uncited_audit_failure_entry()
        e["manifest_claim_id"] = ["unhashable", "list", "as", "claim_id"]
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[e],
        )
        # Lint should report SOMETHING (schema-shape finding), exit 1, NOT crash.
        path = write_passport(self.tmp, passport)
        code, _, err = run_lint(path)
        self.assertEqual(
            code,
            1,
            msg=f"expected clean lint failure on malformed manifest_claim_id, got exit={code}\nstderr:\n{err}",
        )
        self.assertNotIn(
            "Traceback",
            err,
            msg="lint MUST NOT crash with a traceback on malformed manifest_claim_id (Codex R2 P2-2)",
        )

    def test_uaf_malformed_rationale_does_not_crash_lint(self) -> None:
        e = uncited_audit_failure_entry()
        e["rationale"] = ["unhashable", "rationale"]
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uaf=[e],
        )
        path = write_passport(self.tmp, passport)
        code, _, err = run_lint(path)
        self.assertEqual(
            code,
            1,
            msg=f"expected clean lint failure on malformed rationale, got exit={code}\nstderr:\n{err}",
        )
        self.assertNotIn(
            "Traceback",
            err,
            msg="lint MUST NOT crash with a traceback on malformed rationale (Codex R2 P2-3)",
        )

    # ----- Co-existence with uncited_assertions[] IS permitted.
    def test_uaf_coexists_with_uncited_assertion(self) -> None:
        # D4-c detector positive (UA) + judge failure (UAF) on the same sentence
        # are independent signals; cross-aggregate exclusivity does NOT apply.
        ua = uncited_assertion_entry()
        uaf = uncited_audit_failure_entry()
        passport = build_passport(
            manifests=[self._manifest_with_mnc_and_nc()],
            uncited=[ua],
            uaf=[uaf],
        )
        self.assertLintClean(passport)


# ---------------------------------------------------------------------------
# T-S9: Defensive guard against malformed passports.
# Step 13 R4 codex P2 #4 — malformed aggregates (non-list / non-dict entries)
# must surface as schema findings rather than crash the lint with an
# AttributeError traceback.
# ---------------------------------------------------------------------------


class TS9MalformedPassportGuard(_LintTestBase):
    """T-S9: passport with malformed aggregate yields schema finding, not crash."""

    def test_claim_audit_results_with_non_dict_entry(self) -> None:
        # Pre-R4: list of non-dict in claim_audit_results raised AttributeError
        # because dict-only invariant loops ran .get() before noticing the shape.
        body = build_passport()
        body["claim_audit_results"] = ["this should be an object, not a string"]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(
            code,
            1,
            msg=f"expected clean lint failure on malformed aggregate; got exit={code}\nstderr:\n{err}",
        )
        self.assertNotIn(
            "Traceback",
            err,
            msg=f"lint must not raise — got traceback:\n{err}",
        )
        self.assertIn("schema", out, msg=f"expected schema finding tag in stdout:\n{out}")

    def test_claim_intent_manifests_as_dict_instead_of_list(self) -> None:
        body = build_passport()
        body["claim_intent_manifests"] = {"oops": "should be a list"}
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not raise:\n{err}")
        self.assertIn("schema", out)

    def test_non_object_passport_body_yields_clean_finding(self) -> None:
        # Step 13 R7 codex P3: `[]`, `null`, scalar top-level JSON would
        # previously crash with AttributeError on `.get()`. Validate that
        # each surfaces as a schema finding without traceback.
        for malformed_body in ([], None, 42, "passport"):
            with self.subTest(body=malformed_body):
                path = self.tmp / f"malformed_{type(malformed_body).__name__}.json"
                path.write_text(json.dumps(malformed_body), encoding="utf-8")
                code, out, err = run_lint(path)
                self.assertEqual(
                    code,
                    1,
                    msg=f"expected exit=1 for body={malformed_body!r}; got {code}\nstderr:\n{err}",
                )
                self.assertNotIn(
                    "Traceback",
                    err,
                    msg=f"lint must not raise for body={malformed_body!r}:\n{err}",
                )
                self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_falsey_malformed_aggregate_does_not_bypass_schema(self) -> None:
        # Step 13 R5 codex P2 #1: `body.get(k, []) or []` would silently
        # convert a malformed `{}` / `null` / `0` / `""` value to an empty
        # list and skip schema validation. Each falsey-but-malformed shape
        # must surface as a schema finding.
        for malformed in ({}, None, 0, ""):
            with self.subTest(malformed=malformed):
                body = build_passport()
                body["claim_audit_results"] = malformed
                path = write_passport(self.tmp, body)
                code, out, err = run_lint(path)
                self.assertEqual(
                    code,
                    1,
                    msg=f"expected exit=1 for malformed={malformed!r}; got {code}\nstdout:\n{out}\nstderr:\n{err}",
                )
                self.assertIn("schema", out, msg=f"expected schema finding for malformed={malformed!r}:\n{out}")
                self.assertNotIn("Traceback", err, msg=f"lint must not raise for malformed={malformed!r}:\n{err}")

    # Step 13 R6 codex P2 + R8 P2-2 — nested schema-invalid shapes must not
    # crash the cross-field invariant walkers. Schema validator records the
    # finding; the invariant helpers then iterate the malformed nested shape
    # and previously hit TypeError/AttributeError. Issue #119 + #120 P2-2.

    def test_manifest_claims_as_string_does_not_crash_invariant_walker(self) -> None:
        # #119 + #120 P2-2: claim_intent_manifests[0].claims is a string,
        # not a list. Schema validator records the finding; the cross-field
        # invariant walker (M-INV-1..M-INV-4) must NOT iterate the string
        # and crash. Expect clean exit=1 with schema finding, no traceback.
        body = build_passport()
        body["claim_intent_manifests"][0]["claims"] = "should be a list"
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on nested string:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_manifest_claim_with_non_string_claim_id_does_not_crash(self) -> None:
        # #119: manifest.claims[].claim_id is a non-string. Schema records
        # the type mismatch; invariant walker must skip this manifest's
        # cross-field checks instead of crashing on .get() / regex match.
        body = build_passport()
        body["claim_intent_manifests"][0]["claims"][0]["claim_id"] = 42
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on non-string claim_id:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_audited_indices_mixed_types_does_not_crash_sampling_walker(self) -> None:
        # #119: audit_sampling_summaries[].audited_indices contains mixed
        # str/int types. Schema records the type mismatch; S-INV-4 walker
        # (indices[i] <= indices[i-1]) must skip instead of raising
        # TypeError on '<=' between str and int.
        body = build_passport()
        body["audit_sampling_summaries"] = [{
            "audit_run_id": AUDIT_RUN_ID,
            "max_claims_per_paper": 10,
            "total_citation_count": 5,
            "audited_count": 2,
            "audited_indices": ["a", 1],
            "sampling_strategy": "stratified_buckets_v1",
            "emitted_at": "2026-05-15T10:15:00Z",
        }]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on mixed-type indices:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    # v3.8.1 Round 2 codex review P2 + adjacent unhashable-id surfaces.
    # Schema validator records the type mismatch separately; uniqueness loops
    # and dedupe key construction must not crash on unhashable nested ids.

    def test_unhashable_claim_id_does_not_crash_m_inv_1(self) -> None:
        # codex round 2 P2: claim.get("claim_id") returns a list/dict
        # (unhashable). M-INV-1 uniqueness `cid in claim_ids` crashes with
        # TypeError. Schema records the type mismatch but the invariant walker
        # still raises, masking the schema findings.
        body = build_passport()
        body["claim_intent_manifests"][0]["claims"][0]["claim_id"] = ["bad", "type"]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on unhashable claim_id:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_unhashable_finding_id_does_not_crash_cv_inv_1(self) -> None:
        # CV-INV-1 finding_id uniqueness `fid in seen` crashes when finding_id
        # is a list / dict (schema-invalid). Same surface class as the M-INV-1
        # case codex flagged; included for parity coverage across all four
        # finding_id uniqueness sites (M-INV-4 / U-INV-1 / D-INV-1 / CV-INV-1).
        body = build_passport()
        body["constraint_violations"] = [
            {
                "finding_id": ["unhashable"],
                "claim_text": "x",
                "section_path": "Results > Findings",
                "violated_constraint_id": "MNC-1",
                "scoped_manifest_id": MANIFEST_ID,
                "manifest_claim_id": None,
                "judge_verdict": "VIOLATED",
                "rationale": "rationale",
                "judge_model": "gpt-5.5-xhigh",
                "judge_run_at": "2026-05-15T10:14:00Z",
                "rule_version": "D4-a-v1",
            }
        ]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on unhashable finding_id:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_unhashable_mnc_constraint_id_does_not_crash_m_inv_3(self) -> None:
        # codex round 3 P2: manifest_negative_constraints[].constraint_id as
        # list/dict crashes the `mnc_ids = {nc.get("constraint_id") for ...}`
        # set comprehension when the implementation builds an (unused) set.
        # Schema records the type mismatch but the lint still raises.
        body = build_passport()
        body["claim_intent_manifests"][0]["manifest_negative_constraints"] = [
            {"constraint_id": ["unhashable"], "rule": "bad"}
        ]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on unhashable MNC constraint_id:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_non_string_claim_text_does_not_crash_cv_inv_4_dedupe(self) -> None:
        # CV-INV-4 dedupe key constructs hashlib.sha256((claim_text or "").encode())
        # — if claim_text is a list / dict / int (schema-invalid), the `or ""`
        # idiom passes the non-string through and .encode() raises AttributeError.
        # Codex round 2 adversarial probing surfaced this same class.
        body = build_passport()
        body["constraint_violations"] = [
            {
                "finding_id": "CV-001",
                "claim_text": ["not", "a", "string"],
                "section_path": "Results > Findings",
                "violated_constraint_id": "MNC-1",
                "scoped_manifest_id": MANIFEST_ID,
                "manifest_claim_id": None,
                "judge_verdict": "VIOLATED",
                "rationale": "rationale",
                "judge_model": "gpt-5.5-xhigh",
                "judge_run_at": "2026-05-15T10:14:00Z",
                "rule_version": "D4-a-v1",
            }
        ]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn("Traceback", err, msg=f"lint must not crash on non-string claim_text:\n{err}")
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")


# v3.9.1 / #130 — manifest_id non-string guard in _build_manifest_index +
# _build_manifest_constraint_index. Schema validator records the type
# mismatch finding; the index builders must skip non-string IDs cleanly
# instead of raising TypeError("unhashable type") on setdefault() / [mid]=.
class TSManifestIdNonStringGuard(_LintTestBase):
    """Issue #130: manifest_id of type list/dict must not crash index builders."""

    def test_manifest_id_as_list_does_not_crash(self) -> None:
        body = build_passport()
        body["claim_intent_manifests"][0]["manifest_id"] = ["oops"]
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn(
            "Traceback",
            err,
            msg=f"lint must not crash on list manifest_id (unhashable in setdefault):\n{err}",
        )
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")

    def test_manifest_id_as_dict_does_not_crash(self) -> None:
        body = build_passport()
        body["claim_intent_manifests"][0]["manifest_id"] = {"oops": "dict id"}
        path = write_passport(self.tmp, body)
        code, out, err = run_lint(path)
        self.assertEqual(code, 1, msg=f"expected exit=1; got {code}\nstderr:\n{err}")
        self.assertNotIn(
            "Traceback",
            err,
            msg=f"lint must not crash on dict manifest_id (unhashable in setdefault):\n{err}",
        )
        self.assertIn("schema", out, msg=f"expected schema finding:\n{out}")


if __name__ == "__main__":
    unittest.main()
