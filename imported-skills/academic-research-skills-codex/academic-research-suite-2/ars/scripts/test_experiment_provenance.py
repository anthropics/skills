"""Tests for #260 Experiment Provenance Intake + claim->experiment alignment.

Covers the two new schemas, the seven new cross-array invariants
(EP-INV-1..5 / EA-INV-1..2 in check_claim_audit_consistency.py), the
fail-closed legacy-boundary symmetry, mixed-evidence two-row handling, the
verdict-derivation rules (schema + agent-prompt level), a mutation pass proving
each new invariant is load-bearing, reverse-invariant pins on the writer/intake
producers, and example + literature-only regressions.

Spec: docs/design/2026-06-08-260-experiment-provenance-intake-spec.md
(§"Test strategy", D4-D7).

Layering note (open question flagged for ship-gate review): the fail-closed
legacy boundary has TWO halves with different enforcement layers —
  * the DECLARATION<->PROVENANCE SYMMETRY half (EP-INV-4) is deterministic and
    lives in the lint; it is tested here against validate_passport.
  * the ARS_VERSION numeric legacy gate (repro_lock.ars_version < #260 const =>
    legacy_unknown advisory; everything else treated-as-post-#260 => declaration
    REQUIRED) is described in integrity_verification_agent.md (D7) as a gate
    HEURISTIC anchored on the version constant, NOT a deterministic lint check.
    The lint does NOT compare ars_version numerically. We therefore test the
    prose-layer existence of that boundary (the agent prompt carries the rule)
    rather than asserting a numeric lint verdict that does not exist. Whether
    the ars_version gate should be promoted into a deterministic lint is left to
    the ship-gate codex consult.

Run:
    python -m unittest scripts.test_experiment_provenance -v
    pytest scripts/test_experiment_provenance.py
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path
from typing import Any

import yaml

from tests.test_helpers import build_schema_validator, load_json_schema, run_script

REPO = Path(__file__).resolve().parent.parent
PASSPORT = REPO / "shared/contracts/passport"
LINT = REPO / "scripts/check_claim_audit_consistency.py"
SHAPE_VALIDATOR = REPO / "scripts/check_experiment_provenance.py"
EXAMPLE = REPO / "examples/passport_with_experiment_provenance.yaml"

# Import the lint module once at module level (the dual-path insert handles the
# CLI-vs-unittest sys.path gap). MutationTests monkeypatches attributes on this
# object, so both the in-process _validate() driver and the mutation tests share
# the same module reference.
sys.path.insert(0, str(REPO / "scripts"))
import check_claim_audit_consistency as _lint  # noqa: E402

PROVENANCE_SCHEMA = PASSPORT / "experiment_provenance_entry.schema.json"
ALIGNMENT_SCHEMA = PASSPORT / "experiment_alignment_result.schema.json"
MANIFEST_SCHEMA = PASSPORT / "claim_intent_manifest.schema.json"

# Agent / writer prompts touched by #260.
INTEGRITY_AGENT = REPO / "academic-pipeline/agents/integrity_verification_agent.md"
WRITER_PROMPTS = {
    "synthesis_agent": REPO / "deep-research/agents/synthesis_agent.md",
    "draft_writer_agent": REPO / "academic-paper/agents/draft_writer_agent.md",
    "report_compiler_agent": REPO / "deep-research/agents/report_compiler_agent.md",
}

MANIFEST_ID = "M-2026-06-08T09:10:00Z-1a2b"


# ---------------------------------------------------------------------------
# Fixture builders. Each returns a fresh dict so a test can mutate one field
# without leaking to siblings.
# ---------------------------------------------------------------------------


def repro_lock_block() -> dict[str, Any]:
    """A well-formed nested repro_lock matching the canonical field set."""
    return {
        "schema_version": "1.0",
        "stochasticity_declaration": "Configuration lock, not a replay guarantee.",
        "ars_version": "3.11.1",
        "model": {"family": "custom", "id": "encoder-v2", "weight_stable": True},
        "prompts": {
            "hash_timing": "skill-load",
            "skill_md_hash": "sha256:" + "a" * 60,
            "agents_bundle_hash": "sha256:" + "b" * 60,
        },
        "materials": {"list_hash": "sha256:" + "c" * 60, "count": 3},
        "external_protocols": {
            "s2_api_protocol_version": "3.11",
            "s2_snapshot_available": False,
        },
        "cross_model": {"enabled": False, "secondary_model_id": None},
    }


def provenance_entry(experiment_id: str = "exp-pruning") -> dict[str, Any]:
    """A well-formed experiment_provenance[] entry."""
    return {
        "experiment_id": experiment_id,
        "title": f"Experiment {experiment_id}",
        "repro_lock": repro_lock_block(),
        "planned_vs_executed": [
            {
                "planned": "macro-F1 on held-out test set",
                "executed": True,
                "result_file": f"results/{experiment_id}/metrics.json",
                "metric": "macro-F1",
                "value": 0.81,
            }
        ],
        "negative_results": [],
        "known_limitations": [],
    }


def alignment_entry(
    *,
    finding_id: str = "EA-001",
    claim_id: str = "C-001",
    experiment_id: str = "exp-pruning",
    verdict: str = "ALIGNED",
) -> dict[str, Any]:
    """A well-formed experiment_alignment_results[] entry."""
    return {
        "finding_id": finding_id,
        "scoped_manifest_id": MANIFEST_ID,
        "claim_id": claim_id,
        "claim_text": "Removing pruning lowers macro-F1 by 4.2 points.",
        "experiment_id": experiment_id,
        "result_pointer": f"results/{experiment_id}/metrics.json#macro-F1",
        "manuscript_locator": "4. Results > 4.2 Ablations",
        "alignment_verdict": verdict,
        "rationale": "The reported drop matches the claim.",
        "judge_model": "gpt-5.5-xhigh",
        "judge_run_at": "2026-06-08T09:20:00Z",
        "rule_version": "EA-v1",
    }


def claim(
    *,
    claim_id: str = "C-001",
    kind: str = "empirical",
    planned_refs: list[str] | None = None,
    planned_experiment_ids: list[str] | None = None,
) -> dict[str, Any]:
    c: dict[str, Any] = {
        "claim_id": claim_id,
        "claim_text": f"Claim {claim_id} text.",
        "intended_evidence_kind": kind,
        "planned_refs": planned_refs if planned_refs is not None else [],
    }
    if planned_experiment_ids is not None:
        c["planned_experiment_ids"] = planned_experiment_ids
    return c


def manifest(claims: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    return {
        "manifest_version": "1.0",
        "manifest_id": MANIFEST_ID,
        "emitted_by": "draft_writer_agent",
        "emitted_at": "2026-06-08T09:10:00Z",
        "claims": claims if claims is not None else [claim()],
        "manifest_negative_constraints": [],
    }


def declaration(status: str = "experiments_declared") -> dict[str, Any]:
    return {
        "status": status,
        "declared_at": "2026-06-08T09:05:00Z",
        "declared_by": "scholar",
    }


# Sentinel distinguishing "intake_declaration omitted" (insert the default
# declaration) from an explicit None (omit the key — legacy-passport tests).
_MISSING = object()


def build_passport(
    *,
    manifests: list[dict[str, Any]] | None = None,
    provenance: list[dict[str, Any]] | None = None,
    alignment: list[dict[str, Any]] | None = None,
    intake_declaration: Any = _MISSING,
) -> dict[str, Any]:
    """Minimal passport carrying the #260 aggregates the lint reads.

    A standard happy-path passport: one manifest with one experiment-backed
    claim, one provenance entry, an experiments_declared declaration.
    """
    body: dict[str, Any] = {
        "claim_intent_manifests": manifests
        if manifests is not None
        else [manifest([claim(planned_experiment_ids=["exp-pruning"])])],
        "claim_audit_results": [],
        "uncited_assertions": [],
        "claim_drifts": [],
        "constraint_violations": [],
        "audit_sampling_summaries": [],
        "uncited_audit_failures": [],
        "experiment_provenance": provenance
        if provenance is not None
        else [provenance_entry()],
        "experiment_alignment_results": alignment or [],
    }
    if intake_declaration is _MISSING:
        body["experiment_intake_declaration"] = declaration()
    elif intake_declaration is not None:
        body["experiment_intake_declaration"] = intake_declaration
    return body


# ---------------------------------------------------------------------------
# Lint driver. Reuses check_claim_audit_consistency.validate_passport directly
# (in-process) — faster than the subprocess and gives us the Finding objects.
# ---------------------------------------------------------------------------


def _validate(body: dict[str, Any]) -> list[str]:
    """Run the lint in-process; return rendered finding strings."""
    return [f.render() for f in _lint.validate_passport(body)]


def _invariant_tags(findings: list[str]) -> set[str]:
    """Extract the leading invariant tag from each rendered finding."""
    return {f.split(":", 1)[0] for f in findings}


class _LintBase(unittest.TestCase):
    def assertClean(self, body: dict[str, Any], msg: str = "") -> None:
        findings = _validate(body)
        self.assertEqual(findings, [], msg=msg + "\n" + "\n".join(findings))

    def assertFinds(self, body: dict[str, Any], invariant: str) -> list[str]:
        findings = _validate(body)
        self.assertIn(
            invariant,
            _invariant_tags(findings),
            msg=f"expected {invariant}; got findings:\n" + "\n".join(findings),
        )
        return findings


# ===========================================================================
# 1. Schema positive / negative.
# ===========================================================================


class SchemaTests(unittest.TestCase):
    def test_schemas_parse_as_draft_2020_12(self) -> None:
        for path in (PROVENANCE_SCHEMA, ALIGNMENT_SCHEMA, MANIFEST_SCHEMA):
            with self.subTest(schema=path.name):
                load_json_schema(path)

    def test_provenance_entry_positive(self) -> None:
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        errors = list(v.iter_errors(provenance_entry()))
        self.assertEqual(errors, [], msg=f"{errors}")

    def test_alignment_entry_positive(self) -> None:
        v = build_schema_validator(load_json_schema(ALIGNMENT_SCHEMA))
        errors = list(v.iter_errors(alignment_entry()))
        self.assertEqual(errors, [], msg=f"{errors}")

    def test_provenance_missing_required_key_fails(self) -> None:
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        entry = provenance_entry()
        del entry["repro_lock"]
        errors = list(v.iter_errors(entry))
        self.assertNotEqual(errors, [], msg="missing repro_lock should fail")

    def test_provenance_absent_negative_results_key_is_malformed(self) -> None:
        """D6 check-0 absent-key rule: the negative_results KEY must be present."""
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        entry = provenance_entry()
        del entry["negative_results"]
        errors = list(v.iter_errors(entry))
        self.assertNotEqual(errors, [], msg="absent negative_results key is malformed")

    def test_provenance_empty_negative_results_is_well_formed(self) -> None:
        """An empty [] is well-formed (routes to the check-4 advisory, not malformed)."""
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        entry = provenance_entry()
        entry["negative_results"] = []
        entry["known_limitations"] = []
        errors = list(v.iter_errors(entry))
        self.assertEqual(errors, [], msg=f"empty [] should be well-formed: {errors}")

    def test_provenance_absent_known_limitations_key_is_malformed(self) -> None:
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        entry = provenance_entry()
        del entry["known_limitations"]
        errors = list(v.iter_errors(entry))
        self.assertNotEqual(errors, [], msg="absent known_limitations key is malformed")

    def test_planned_vs_executed_minitems_1(self) -> None:
        """A provenance entry with empty planned_vs_executed is degenerate (minItems 1)."""
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        entry = provenance_entry()
        entry["planned_vs_executed"] = []
        errors = list(v.iter_errors(entry))
        self.assertNotEqual(errors, [], msg="empty planned_vs_executed should fail minItems")

    def test_alignment_provenance_missing_not_a_verdict(self) -> None:
        """PROVENANCE_MISSING is deliberately NOT in the verdict enum (D4)."""
        v = build_schema_validator(load_json_schema(ALIGNMENT_SCHEMA))
        entry = alignment_entry(verdict="PROVENANCE_MISSING")
        errors = list(v.iter_errors(entry))
        self.assertTrue(
            any(e.validator == "enum" for e in errors),
            msg=f"PROVENANCE_MISSING must be rejected by the verdict enum; got {[e.validator for e in errors]}",
        )

    def test_alignment_finding_id_pattern(self) -> None:
        v = build_schema_validator(load_json_schema(ALIGNMENT_SCHEMA))
        entry = alignment_entry(finding_id="UA-001")  # wrong prefix
        errors = list(v.iter_errors(entry))
        self.assertTrue(
            any(e.validator == "pattern" for e in errors),
            msg="finding_id must match ^EA-[0-9]{3,}$",
        )

    def test_manifest_planned_experiment_ids_optional(self) -> None:
        """planned_experiment_ids is optional-absent; a claim without it validates."""
        v = build_schema_validator(load_json_schema(MANIFEST_SCHEMA))
        errors = list(v.iter_errors(manifest([claim()])))
        self.assertEqual(errors, [], msg=f"{errors}")

    def test_manifest_planned_experiment_ids_minitems_1(self) -> None:
        """When present, planned_experiment_ids must be minItems 1 (omit the field, not [])."""
        v = build_schema_validator(load_json_schema(MANIFEST_SCHEMA))
        m = manifest([claim(planned_experiment_ids=[])])
        errors = list(v.iter_errors(m))
        self.assertNotEqual(errors, [], msg="empty planned_experiment_ids should fail minItems")

    def test_manifest_planned_experiment_ids_unique(self) -> None:
        v = build_schema_validator(load_json_schema(MANIFEST_SCHEMA))
        m = manifest([claim(planned_experiment_ids=["exp-pruning", "exp-pruning"])])
        errors = list(v.iter_errors(m))
        self.assertTrue(
            any(e.validator == "uniqueItems" for e in errors),
            msg="duplicate planned_experiment_ids should fail uniqueItems",
        )


# ===========================================================================
# 2. Cross-array invariants EP-INV-1..4 / EA-INV-1..2 (positive + negative).
# ===========================================================================


class CrossArrayInvariantTests(_LintBase):
    def test_baseline_positive(self) -> None:
        self.assertClean(build_passport())

    # --- EP-INV-1: experiment_id unique within the passport ---
    def test_ep_inv_1_duplicate_experiment_id(self) -> None:
        body = build_passport(
            provenance=[provenance_entry("exp-x"), provenance_entry("exp-x")]
        )
        self.assertFinds(body, "EP-INV-1")

    # --- EP-INV-2: planned_experiment_ids resolve ---
    def test_ep_inv_2_dangling_planned_experiment_id(self) -> None:
        body = build_passport(
            manifests=[manifest([claim(planned_experiment_ids=["exp-ghost"])])],
            provenance=[provenance_entry("exp-pruning")],
        )
        self.assertFinds(body, "EP-INV-2")

    # --- EP-INV-3: experiment ids => empirical kind ---
    def test_ep_inv_3_non_empirical_with_experiment_id(self) -> None:
        body = build_passport(
            manifests=[
                manifest(
                    [claim(kind="theoretical", planned_experiment_ids=["exp-pruning"])]
                )
            ]
        )
        self.assertFinds(body, "EP-INV-3")

    def test_ep_inv_3_mixed_evidence_allowed(self) -> None:
        """Mixed literature + experiment on an empirical claim is allowed."""
        body = build_passport(
            manifests=[
                manifest(
                    [
                        claim(
                            kind="empirical",
                            planned_refs=["dettmers2022int8"],
                            planned_experiment_ids=["exp-pruning"],
                        )
                    ]
                )
            ]
        )
        self.assertClean(body, msg="mixed-evidence empirical claim must not trip EP-INV-3")

    # --- EP-INV-4: declaration <-> provenance symmetry (deterministic half of D7) ---
    def test_ep_inv_4_declared_but_empty_provenance(self) -> None:
        body = build_passport(
            provenance=[],
            manifests=[manifest([claim()])],  # no experiment ids => no EP-INV-2 noise
            intake_declaration=declaration("experiments_declared"),
        )
        self.assertFinds(body, "EP-INV-4")

    def test_ep_inv_4_no_experiments_but_populated_provenance(self) -> None:
        body = build_passport(
            intake_declaration=declaration("no_experiments_declared"),
        )
        self.assertFinds(body, "EP-INV-4")

    def test_ep_inv_4_symmetry_clean_both_directions(self) -> None:
        # experiments_declared + non-empty provenance: clean.
        self.assertClean(
            build_passport(intake_declaration=declaration("experiments_declared"))
        )
        # no_experiments_declared + empty provenance: clean.
        self.assertClean(
            build_passport(
                provenance=[],
                manifests=[manifest([claim()])],
                intake_declaration=declaration("no_experiments_declared"),
            )
        )

    # --- EP-INV-5: declaration well-formedness when present ---
    def test_ep_inv_5_bad_status_enum(self) -> None:
        body = build_passport(
            intake_declaration={
                "status": "garbage",
                "declared_at": "2026-06-08T09:05:00Z",
                "declared_by": "scholar",
            },
        )
        self.assertFinds(body, "EP-INV-5")

    def test_ep_inv_5_declared_by_not_scholar(self) -> None:
        body = build_passport(
            intake_declaration={
                "status": "experiments_declared",
                "declared_at": "2026-06-08T09:05:00Z",
                "declared_by": "draft_writer_agent",
            },
        )
        self.assertFinds(body, "EP-INV-5")

    def test_ep_inv_5_missing_declared_at(self) -> None:
        body = build_passport(
            intake_declaration={
                "status": "experiments_declared",
                "declared_by": "scholar",
            },
        )
        self.assertFinds(body, "EP-INV-5")

    def test_ep_inv_5_legacy_unknown_is_valid_status(self) -> None:
        """legacy_unknown is a valid declaration status (D7); it must not trip EP-INV-5.

        Pair it with no provenance so the symmetry check (EP-INV-4) stays quiet
        — legacy_unknown is neither experiments_declared nor no_experiments_declared,
        so EP-INV-4 does not fire either way."""
        body = build_passport(
            provenance=[],
            manifests=[manifest([claim()])],
            intake_declaration={
                "status": "legacy_unknown",
                "declared_at": "2026-06-08T09:05:00Z",
                "declared_by": "scholar",
            },
        )
        self.assertClean(body)

    def test_ep_inv_5_absent_declaration_does_not_fire(self) -> None:
        """A wholly absent declaration is NOT an EP-INV-5 violation — presence/
        absence is the gate's ars_version-anchored decision, not this shape check."""
        body = {
            "claim_intent_manifests": [manifest([claim()])],
            "claim_audit_results": [],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
            "uncited_audit_failures": [],
        }
        self.assertClean(body)

    # --- EA-INV-1: finding_id unique ---
    def test_ea_inv_1_duplicate_finding_id(self) -> None:
        body = build_passport(
            alignment=[
                alignment_entry(finding_id="EA-001"),
                alignment_entry(finding_id="EA-001"),
            ]
        )
        self.assertFinds(body, "EA-INV-1")

    # --- EA-INV-2: alignment row references resolve ---
    def test_ea_inv_2_dangling_claim(self) -> None:
        body = build_passport(
            alignment=[alignment_entry(claim_id="C-999")],
        )
        self.assertFinds(body, "EA-INV-2")

    def test_ea_inv_2_dangling_experiment_id_is_structural_not_verdict(self) -> None:
        """A dangling experiment_id is a structural FAIL, never a PROVENANCE_MISSING verdict."""
        body = build_passport(
            alignment=[alignment_entry(experiment_id="exp-ghost")],
        )
        self.assertFinds(body, "EA-INV-2")


# ===========================================================================
# 3. Mixed-evidence two-row + worst-verdict-wins (structural correctness).
# The gate combination (worst-verdict-wins) is the integrity agent's job; at
# the lint/schema layer we pin that the two-row representation is well-formed
# and an OVERSTATED experiment row coexists with a clean citation path.
# ===========================================================================


class MixedEvidenceTests(_LintBase):
    def test_mixed_evidence_two_rows_clean(self) -> None:
        """C-002 mixed: a citation row (claim_audit_results) AND an experiment row."""
        m = manifest(
            [
                claim(
                    claim_id="C-002",
                    kind="empirical",
                    planned_refs=["dettmers2022int8"],
                    planned_experiment_ids=["exp-quant"],
                )
            ]
        )
        body = build_passport(
            manifests=[m],
            provenance=[provenance_entry("exp-quant")],
            alignment=[
                alignment_entry(
                    finding_id="EA-002",
                    claim_id="C-002",
                    experiment_id="exp-quant",
                    verdict="OVERSTATED",
                )
            ],
        )
        # The citation-path row for the same claim lives in claim_audit_results[];
        # add a SUPPORTED row keyed to the same (manifest, claim).
        body["claim_audit_results"] = [
            {
                "claim_id": "C-002",
                "scoped_manifest_id": MANIFEST_ID,
                "claim_text": "Claim C-002 text.",
                "ref_slug": "dettmers2022int8",
                "anchor_kind": "page",
                "anchor_value": "5",
                "judgment": "SUPPORTED",
                "audit_status": "completed",
                "defect_stage": None,
                "rationale": "Cited page supports the literature half of the claim.",
                "judge_model": "gpt-5.5-xhigh",
                "judge_run_at": "2026-06-08T09:22:00Z",
                "ref_retrieval_method": "api",
                "audit_run_id": "2026-06-08T09:10:00Z-9f8e",
            }
        ]
        # Both rows are well-formed and cross-resolve: lint stays clean. The
        # OVERSTATED verdict is a gate-decision input, not a lint violation.
        self.assertClean(body)

    def test_overstated_verdict_is_a_valid_enum_member(self) -> None:
        v = build_schema_validator(load_json_schema(ALIGNMENT_SCHEMA))
        self.assertEqual(
            list(v.iter_errors(alignment_entry(verdict="OVERSTATED"))),
            [],
        )


# ===========================================================================
# 4. Verdict-derivation rules (D4) — schema + agent-prompt level.
# The verdict is COMPUTED by the integrity agent at the gate; the derivation
# rules (negative-result-contradiction => NOT_SUPPORTED; all-skipped =>
# NOT_SUPPORTED) are encoded in integrity_verification_agent.md. We pin (a) the
# verdict enum admits NOT_SUPPORTED_BY_PROVENANCE, and (b) the agent prompt
# states both derivation rules so the heuristic and structured layers agree.
# ===========================================================================


class VerdictDerivationTests(unittest.TestCase):
    def test_not_supported_verdict_valid(self) -> None:
        v = build_schema_validator(load_json_schema(ALIGNMENT_SCHEMA))
        self.assertEqual(
            list(v.iter_errors(alignment_entry(verdict="NOT_SUPPORTED_BY_PROVENANCE"))),
            [],
        )

    def test_agent_prompt_states_negative_result_derivation(self) -> None:
        text = INTEGRITY_AGENT.read_text(encoding="utf-8")
        self.assertIn("negative_results", text)
        self.assertIn("NOT_SUPPORTED_BY_PROVENANCE", text)

    def test_agent_prompt_states_all_skipped_derivation(self) -> None:
        """The all-executed:false rule must TIE executed:false to the verdict.

        `planned_vs_executed` / `executed` are structural schema vocabulary that
        survive even if the derivation rule is stripped, so bare presence is too
        weak. We require an `executed:false ... NOT_SUPPORTED_BY_PROVENANCE`
        co-occurrence within a small window — the rule's actual triggering shape
        — so a prompt that mentions the fields but drops the rule fails."""
        import re

        text = INTEGRITY_AGENT.read_text(encoding="utf-8")
        self.assertIn("planned_vs_executed", text)
        # executed:false (any whitespace) followed by the verdict within ~300
        # chars — the all-skipped derivation rule, not two scattered keywords.
        pattern = re.compile(
            r"executed\s*:?\s*false.{0,300}NOT_SUPPORTED_BY_PROVENANCE",
            re.IGNORECASE | re.DOTALL,
        )
        self.assertRegex(
            text,
            pattern,
            msg="integrity agent must tie all-executed:false to "
            "NOT_SUPPORTED_BY_PROVENANCE (the all-skipped derivation rule)",
        )

    def test_provenance_entry_can_carry_all_skipped(self) -> None:
        """A provenance entry with every planned_vs_executed executed:false is
        well-formed shape-wise (the verdict derivation is the gate's job)."""
        v = build_schema_validator(load_json_schema(PROVENANCE_SCHEMA))
        entry = provenance_entry()
        entry["planned_vs_executed"] = [
            {
                "planned": "macro-F1 sweep",
                "executed": False,
                "skip_reason": "GPU unavailable",
            }
        ]
        self.assertEqual(list(v.iter_errors(entry)), [])


# ===========================================================================
# 5. Mutation test — each new invariant is load-bearing, not vacuous.
# We neutralise the invariant's check function (trivial accept-all) and assert
# the negative fixture flips from FAIL to FULLY CLEAN. Asserting "0 findings
# after mutation" (not merely "the target tag disappears") is the stronger form:
# it proves (a) the invariant is load-bearing for its fixture, AND (b) the
# fixture is isolated — it triggers ONLY that invariant, so a vacuous sibling
# could not hide behind a second still-firing finding. Each fixture below is
# single-invariant by construction; the 0-findings assert enforces that.
# ===========================================================================


class MutationTests(unittest.TestCase):
    """Prove each EP/EA invariant is load-bearing by neutralising it."""

    def _findings(self, body: dict[str, Any]) -> list[str]:
        return [f.render() for f in _lint.validate_passport(body)]

    def _assert_load_bearing(
        self, body: dict[str, Any], *, tag: str, fn_attr: str
    ) -> None:
        """Fire `tag` on `body`, then neutralise `_lint.<fn_attr>` and assert the
        fixture is FULLY clean (0 findings) — load-bearing AND single-invariant."""
        before = self._findings(body)
        self.assertIn(tag, _invariant_tags(before), msg=f"{tag} did not fire:\n" + "\n".join(before))
        original = getattr(_lint, fn_attr)
        try:
            setattr(_lint, fn_attr, lambda *a, **k: [])
            after = self._findings(body)
            self.assertEqual(
                after,
                [],
                msg=f"neutralising {fn_attr} should leave the {tag} fixture fully "
                f"clean (proving it is single-invariant + load-bearing); got:\n"
                + "\n".join(after),
            )
        finally:
            setattr(_lint, fn_attr, original)

    _EP = "_check_experiment_provenance_invariants"
    _EA = "_check_experiment_alignment_invariants"

    def test_mutation_ep_inv_1(self) -> None:
        body = build_passport(
            provenance=[provenance_entry("exp-x"), provenance_entry("exp-x")]
        )
        self._assert_load_bearing(body, tag="EP-INV-1", fn_attr=self._EP)

    def test_mutation_ep_inv_2(self) -> None:
        body = build_passport(
            manifests=[manifest([claim(planned_experiment_ids=["exp-ghost"])])],
            provenance=[provenance_entry("exp-pruning")],
        )
        self._assert_load_bearing(body, tag="EP-INV-2", fn_attr=self._EP)

    def test_mutation_ep_inv_3(self) -> None:
        body = build_passport(
            manifests=[
                manifest([claim(kind="normative", planned_experiment_ids=["exp-pruning"])])
            ]
        )
        self._assert_load_bearing(body, tag="EP-INV-3", fn_attr=self._EP)

    def test_mutation_ep_inv_4(self) -> None:
        body = build_passport(
            provenance=[],
            manifests=[manifest([claim()])],
            intake_declaration=declaration("experiments_declared"),
        )
        self._assert_load_bearing(body, tag="EP-INV-4", fn_attr=self._EP)

    def test_mutation_ep_inv_5(self) -> None:
        body = build_passport(
            intake_declaration={
                "status": "garbage",
                "declared_at": "2026-06-08T09:05:00Z",
                "declared_by": "scholar",
            },
        )
        self._assert_load_bearing(body, tag="EP-INV-5", fn_attr=self._EP)

    def test_mutation_ea_inv_1(self) -> None:
        body = build_passport(
            alignment=[
                alignment_entry(finding_id="EA-001"),
                alignment_entry(finding_id="EA-001"),
            ]
        )
        self._assert_load_bearing(body, tag="EA-INV-1", fn_attr=self._EA)

    def test_mutation_ea_inv_2(self) -> None:
        body = build_passport(alignment=[alignment_entry(claim_id="C-999")])
        self._assert_load_bearing(body, tag="EA-INV-2", fn_attr=self._EA)


# ===========================================================================
# 6. Reverse-invariant — the producers exist (writer-binding + intake).
# Pins that a future schema-required promotion can't silently drift ahead of
# the producers: the three writers carry the planned_experiment_ids emission
# instruction, and the intake/README + integrity agent carry the declaration.
# ===========================================================================


class ReverseInvariantTests(unittest.TestCase):
    def test_three_writers_emit_planned_experiment_ids(self) -> None:
        for name, path in WRITER_PROMPTS.items():
            with self.subTest(writer=name):
                text = path.read_text(encoding="utf-8")
                self.assertIn(
                    "planned_experiment_ids",
                    text,
                    msg=f"{name} prompt missing the planned_experiment_ids emission instruction",
                )

    def test_intake_declaration_producer_documented(self) -> None:
        """The declaration is set at Stage 1 intake — README documents it."""
        readme = (REPO / "README.md").read_text(encoding="utf-8")
        self.assertIn("experiment_intake_declaration", readme)

    def test_integrity_agent_carries_declaration_anti_skip(self) -> None:
        text = INTEGRITY_AGENT.read_text(encoding="utf-8")
        self.assertIn("experiment_intake_declaration", text)
        # The boundary non-goal wording must be carried verbatim (POSITIONING).
        self.assertIn("does not judge whether the experiment", text)


# ===========================================================================
# 7. Example + literature-only regressions.
# ===========================================================================


class RegressionTests(_LintBase):
    def test_shipped_example_shape_validates(self) -> None:
        proc = run_script(SHAPE_VALIDATOR, str(EXAMPLE), extra_env={"PYTHONPATH": str(REPO)})
        self.assertEqual(
            proc.returncode,
            0,
            msg=f"shape validator failed on example:\n{proc.stdout}\n{proc.stderr}",
        )

    def test_shipped_example_cross_array_clean(self) -> None:
        body = yaml.safe_load(EXAMPLE.read_text(encoding="utf-8"))
        self.assertClean(body, msg="shipped example must pass the cross-array lint")

    def test_literature_only_passport_not_broken(self) -> None:
        """A clean lit-review passport with no_experiments_declared and no
        experiment aggregates must pass — the fail-closed gate does not break
        the most common pipeline (no provenance needed, just the declaration)."""
        body = {
            "claim_intent_manifests": [
                manifest(
                    [claim(claim_id="C-001", kind="empirical", planned_refs=["smith2024"])]
                )
            ],
            "claim_audit_results": [],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
            "uncited_audit_failures": [],
            "experiment_intake_declaration": declaration("no_experiments_declared"),
        }
        self.assertClean(body)

    def test_legacy_passport_without_experiment_aggregates_clean(self) -> None:
        """A pre-#260 passport carrying none of the new aggregates and no
        declaration must not trip the new lint (the lint adds findings only when
        the symmetry is actively violated — absence is owned by the gate's
        ars_version heuristic, not the lint)."""
        body = {
            "claim_intent_manifests": [manifest([claim()])],
            "claim_audit_results": [],
            "uncited_assertions": [],
            "claim_drifts": [],
            "constraint_violations": [],
            "audit_sampling_summaries": [],
            "uncited_audit_failures": [],
        }
        self.assertClean(body)

    def test_experiment_only_claim_rides_ea_aggregate_not_claim_audit(self) -> None:
        """claim_audit_result.required regression (D4): an experiment-ONLY claim
        has no <!--ref:slug-->, so it cannot satisfy claim_audit_result.required
        (which mandates ref_slug). It rides experiment_alignment_results[] alone;
        claim_audit_results[] stays empty for it. This pins that the EA-only
        representation is the clean shape — a sentinel claim_audit_result row was
        deliberately NOT introduced (no relaxation of claim_audit_result.required)."""
        m = manifest([claim(claim_id="C-001", planned_experiment_ids=["exp-pruning"])])
        body = build_passport(
            manifests=[m],
            provenance=[provenance_entry("exp-pruning")],
            alignment=[alignment_entry(claim_id="C-001", experiment_id="exp-pruning")],
        )
        # No claim_audit_results[] row for the experiment-only claim.
        self.assertEqual(body["claim_audit_results"], [])
        self.assertClean(body)
        # And claim_audit_result.required still mandates ref_slug (untouched): an
        # experiment claim with no ref_slug cannot validate against that schema.
        car_schema = build_schema_validator(
            load_json_schema(PASSPORT / "claim_audit_result.schema.json")
        )
        ref_less_row = {
            "claim_id": "C-001",
            "scoped_manifest_id": MANIFEST_ID,
            "claim_text": "Experiment-only claim.",
            "judgment": "SUPPORTED",
            "audit_status": "completed",
        }  # no ref_slug
        self.assertNotEqual(
            list(car_schema.iter_errors(ref_less_row)),
            [],
            msg="claim_audit_result.required must still mandate ref_slug (no relaxation)",
        )


# ===========================================================================
# 8. D4-c experiment carve-out boundary (documents a known layering).
# The D4-c carve-out (an experiment-only claim must NOT be misrouted into
# uncited_assertions[]) lives at the LLM-caller / agent-prompt layer:
# claim_ref_alignment_audit_agent.md filters the sentence set BEFORE handing
# `uncited_sentences` to run_audit_pipeline. The deterministic detector
# (uncited_assertion_detector.detect_uncited) is sentence-level and
# manifest-UNAWARE — it cannot itself apply the carve-out, and
# run_audit_pipeline's docstring states the carve-out is "NOT invoked here".
# These tests pin that boundary EXPLICITLY so a future deterministic caller
# that skips the carve-out is a visible, tested decision — not a silent
# misroute. (Codex ship-gate review flagged this layering; the production
# caller is the LLM agent, which carves out correctly, so this is a guarded
# boundary, not a live defect.)
# ===========================================================================


class D4cCarveoutBoundaryTests(unittest.TestCase):
    def test_detector_is_manifest_unaware(self) -> None:
        """An experiment-backed sentence with a quantifier is a detect_uncited
        CANDIDATE — the detector cannot know it is experiment-backed. The
        carve-out is the caller's job, not the detector's."""
        from scripts.uncited_assertion_detector import detect_uncited

        is_candidate, tokens = detect_uncited(
            "Removing pruning lowers macro-F1 by 4.2 points on the held-out test set."
        )
        self.assertTrue(
            is_candidate,
            msg="detect_uncited is manifest-unaware: it flags an experiment "
            "sentence as a candidate; the LLM caller must carve it out via "
            "planned_experiment_ids before passing uncited_sentences downstream",
        )

    def test_pipeline_docstring_states_carveout_is_caller_responsibility(self) -> None:
        """run_audit_pipeline must keep documenting that the D4-c carve-out is
        NOT applied inside it — so a deterministic caller is on notice."""
        pipeline_src = (REPO / "scripts/claim_audit_pipeline.py").read_text(encoding="utf-8")
        self.assertIn("D4-c", pipeline_src)
        self.assertRegex(
            pipeline_src,
            r"D4-c.{0,200}(NOT invoked|is the filtered set|filtered)",
        )

    def test_agent_prompt_owns_the_carveout(self) -> None:
        """The carve-out instruction lives in the audit agent prompt (the
        production caller), reconciled with the orthogonal 'manifest membership
        does NOT exempt' rule."""
        agent = (
            REPO / "academic-pipeline/agents/claim_ref_alignment_audit_agent.md"
        ).read_text(encoding="utf-8")
        self.assertIn("planned_experiment_ids", agent)


if __name__ == "__main__":
    unittest.main()
