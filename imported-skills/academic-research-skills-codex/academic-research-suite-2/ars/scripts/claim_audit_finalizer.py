"""ARS v3.8 claim-faithfulness finalizer — 8-row matrix annotations + Stage 6 histogram.

Implements the orchestrator `§3.6 Claim-Faithfulness Audit Gate (v3.8)` matrix
table in `pipeline_orchestrator_agent.md`, plus the Stage 6 reflection
report histogram (renders when ≥5 completed audit entries exist).

The module is invoked by the orchestrator at the Stage 4 → Stage 5 boundary,
AFTER the v3.7.1 Cite-Time Provenance Finalizer resolves anchor presence,
and BEFORE `formatter_agent` runs its hard gate. The classify_* functions
project each passport aggregate row to `{annotation, tier, gate_refuse}`;
`apply_finalizer` reduces over the full passport to produce the
passport-level gate decision + reason list that the formatter consumes.

Spec:
  docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md §5 (8-row
  matrix), §"Manifest cross-reference (D6)" (drift / constraint routing),
  §3.6 (orchestrator prose).

This module deliberately does NO file I/O — it operates on Python dicts
matching the passport aggregate schemas. The orchestrator handles passport
assembly; the formatter handles refusal surfacing. Single-responsibility
keeps the matrix logic unit-testable.
"""
from __future__ import annotations

import re
from collections import Counter
from typing import Any

from scripts._claim_audit_constants import (
    INV14_FAULT_CLASS_TAGS,
    SENTINEL_MANIFEST_ID,
)

# ---------------------------------------------------------------------------
# Severity tiers (per spec §5 finalizer matrix).
# ---------------------------------------------------------------------------

TIER_NONE = "none"
TIER_LOW_WARN = "low_warn"
TIER_MED_WARN = "med_warn"
TIER_HIGH_WARN = "high_warn"

# ---------------------------------------------------------------------------
# Annotation literals (canonical wording per spec §5 table + §"uncited" /
# §"constraint_violation" / §"claim_drifts" subsections + §"audit_sampling").
#
# These literals are the contract surface between the orchestrator and the
# formatter; `formatter_agent.md` REFUSE list reads them via string match.
# Changing a literal here MUST coordinate with the formatter prose update.
# ---------------------------------------------------------------------------

ANNOTATION_CLAIM_AUDIT_AMBIGUOUS = "[CLAIM-AUDIT-AMBIGUOUS]"
ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED = "[HIGH-WARN-CLAIM-NOT-SUPPORTED]"
ANNOTATION_HIGH_WARN_NEGATIVE_CONSTRAINT_VIOLATION = (
    "[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION ({violated_constraint_id})]"
)
ANNOTATION_HIGH_WARN_FABRICATED_REFERENCE = "[HIGH-WARN-FABRICATED-REFERENCE]"
ANNOTATION_HIGH_WARN_ANCHORLESS = (
    "[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS — v3.7.3 R-L3-1-A VIOLATION REACHED AUDIT]"
)
ANNOTATION_LOW_WARN_UNVERIFIED = (
    "[CLAIM-AUDIT-UNVERIFIED — REFERENCE FULL-TEXT NOT RETRIEVABLE]"
)
ANNOTATION_MED_WARN_TOOL_FAILURE = "[CLAIM-AUDIT-TOOL-FAILURE — {fault_class}]"
# v3.8.2 / #118 — UAF aggregate annotation. Same fault-class enum as the
# cited-path INV-14 row but routed through `uncited_audit_failures[]`
# because claim_audit_result.ref_slug is required.
ANNOTATION_MED_WARN_TOOL_FAILURE_UNCITED = "[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — {fault_class}]"

ANNOTATION_UNCITED_ASSERTION = "[UNCITED-ASSERTION]"
ANNOTATION_HIGH_WARN_CONSTRAINT_VIOLATION_UNCITED = (
    "[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED ({violated_constraint_id})]"
)
ANNOTATION_LOW_WARN_CLAIM_DRIFT = "[LOW-WARN-CLAIM-DRIFT — kind={drift_kind}]"
ANNOTATION_SAMPLING = (
    "[CLAIM-AUDIT-SAMPLED — {audited_count}/{total_citation_count} audited]"
)

ANNOTATION_MANIFEST_MISSING = (
    "[CLAIM-AUDIT-MANIFEST-MISSING — audit ran without pre-commitment baseline]"
)

# Set of annotation prefixes that `/ars-mark-read` CANNOT clear — structural
# verdicts on prose faithfulness rather than acknowledgement-eligible trust
# states. Mirrors v3.7.3 R-L3-1-A asymmetry (locator is structural).
_UNCLEARABLE_HIGH_WARN_PREFIXES: tuple[str, ...] = (
    "[HIGH-WARN-CLAIM-NOT-SUPPORTED]",
    "[HIGH-WARN-NEGATIVE-CONSTRAINT-VIOLATION",
    "[HIGH-WARN-FABRICATED-REFERENCE]",
    "[HIGH-WARN-CLAIM-AUDIT-ANCHORLESS",
    "[HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED",
)

# Permitted defect_stages for the source-level UNSUPPORTED row (T-F1c).
_UNSUPPORTED_SOURCE_LEVEL_DEFECTS: frozenset[str] = frozenset(
    {"source_description", "metadata", "citation_anchor", "synthesis_overclaim"}
)

# Rationale prefix regex for audit_tool_failure rows — the fault-class tag is
# the leading colon-terminated token per INV-14 (spec §"Error handling").
_RATIONALE_FAULT_CLASS_RE = re.compile(r"^([a-z_]+):")


def _classify_retrieval_failed(
    *,
    defect_stage: str | None,
    ref_retrieval_method: str,
    rationale: str,
) -> dict[str, Any]:
    """Discriminate the three (RETRIEVAL_FAILED, not_applicable) rows by method.

    Raises ValueError on (defect_stage, ref_retrieval_method) combinations not
    covered by the §5 matrix rows. The spec §6 consistency lint
    (`check_claim_audit_consistency.py`) is the authoritative upstream gate
    — it rejects malformed rows BEFORE they reach the finalizer. A raise
    here signals that an out-of-contract row escaped lint (e.g. INV-10 /
    INV-11 / INV-14 violation, or a passport assembled without lint
    validation). Coercing such rows to a default tier would silently mask
    the upstream bug; raising surfaces it.
    """
    if defect_stage == "retrieval_existence" and ref_retrieval_method == "not_found":
        return {
            "annotation": ANNOTATION_HIGH_WARN_FABRICATED_REFERENCE,
            "tier": TIER_HIGH_WARN,
            "gate_refuse": True,
        }
    if defect_stage == "not_applicable":
        if ref_retrieval_method == "not_attempted":
            return {
                "annotation": ANNOTATION_HIGH_WARN_ANCHORLESS,
                "tier": TIER_HIGH_WARN,
                "gate_refuse": True,
            }
        if ref_retrieval_method == "failed":
            return {
                "annotation": ANNOTATION_LOW_WARN_UNVERIFIED,
                "tier": TIER_LOW_WARN,
                "gate_refuse": False,
            }
        if ref_retrieval_method == "audit_tool_failure":
            match = _RATIONALE_FAULT_CLASS_RE.match(rationale)
            fault_class = (
                match.group(1)
                if match and match.group(1) in INV14_FAULT_CLASS_TAGS
                else "retrieval_api_error"
            )
            return {
                "annotation": ANNOTATION_MED_WARN_TOOL_FAILURE.format(fault_class=fault_class),
                "tier": TIER_MED_WARN,
                "gate_refuse": False,
            }
    raise ValueError(
        f"unexpected RETRIEVAL_FAILED row: defect_stage={defect_stage!r} "
        f"ref_retrieval_method={ref_retrieval_method!r}"
    )


def classify_claim_audit_result(entry: dict[str, Any]) -> dict[str, Any]:
    """Apply the §5 8-row matrix to a single claim_audit_result row.

    Returns `{"annotation": str | None, "tier": str, "gate_refuse": bool}`.
    `annotation=None` indicates the SUPPORTED pass row (no formatter output).
    """
    judgment = entry["judgment"]
    defect_stage = entry.get("defect_stage")
    ref_retrieval_method = entry.get("ref_retrieval_method", "not_attempted")
    rationale = entry.get("rationale", "")

    if judgment == "SUPPORTED":
        return {"annotation": None, "tier": TIER_NONE, "gate_refuse": False}

    if judgment == "AMBIGUOUS":
        # Spec §3.1 INV-3 permits {source_description, citation_anchor,
        # synthesis_overclaim, null} on AMBIGUOUS — the §6 consistency lint is
        # the authoritative gate for the allowed-matrix invariant. The matrix
        # row, however, ALWAYS emits the same annotation + tier regardless of
        # which permitted defect_stage the judge picked, so the local
        # `defect_stage` value never affects the return. The previous version
        # of this branch reassigned out-of-set values to None but never read
        # them back — dead code per Step 8 codex /simplify advisory.
        # Validation stays the lint's responsibility (§6 rule 5); this branch
        # produces the LOW-WARN advisory and trusts the schema-validated row.
        return {
            "annotation": ANNOTATION_CLAIM_AUDIT_AMBIGUOUS,
            "tier": TIER_LOW_WARN,
            "gate_refuse": False,
        }

    if judgment == "UNSUPPORTED":
        if defect_stage == "negative_constraint_violation":
            return {
                "annotation": ANNOTATION_HIGH_WARN_NEGATIVE_CONSTRAINT_VIOLATION.format(
                    violated_constraint_id=entry.get("violated_constraint_id", "?")
                ),
                "tier": TIER_HIGH_WARN,
                "gate_refuse": True,
            }
        if defect_stage in _UNSUPPORTED_SOURCE_LEVEL_DEFECTS:
            return {
                "annotation": ANNOTATION_HIGH_WARN_CLAIM_NOT_SUPPORTED,
                "tier": TIER_HIGH_WARN,
                "gate_refuse": True,
            }
        raise ValueError(
            f"UNSUPPORTED row carries unexpected defect_stage={defect_stage!r}; "
            "spec §3.1 INV-2 permits source_description / metadata / citation_anchor / "
            "synthesis_overclaim / negative_constraint_violation only"
        )

    if judgment == "RETRIEVAL_FAILED":
        return _classify_retrieval_failed(
            defect_stage=defect_stage,
            ref_retrieval_method=ref_retrieval_method,
            rationale=rationale,
        )

    raise ValueError(f"unknown judgment: {judgment!r}")


def classify_uncited_assertion(entry: dict[str, Any]) -> dict[str, Any]:
    """LOW-WARN advisory `[UNCITED-ASSERTION]` for every uncited_assertions[] row."""
    return {
        "annotation": ANNOTATION_UNCITED_ASSERTION,
        "tier": TIER_LOW_WARN,
        "gate_refuse": False,
    }


def classify_constraint_violation(entry: dict[str, Any]) -> dict[str, Any]:
    """HIGH-WARN gate-refuse for uncited claim that violates MNC/NC scope."""
    return {
        "annotation": ANNOTATION_HIGH_WARN_CONSTRAINT_VIOLATION_UNCITED.format(
            violated_constraint_id=entry.get("violated_constraint_id", "?")
        ),
        "tier": TIER_HIGH_WARN,
        "gate_refuse": True,
    }


def classify_claim_drift(entry: dict[str, Any]) -> dict[str, Any]:
    """LOW-WARN advisory for drift findings (per D4-a; never gate-refuses)."""
    return {
        "annotation": ANNOTATION_LOW_WARN_CLAIM_DRIFT.format(drift_kind=entry["drift_kind"]),
        "tier": TIER_LOW_WARN,
        "gate_refuse": False,
    }


def classify_uncited_audit_failure(entry: dict[str, Any]) -> dict[str, Any]:
    """MED-WARN advisory for uncited-path judge outage (v3.8.2 / #118).

    Mirrors INV-14 semantics on the uncited path: emits
    `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]` next to the
    offending sentence. Gate passes — retry-next-pass remediation.
    UAF-INV-5 (lint) guarantees `fault_class` is one of the seven
    INV14_FAULT_CLASS_TAGS values; we surface the row's literal here.

    The `or "?"` fallback covers both missing-key (KeyError equivalent)
    and explicit-null (`"fault_class": null`) cases — without it a
    malformed row with explicit null would render as `[...— None]`
    (Gemini R2 P3, 2026-05-17). Schema validation rejects either form,
    but a defensive renderer is one less thing to think about.
    """
    return {
        "annotation": ANNOTATION_MED_WARN_TOOL_FAILURE_UNCITED.format(
            fault_class=entry.get("fault_class") or "?",
        ),
        "tier": TIER_MED_WARN,
        "gate_refuse": False,
    }


def classify_audit_sampling_summary(entry: dict[str, Any]) -> dict[str, Any]:
    """Paper-level LOW-WARN annotation when audited_count < total_citation_count (S-INV-3)."""
    if entry["audited_count"] >= entry["total_citation_count"]:
        return {"annotation": None, "tier": TIER_NONE, "gate_refuse": False}
    return {
        "annotation": ANNOTATION_SAMPLING.format(
            audited_count=entry["audited_count"],
            total_citation_count=entry["total_citation_count"],
        ),
        "tier": TIER_LOW_WARN,
        "gate_refuse": False,
    }


def apply_finalizer(passport: dict[str, list[dict[str, Any]]]) -> dict[str, Any]:
    """Run the matrix across every passport aggregate; reduce to a gate decision.

    Returns:
        {
            "annotations": list of {entry_ref, annotation, tier},
            "gate_refuse": bool — True if any row has gate_refuse=True,
            "gate_refuse_reasons": list[str] — annotations that triggered refuse,
        }
    """
    annotations: list[dict[str, Any]] = []
    gate_refuse_reasons: list[str] = []

    routing: tuple[tuple[str, Any], ...] = (
        ("claim_audit_results", classify_claim_audit_result),
        ("uncited_assertions", classify_uncited_assertion),
        ("constraint_violations", classify_constraint_violation),
        ("claim_drifts", classify_claim_drift),
        # v3.8.2 / #118 — UAF aggregate routes to MED-WARN advisory.
        # Placed BEFORE audit_sampling_summaries so sentence-level
        # annotations group with the other line-item checks; the
        # paper-level sampling summary belongs at the tail (Gemini R2
        # P3, 2026-05-17). Without this entry, the schema/lint accept
        # UAF rows but the finalizer never surfaces them and the
        # formatter never sees the [CLAIM-AUDIT-TOOL-FAILURE-UNCITED — ...]
        # annotation (Codex R1 P2-1, 2026-05-17).
        ("uncited_audit_failures", classify_uncited_audit_failure),
        ("audit_sampling_summaries", classify_audit_sampling_summary),
    )

    for aggregate_key, classifier in routing:
        for entry in passport.get(aggregate_key, []):
            result = classifier(entry)
            if result["annotation"] is None:
                continue
            annotations.append(
                {
                    "aggregate": aggregate_key,
                    "entry": entry,
                    "annotation": result["annotation"],
                    "tier": result["tier"],
                }
            )
            if result["gate_refuse"]:
                gate_refuse_reasons.append(result["annotation"])

    # MANIFEST-MISSING paper-level advisory (spec §9 acceptance criterion;
    # Step 8 codex R1 P2 closure). Fires when the audit ran without a
    # pre-commitment baseline — both `claim_intent_manifests[]` is empty
    # AND at least one claim_audit_result carries the sentinel scope. The
    # second condition prevents firing on an empty passport (where there's
    # nothing to surface a warning about). Always advisory; never
    # gate-refuses (the audit completed, it just lacks the drift /
    # constraint-inheritance signal a manifest would have provided).
    if not passport.get("claim_intent_manifests"):
        has_sentinel_row = any(
            r.get("scoped_manifest_id") == SENTINEL_MANIFEST_ID
            for r in passport.get("claim_audit_results", [])
        )
        if has_sentinel_row:
            annotations.append(
                {
                    "aggregate": "paper_level",
                    "entry": None,
                    "annotation": ANNOTATION_MANIFEST_MISSING,
                    "tier": TIER_LOW_WARN,
                }
            )

    return {
        "annotations": annotations,
        "gate_refuse": bool(gate_refuse_reasons),
        "gate_refuse_reasons": gate_refuse_reasons,
    }


def render_stage6_histogram(
    claim_audit_results: list[dict[str, Any]],
    *,
    threshold: int = 5,
) -> str | None:
    """Render the per-defect_stage histogram for the AI Self-Reflection Report.

    Threshold is on `audit_status == "completed"` rows (per spec §"Outputs
    feeding Stage 6 self-reflection" literal "≥ 5 completed entries"). When
    fewer than `threshold` completed rows exist, returns None.

    When the threshold is met, the histogram counts rows by `defect_stage`,
    excluding null values (SUPPORTED rows). If every completed row is
    SUPPORTED (zero defects to plot), the histogram still emits — it
    surfaces "No defect stages recorded across N completed entries." so
    the Stage 6 appendix stays consistent and the user sees that the audit
    ran clean rather than wondering whether the histogram was suppressed.

    Step 8 codex R4 P2-1 closure: prior implementation gated the threshold
    on completed-with-defect rows, suppressing the appendix when the
    paper had ≥5 completed audits but ≤4 defect_stage entries. Spec
    literal is "≥ 5 completed entries"; common mostly-SUPPORTED papers
    must still surface the reflection block.

    The output is a stable plain-text rendering keyed by defect_stage; the
    orchestrator embeds it under the Stage 6 reflection appendix. Stage-6
    formatting (markdown headings, separators) is the orchestrator's
    responsibility; this module emits only the histogram block.
    """
    completed = [r for r in claim_audit_results if r.get("audit_status") == "completed"]
    if len(completed) < threshold:
        return None

    defects = [r["defect_stage"] for r in completed if r.get("defect_stage") is not None]
    n_completed = len(completed)

    if not defects:
        return (
            f"Claim-faithfulness defect_stage histogram (n={n_completed} completed entries):"
            f"\n  - No defect stages recorded across {n_completed} completed entries."
        )

    counts = Counter(defects)
    lines = [f"Claim-faithfulness defect_stage histogram (n={n_completed} completed entries):"]
    for stage in sorted(counts):
        lines.append(f"  - {stage}: {counts[stage]}")
    return "\n".join(lines)


def ars_mark_read_clears(*, annotation: str, tier: str) -> bool:
    """Return True iff `/ars-mark-read` can promote the annotation to cleared state.

    HIGH-WARN classes covering structural verdicts on prose faithfulness CANNOT
    be cleared by acknowledgement (T-F3 asymmetry, mirrors v3.7.3 R-L3-1-A).
    LOW-WARN paywall / advisory rows CAN — the user has accepted the
    unverifiable state and chosen to ship.

    The MED-WARN audit_tool_failure row is NOT acknowledgement-clearable
    either (the remediation is retry on next pipeline pass, not
    acknowledgement); it stays surfaced until a fresh audit pass resolves
    the underlying infrastructure problem or downgrades to LOW-WARN paywall.
    """
    if tier == TIER_HIGH_WARN:
        return False
    if tier == TIER_MED_WARN:
        return False
    # The HIGH-WARN-prefix check below is defense-in-depth against
    # caller bugs where a HIGH-WARN annotation arrives with mismatched
    # tier=TIER_LOW_WARN (e.g. a passport hand-edit or a downstream
    # consumer that lost the tier mapping). Well-formed inputs never
    # trigger this branch — every HIGH-WARN prefix is produced only by
    # the matrix paths that also set tier=TIER_HIGH_WARN. Keeping the
    # check rather than dropping it preserves the safety surface; a
    # silent True return on a mistyped HIGH-WARN would acknowledge a
    # gate-refuse-class violation as cleared.
    return tier == TIER_LOW_WARN and not any(
        annotation.startswith(prefix) for prefix in _UNCLEARABLE_HIGH_WARN_PREFIXES
    )
