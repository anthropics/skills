#!/usr/bin/env python3
"""check_claim_audit_consistency.py — ARS v3.8 claim-faithfulness audit lint.

Enforces the 39 cross-field invariants spanning the six aggregates that
claim_ref_alignment_audit_agent populates:

    claim_audit_results[]           — INV-1..INV-19      (§3.1)
    claim_intent_manifests[]        — M-INV-1..M-INV-4   (§3.2)
    uncited_assertions[]            — U-INV-1..U-INV-4   (§3.3)
    claim_drifts[]                  — D-INV-1..D-INV-4   (§3.4)
    constraint_violations[]         — CV-INV-1..CV-INV-4 (§3.5)
    audit_sampling_summaries[]      — S-INV-1..S-INV-4   (§4 step 3)

Plus the §3.1 allowed (judgment, audit_status, defect_stage) matrix, and
schema-shape validation for every entry in each aggregate against the
corresponding shipped JSON Schema.

Cross-field invariants are intentionally NOT expressed in JSON Schema —
the matrix is conditional and the cross-array (scoped_manifest_id, *)
integrity checks span aggregates. This lint is the contract under test
in scripts/test_claim_audit_schema.py.

CLI:
    python3 scripts/check_claim_audit_consistency.py --passport <path>

Exit codes:
    0   no findings
    1   one or more invariant violations (printed to stdout, one per line)
    2   internal error (passport not found / malformed JSON / schema not found)

See docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md
§3.1-§3.5 and §6 for the full invariant catalogue.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
import urllib.parse
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from jsonschema import Draft202012Validator

# Allow both CLI invocations (`python3 scripts/check_claim_audit_consistency.py`)
# AND package-style invocations (`python -m unittest scripts.test_*`) to resolve
# the shared constants module. The CLI path puts scripts/ on sys.path, the
# unittest path puts repo root on sys.path — the insert below covers the gap.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _claim_audit_constants import (  # noqa: E402
    INV6_RATIONALE_PREFIX,
    INV14_FAULT_CLASS_TAGS,
    RE_CLAIM_ID,
    RE_MNC_CONSTRAINT,
    RE_NC_CONSTRAINT,
    RE_NC_INNER_HYPHEN,
    SENTINEL_MANIFEST_ID,
    SUBCLAIM_NON_SUPPORTED,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
PASSPORT_SCHEMAS = REPO_ROOT / "shared/contracts/passport"

SCHEMA_FILES = {
    "claim_audit_result": PASSPORT_SCHEMAS / "claim_audit_result.schema.json",
    "claim_intent_manifest": PASSPORT_SCHEMAS / "claim_intent_manifest.schema.json",
    "uncited_assertion": PASSPORT_SCHEMAS / "uncited_assertion.schema.json",
    "claim_drift": PASSPORT_SCHEMAS / "claim_drift.schema.json",
    "constraint_violation": PASSPORT_SCHEMAS / "constraint_violation.schema.json",
    "uncited_audit_failure": PASSPORT_SCHEMAS / "uncited_audit_failure.schema.json",
    "experiment_provenance_entry": PASSPORT_SCHEMAS / "experiment_provenance_entry.schema.json",
    "experiment_alignment_result": PASSPORT_SCHEMAS / "experiment_alignment_result.schema.json",
}

# Inline schema for audit_sampling_summary (spec §4 step 3) — not a shipped file.
AUDIT_SAMPLING_SUMMARY_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "additionalProperties": False,
    "required": [
        "audit_run_id",
        "max_claims_per_paper",
        "total_citation_count",
        "audited_count",
        "audited_indices",
        "sampling_strategy",
        "emitted_at",
    ],
    "properties": {
        "audit_run_id": {
            "type": "string",
            "pattern": r"^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z-[0-9a-f]{4}$",
        },
        "max_claims_per_paper": {"type": "integer", "minimum": 1},
        "total_citation_count": {"type": "integer", "minimum": 0},
        "audited_count": {"type": "integer", "minimum": 0},
        "audited_indices": {
            "type": "array",
            "items": {"type": "integer", "minimum": 0},
        },
        "sampling_strategy": {"const": "stratified_buckets_v1"},
        "emitted_at": {"type": "string", "format": "date-time"},
    },
}

# Allowed (judgment, audit_status, defect_stage) triples — §3.1 table.
# Negative-constraint-violation rows still permit any ref_retrieval_method
# in this matrix; INV-7/INV-8 further restrict the surrounding shape.
ALLOWED_MATRIX: set[tuple[str, str, Any]] = {
    ("SUPPORTED", "completed", None),
    ("AMBIGUOUS", "completed", "source_description"),
    ("AMBIGUOUS", "completed", "citation_anchor"),
    ("AMBIGUOUS", "completed", "synthesis_overclaim"),
    ("AMBIGUOUS", "completed", None),
    ("UNSUPPORTED", "completed", "source_description"),
    ("UNSUPPORTED", "completed", "metadata"),
    ("UNSUPPORTED", "completed", "citation_anchor"),
    ("UNSUPPORTED", "completed", "synthesis_overclaim"),
    ("UNSUPPORTED", "completed", "negative_constraint_violation"),
    ("RETRIEVAL_FAILED", "completed", "retrieval_existence"),
    ("RETRIEVAL_FAILED", "inconclusive", "not_applicable"),
}

@dataclass(frozen=True)
class Finding:
    invariant: str
    detail: str

    def render(self) -> str:
        return f"{self.invariant}: {self.detail}"


# ---------------------------------------------------------------------------
# Schema loaders (cached once per process to amortise check_schema cost).
# ---------------------------------------------------------------------------

_VALIDATORS: dict[str, Draft202012Validator] = {}


def _validator(name: str) -> Draft202012Validator:
    if name not in _VALIDATORS:
        if name == "audit_sampling_summary":
            schema = AUDIT_SAMPLING_SUMMARY_SCHEMA
        else:
            path = SCHEMA_FILES[name]
            if not path.is_file():
                raise FileNotFoundError(f"schema missing: {path}")
            schema = json.loads(path.read_text(encoding="utf-8"))
        Draft202012Validator.check_schema(schema)
        _VALIDATORS[name] = Draft202012Validator(
            schema, format_checker=Draft202012Validator.FORMAT_CHECKER
        )
    return _VALIDATORS[name]


# ---------------------------------------------------------------------------
# claim_audit_result invariants (INV-1..INV-19).
# Each helper returns a list of Findings; the caller aggregates across rows.
# ---------------------------------------------------------------------------


def _check_inv_1(e: dict[str, Any]) -> list[Finding]:
    """SUPPORTED -> defect_stage=null AND violated_constraint_id=null AND completed."""
    if e.get("judgment") != "SUPPORTED":
        return []
    findings: list[Finding] = []
    if e.get("defect_stage") is not None:
        findings.append(Finding("INV-1", f"SUPPORTED row has non-null defect_stage={e['defect_stage']!r}"))
    if e.get("violated_constraint_id") not in (None, ""):
        findings.append(Finding("INV-1", "SUPPORTED row has non-null violated_constraint_id"))
    if e.get("audit_status") != "completed":
        findings.append(Finding("INV-1", f"SUPPORTED row has audit_status={e.get('audit_status')!r}"))
    return findings


def _check_inv_2(e: dict[str, Any]) -> list[Finding]:
    """UNSUPPORTED -> defect_stage in 5-set AND completed."""
    if e.get("judgment") != "UNSUPPORTED":
        return []
    allowed = {
        "source_description",
        "metadata",
        "citation_anchor",
        "synthesis_overclaim",
        "negative_constraint_violation",
    }
    findings: list[Finding] = []
    if e.get("defect_stage") not in allowed:
        findings.append(
            Finding(
                "INV-2",
                f"UNSUPPORTED row has defect_stage={e.get('defect_stage')!r}; must be one of {sorted(allowed)}",
            )
        )
    if e.get("audit_status") != "completed":
        findings.append(Finding("INV-2", f"UNSUPPORTED row has audit_status={e.get('audit_status')!r}"))
    return findings


def _check_inv_3(e: dict[str, Any]) -> list[Finding]:
    """AMBIGUOUS -> defect_stage in {source_description, citation_anchor, synthesis_overclaim, None}."""
    if e.get("judgment") != "AMBIGUOUS":
        return []
    allowed = {"source_description", "citation_anchor", "synthesis_overclaim", None}
    findings: list[Finding] = []
    if e.get("defect_stage") not in allowed:
        findings.append(
            Finding(
                "INV-3",
                f"AMBIGUOUS row has defect_stage={e.get('defect_stage')!r}; must be one of "
                f"{sorted([x for x in allowed if x is not None]) + ['null']}",
            )
        )
    if e.get("audit_status") != "completed":
        findings.append(Finding("INV-3", f"AMBIGUOUS row has audit_status={e.get('audit_status')!r}"))
    return findings


def _check_inv_4(e: dict[str, Any]) -> list[Finding]:
    """RETRIEVAL_FAILED + inconclusive -> defect_stage=not_applicable."""
    if e.get("judgment") != "RETRIEVAL_FAILED":
        return []
    if e.get("audit_status") != "inconclusive":
        return []
    if e.get("defect_stage") != "not_applicable":
        return [
            Finding(
                "INV-4",
                f"RETRIEVAL_FAILED+inconclusive row has defect_stage={e.get('defect_stage')!r}; must be not_applicable",
            )
        ]
    return []


def _check_inv_5(e: dict[str, Any]) -> list[Finding]:
    """RETRIEVAL_FAILED + completed -> defect_stage=retrieval_existence."""
    if e.get("judgment") != "RETRIEVAL_FAILED":
        return []
    if e.get("audit_status") != "completed":
        return []
    if e.get("defect_stage") != "retrieval_existence":
        return [
            Finding(
                "INV-5",
                f"RETRIEVAL_FAILED+completed row has defect_stage={e.get('defect_stage')!r}; must be retrieval_existence",
            )
        ]
    return []


def _check_inv_6(e: dict[str, Any]) -> list[Finding]:
    """anchor_kind=none firm rule (D1)."""
    if e.get("anchor_kind") != "none":
        return []
    findings: list[Finding] = []
    if e.get("judgment") != "RETRIEVAL_FAILED":
        findings.append(Finding("INV-6", f"anchor=none row has judgment={e.get('judgment')!r}; must be RETRIEVAL_FAILED"))
    if e.get("audit_status") != "inconclusive":
        findings.append(Finding("INV-6", f"anchor=none row has audit_status={e.get('audit_status')!r}; must be inconclusive"))
    if e.get("defect_stage") != "not_applicable":
        findings.append(Finding("INV-6", f"anchor=none row has defect_stage={e.get('defect_stage')!r}; must be not_applicable"))
    if e.get("ref_retrieval_method") != "not_attempted":
        findings.append(
            Finding(
                "INV-6",
                f"anchor=none row has ref_retrieval_method={e.get('ref_retrieval_method')!r}; must be not_attempted",
            )
        )
    # Schema mandates the empty sentinel for anchor_value when anchor_kind=none.
    # A residual stale anchor (e.g. "123") here violates the schema contract;
    # pipeline _anchorless_entry pins "" but the lint must enforce it for
    # passports authored outside the pipeline (manual fixtures, replays).
    if e.get("anchor_value", "") != "":
        findings.append(
            Finding(
                "INV-6",
                f"anchor=none row has non-empty anchor_value={e.get('anchor_value')!r}; must be empty sentinel string",
            )
        )
    rationale = e.get("rationale") or ""
    if not rationale.startswith(INV6_RATIONALE_PREFIX):
        findings.append(
            Finding(
                "INV-6",
                f"anchor=none row rationale must start with {INV6_RATIONALE_PREFIX!r}; got {rationale[:60]!r}",
            )
        )
    return findings


def _check_inv_7(e: dict[str, Any]) -> list[Finding]:
    """defect_stage=negative_constraint_violation -> violated_constraint_id != null."""
    if e.get("defect_stage") != "negative_constraint_violation":
        return []
    if e.get("violated_constraint_id") in (None, ""):
        return [Finding("INV-7", "negative_constraint_violation row has null violated_constraint_id")]
    return []


def _check_inv_8(e: dict[str, Any]) -> list[Finding]:
    """defect_stage=negative_constraint_violation -> judgment=UNSUPPORTED."""
    if e.get("defect_stage") != "negative_constraint_violation":
        return []
    if e.get("judgment") != "UNSUPPORTED":
        return [
            Finding(
                "INV-8",
                f"negative_constraint_violation row has judgment={e.get('judgment')!r}; must be UNSUPPORTED",
            )
        ]
    return []


def _check_inv_9(e: dict[str, Any]) -> list[Finding]:
    """upstream_dispute != null -> defect_stage substantive."""
    if not e.get("upstream_dispute"):
        return []
    stage = e.get("defect_stage")
    if stage in (None, "not_applicable"):
        return [
            Finding(
                "INV-9",
                f"upstream_dispute set on non-substantive row (defect_stage={stage!r})",
            )
        ]
    return []


def _check_inv_10(e: dict[str, Any]) -> list[Finding]:
    """ref_retrieval_method=failed -> RETRIEVAL_FAILED + inconclusive + not_applicable."""
    if e.get("ref_retrieval_method") != "failed":
        return []
    findings: list[Finding] = []
    if e.get("judgment") != "RETRIEVAL_FAILED":
        findings.append(Finding("INV-10", f"method=failed but judgment={e.get('judgment')!r}"))
    if e.get("audit_status") != "inconclusive":
        findings.append(Finding("INV-10", f"method=failed but audit_status={e.get('audit_status')!r}"))
    if e.get("defect_stage") != "not_applicable":
        findings.append(Finding("INV-10", f"method=failed but defect_stage={e.get('defect_stage')!r}"))
    return findings


def _check_inv_11(e: dict[str, Any]) -> list[Finding]:
    """ref_retrieval_method=not_attempted ↔ anchor_kind=none."""
    method = e.get("ref_retrieval_method")
    kind = e.get("anchor_kind")
    if method == "not_attempted" and kind != "none":
        return [
            Finding(
                "INV-11",
                f"method=not_attempted but anchor_kind={kind!r}; must be none",
            )
        ]
    if kind == "none" and method != "not_attempted":
        return [
            Finding(
                "INV-11",
                f"anchor=none but ref_retrieval_method={method!r}; must be not_attempted",
            )
        ]
    return []


def _check_inv_12(e: dict[str, Any]) -> list[Finding]:
    """ref_retrieval_method=not_found ↔ RETRIEVAL_FAILED + completed + retrieval_existence."""
    method = e.get("ref_retrieval_method")
    triple = (e.get("judgment"), e.get("audit_status"), e.get("defect_stage"))
    fabricated = ("RETRIEVAL_FAILED", "completed", "retrieval_existence")
    if method == "not_found" and triple != fabricated:
        return [
            Finding(
                "INV-12",
                f"method=not_found but triple={triple!r}; must be {fabricated!r}",
            )
        ]
    if triple == fabricated and method != "not_found":
        return [
            Finding(
                "INV-12",
                f"fabricated triple but method={method!r}; must be not_found",
            )
        ]
    return []


def _check_inv_13(e: dict[str, Any]) -> list[Finding]:
    """defect_stage=metadata -> UNSUPPORTED + completed + method in {api, manual_pdf}."""
    if e.get("defect_stage") != "metadata":
        return []
    findings: list[Finding] = []
    if e.get("judgment") != "UNSUPPORTED":
        findings.append(Finding("INV-13", f"metadata row has judgment={e.get('judgment')!r}"))
    if e.get("audit_status") != "completed":
        findings.append(Finding("INV-13", f"metadata row has audit_status={e.get('audit_status')!r}"))
    if e.get("ref_retrieval_method") not in ("api", "manual_pdf"):
        findings.append(
            Finding(
                "INV-13",
                f"metadata row has ref_retrieval_method={e.get('ref_retrieval_method')!r}; must be api or manual_pdf",
            )
        )
    return findings


def _check_inv_14(e: dict[str, Any]) -> list[Finding]:
    """audit_tool_failure -> RETRIEVAL_FAILED + inconclusive + not_applicable + rationale fault-class prefix."""
    if e.get("ref_retrieval_method") != "audit_tool_failure":
        return []
    findings: list[Finding] = []
    if e.get("judgment") != "RETRIEVAL_FAILED":
        findings.append(Finding("INV-14", f"audit_tool_failure row has judgment={e.get('judgment')!r}"))
    if e.get("audit_status") != "inconclusive":
        findings.append(Finding("INV-14", f"audit_tool_failure row has audit_status={e.get('audit_status')!r}"))
    if e.get("defect_stage") != "not_applicable":
        findings.append(Finding("INV-14", f"audit_tool_failure row has defect_stage={e.get('defect_stage')!r}"))
    rationale = e.get("rationale") or ""
    if not any(rationale.startswith(f"{tag}:") for tag in INV14_FAULT_CLASS_TAGS):
        findings.append(
            Finding(
                "INV-14",
                f"audit_tool_failure rationale must begin with one of "
                f"{INV14_FAULT_CLASS_TAGS}+':' got {rationale[:60]!r}",
            )
        )
    return findings


def _check_inv_15(
    e: dict[str, Any],
    manifest_index: dict[str, set[str]],
) -> list[Finding]:
    """(scoped_manifest_id, claim_id) MUST resolve OR sentinel."""
    sm = e.get("scoped_manifest_id")
    cid = e.get("claim_id")
    if sm == SENTINEL_MANIFEST_ID:
        return []
    if sm not in manifest_index:
        return [
            Finding(
                "INV-15",
                f"dangling scoped_manifest_id={sm!r}; no matching claim_intent_manifests[] entry",
            )
        ]
    if cid not in manifest_index[sm]:
        return [
            Finding(
                "INV-15",
                f"(scoped_manifest_id={sm!r}, claim_id={cid!r}) pair not present in matching manifest",
            )
        ]
    return []


def _check_inv_16(e: dict[str, Any]) -> list[Finding]:
    """anchor_kind != none -> URL-decoded anchor_value non-empty after strip.

    Schema mandates non-empty after URL-decoding so URL-encoded whitespace
    (e.g. `%20`, `%09`) cannot bypass the firm rule. `.strip()` on the raw
    string would accept `"%20"` as a non-empty anchor; decoding first makes
    the check faithful to the contract.
    """
    kind = e.get("anchor_kind")
    if kind in (None, "none"):
        return []
    value = e.get("anchor_value")
    if not isinstance(value, str):
        return [
            Finding(
                "INV-16",
                f"anchor_kind={kind!r} has non-string anchor_value (type={type(value).__name__})",
            )
        ]
    if urllib.parse.unquote(value).strip() == "":
        return [
            Finding(
                "INV-16",
                f"anchor_kind={kind!r} has empty anchor_value (URL-decoded whitespace-only or missing)",
            )
        ]
    return []


def _check_inv_18(e: dict[str, Any]) -> list[Finding]:
    """(RETRIEVAL_FAILED, inconclusive, not_applicable) -> method in {not_attempted, failed, audit_tool_failure}."""
    triple = (e.get("judgment"), e.get("audit_status"), e.get("defect_stage"))
    if triple != ("RETRIEVAL_FAILED", "inconclusive", "not_applicable"):
        return []
    allowed = {"not_attempted", "failed", "audit_tool_failure"}
    method = e.get("ref_retrieval_method")
    if method not in allowed:
        return [
            Finding(
                "INV-18",
                f"(RETRIEVAL_FAILED, inconclusive, not_applicable) row has method={method!r}; must be one of {sorted(allowed)}",
            )
        ]
    return []


def _check_inv_19(e: dict[str, Any]) -> list[Finding]:
    """sub_claim_breakdown present -> normalized-PARTIAL shape pinned (#213).

    Presence of the breakdown is the machine-readable partial-support signal.
    When present it must pin the full B1 normalization: judgment=UNSUPPORTED,
    defect_stage=source_description, and the breakdown is *true-partial* —
    >=2 items with >=1 SUPPORTED AND >=1 non-SUPPORTED sub_verdict. The
    SUPPORTED-AND-non-SUPPORTED pair is what distinguishes a genuine partial
    from an all-supported or all-unsupported decomposition; "non-SUPPORTED
    alone" would wrongly admit an all-UNSUPPORTED breakdown.

    The "what counts as non-SUPPORTED" decision is the shared
    `_claim_audit_constants.SUBCLAIM_NON_SUPPORTED` constant (the literal most
    likely to drift) — `is_true_partial_breakdown` in that module is the bool
    form used by the runtime + calibration. This lint deliberately re-expresses
    the same mix test inline (rather than calling the bool helper) because it
    must emit two DISTINCT findings — "needs >=1 SUPPORTED" and "needs >=1
    non-SUPPORTED" — which a single bool cannot carry. The shared constant keeps
    the verdict set in sync; the granular split is lint-specific.
    """
    if "sub_claim_breakdown" not in e:
        return []
    bd = e["sub_claim_breakdown"]
    findings: list[Finding] = []
    if e.get("judgment") != "UNSUPPORTED":
        findings.append(
            Finding("INV-19", f"sub_claim_breakdown present but judgment={e.get('judgment')!r}; must be UNSUPPORTED")
        )
    if e.get("defect_stage") != "source_description":
        findings.append(
            Finding(
                "INV-19",
                f"sub_claim_breakdown present but defect_stage={e.get('defect_stage')!r}; must be source_description",
            )
        )
    if not isinstance(bd, list) or len(bd) < 2:
        findings.append(Finding("INV-19", "sub_claim_breakdown must have >=2 items (not a true partial)"))
        return findings
    verdicts = [item.get("sub_verdict") for item in _iter_dicts(bd)]
    # "non-SUPPORTED" counts only the *valid* opposing verdicts (the shared
    # SUBCLAIM_NON_SUPPORTED set). A missing or out-of-enum sub_verdict must NOT
    # be read as non-SUPPORTED — that would let `[SUPPORTED, <missing>]`
    # masquerade as true-partial (round-2 review #1). The granular split here is
    # equivalent to `is_true_partial_breakdown(bd)` but yields distinct findings.
    if not any(v == "SUPPORTED" for v in verdicts):
        findings.append(Finding("INV-19", "sub_claim_breakdown is not true-partial: needs >=1 SUPPORTED sub_verdict"))
    if not any(v in SUBCLAIM_NON_SUPPORTED for v in verdicts):
        findings.append(
            Finding("INV-19", "sub_claim_breakdown is not true-partial: needs >=1 non-SUPPORTED sub_verdict")
        )
    return findings


# INV-17 surfaces on malformed NC constraint ids encountered in manifests
# (schema also rejects the wrong shape; lint surfaces the explicit tag).
def _check_inv_17_for_manifest(manifest: dict[str, Any]) -> list[Finding]:
    findings: list[Finding] = []
    for claim in _iter_dicts(manifest.get("claims")):
        for nc in _iter_dicts(claim.get("negative_constraints")):
            cid_raw = nc.get("constraint_id", "")
            cid = cid_raw if isinstance(cid_raw, str) else ""
            if RE_NC_INNER_HYPHEN.match(cid):
                findings.append(
                    Finding(
                        "INV-17",
                        f"NC constraint_id={cid!r} uses NC-C-{{n}} form; canonical is NC-C{{n}}-{{m}} (no hyphen between C and digits)",
                    )
                )
    return findings


def _check_matrix(e: dict[str, Any]) -> list[Finding]:
    triple = (e.get("judgment"), e.get("audit_status"), e.get("defect_stage"))
    if triple not in ALLOWED_MATRIX:
        return [
            Finding(
                "matrix",
                f"triple {triple!r} not in §3.1 allowed (judgment, audit_status, defect_stage) matrix",
            )
        ]
    return []


# ---------------------------------------------------------------------------
# claim_intent_manifest invariants (M-INV-1..M-INV-4).
# ---------------------------------------------------------------------------


def _iter_dicts(value: Any) -> list[dict[str, Any]]:
    """Filter a nested 'list of dict' field to actual dict entries.

    Mirrors `_coerce_aggregate` (which protects top-level aggregates) at the
    nested level: invariant walkers that descend into `claims[]`,
    `negative_constraints[]`, `manifest_negative_constraints[]` etc. expect
    a list of dicts. Schema validation surfaces the type mismatch separately
    as a clean finding; this guard prevents the walker from crashing on a
    string-instead-of-list (`for claim in "broken":`) or a non-dict entry
    (`claim.get(...)`) so the CLI returns actionable lint findings rather
    than a traceback (#119 + #120 P2-2 — Step 13 R6 codex P2).
    """
    if not isinstance(value, list):
        return []
    return [e for e in value if isinstance(e, dict)]


def _check_manifest_invariants(manifests: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    # M-INV-4: manifest_id uniqueness across passport.
    # Skip non-string manifest_ids per v3.8.1 round 2 — schema records the
    # type mismatch separately; unhashable list/dict would crash this loop.
    seen_ids: dict[str, int] = {}
    for i, m in enumerate(manifests):
        mid = m.get("manifest_id")
        if not isinstance(mid, str):
            continue
        if mid in seen_ids:
            findings.append(
                Finding(
                    "M-INV-4",
                    f"duplicate manifest_id={mid!r} (also at claim_intent_manifests[{seen_ids[mid]}])",
                )
            )
        else:
            seen_ids[mid] = i

    for i, m in enumerate(manifests):
        # M-INV-1: claim_id uniqueness within one manifest.
        # Skip non-string claim_ids: schema validator records the type
        # mismatch separately; treating an unhashable list/dict as a dict
        # key here would raise TypeError and crash the lint instead of
        # returning actionable findings (codex round 2 P2 / v3.8.1).
        claim_ids: dict[str, int] = {}
        for j, claim in enumerate(_iter_dicts(m.get("claims"))):
            cid = claim.get("claim_id")
            if not isinstance(cid, str):
                continue
            if cid in claim_ids:
                findings.append(
                    Finding(
                        "M-INV-1",
                        f"duplicate claim_id={cid!r} within manifest_id={m.get('manifest_id')!r} "
                        f"(also at claims[{claim_ids[cid]}])",
                    )
                )
            else:
                claim_ids[cid] = j

        # M-INV-2: NC-C{n}-{m} must scope under a claims[] entry with C-{n}.
        for j, claim in enumerate(_iter_dicts(m.get("claims"))):
            cid_raw = claim.get("claim_id") or ""
            cid = cid_raw if isinstance(cid_raw, str) else ""
            cid_match = RE_CLAIM_ID.match(cid)
            cid_digits = cid_match.group(1) if cid_match else None
            for nc in _iter_dicts(claim.get("negative_constraints")):
                nc_id_raw = nc.get("constraint_id", "")
                nc_id = nc_id_raw if isinstance(nc_id_raw, str) else ""
                nc_match = RE_NC_CONSTRAINT.match(nc_id)
                if nc_match and nc_match.group(1) != cid_digits:
                    findings.append(
                        Finding(
                            "M-INV-2",
                            f"NC constraint_id={nc_id!r} scoped under claim_id={cid!r}; "
                            f"NC digits {nc_match.group(1)!r} must match claim digits {cid_digits!r}",
                        )
                    )

        # M-INV-3: claim-level NC cannot reuse an MNC-* id (only ADD via NC-C{n}-{m}).
        # Per spec §3.2: "claim-level can ADD via NC-C{n}-{m}, never via MNC-*" —
        # the check fires on any claim-level negative_constraint whose id matches
        # the MNC-* pattern, regardless of whether that exact id appears in
        # manifest_negative_constraints[]. (Previous revisions built an unused
        # `mnc_ids` set here that also crashed on schema-invalid unhashable
        # MNC ids — codex round 3 P2; removed in v3.8.1.)
        for j, claim in enumerate(_iter_dicts(m.get("claims"))):
            for nc in _iter_dicts(claim.get("negative_constraints")):
                nc_id_raw = nc.get("constraint_id", "")
                nc_id = nc_id_raw if isinstance(nc_id_raw, str) else ""
                if RE_MNC_CONSTRAINT.match(nc_id):
                    findings.append(
                        Finding(
                            "M-INV-3",
                            f"claim-level negative_constraint reuses MNC-* id={nc_id!r}; "
                            "claim-level can ADD via NC-C{n}-{m}, never via MNC-*",
                        )
                    )

        findings.extend(_check_inv_17_for_manifest(m))

    return findings


def _build_manifest_index(manifests: list[dict[str, Any]]) -> dict[str, set[str]]:
    """Build {manifest_id: {claim_id, ...}} for INV-15 / U-INV-4 / D-INV-2 / CV-INV-2 lookups."""
    index: dict[str, set[str]] = {}
    for m in manifests:
        mid = m.get("manifest_id")
        # #130: skip non-string manifest_id (list/dict would raise
        # TypeError: unhashable type on setdefault). Schema validator
        # already records the type mismatch as a separate finding;
        # the cross-field invariant pass just needs to walk past it.
        if not isinstance(mid, str) or not mid:
            continue
        index.setdefault(mid, set())
        for c in _iter_dicts(m.get("claims")):
            cid = c.get("claim_id")
            if isinstance(cid, str) and cid:
                index[mid].add(cid)
    return index


def _build_manifest_constraint_index(
    manifests: list[dict[str, Any]],
) -> dict[str, dict[str, dict[str, Any]]]:
    """Build {manifest_id: {constraint_id: {kind: 'MNC'|'NC', claim_id: C-{n}|None}}}.

    Used by CV-INV-2 to resolve violated_constraint_id against the active manifest.
    """
    out: dict[str, dict[str, dict[str, Any]]] = {}
    for m in manifests:
        mid = m.get("manifest_id")
        # #130: same guard as _build_manifest_index — non-string mid
        # would raise TypeError on `out[mid] = bucket` (unhashable).
        if not isinstance(mid, str) or not mid:
            continue
        bucket: dict[str, dict[str, Any]] = {}
        for mnc in _iter_dicts(m.get("manifest_negative_constraints")):
            cid = mnc.get("constraint_id")
            if isinstance(cid, str) and cid:
                bucket[cid] = {"kind": "MNC", "claim_id": None}
        for claim in _iter_dicts(m.get("claims")):
            parent = claim.get("claim_id")
            for nc in _iter_dicts(claim.get("negative_constraints")):
                cid = nc.get("constraint_id")
                if isinstance(cid, str) and cid:
                    bucket[cid] = {"kind": "NC", "claim_id": parent}
        out[mid] = bucket
    return out


# ---------------------------------------------------------------------------
# experiment provenance / alignment invariants (#260).
#   EP-INV-1  experiment_id unique within the passport
#   EP-INV-2  planned_experiment_ids[] resolve to an experiment_provenance entry
#             (doubles as the rename + forward-reference dangling-pointer guard)
#   EP-INV-3  planned_experiment_ids present => owning claim is empirical
#   EP-INV-4  experiment_intake_declaration <-> experiment_provenance symmetry
#   EP-INV-5  experiment_intake_declaration well-formedness when present
#             (status enum / declared_by==scholar / declared_at date-time)
#   EA-INV-1  experiment_alignment_results[].finding_id unique
#   EA-INV-2  alignment row (scoped_manifest_id, claim_id) + experiment_id resolve
# These are cross-array integrity checks that JSON Schema cannot express; they
# mirror the INV-15 / U-INV-4 (scoped_manifest_id, *) resolution pattern.
# ---------------------------------------------------------------------------


def _build_claim_detail_index(
    manifests: list[dict[str, Any]],
) -> dict[tuple[str, str], dict[str, Any]]:
    """Build {(manifest_id, claim_id): {evidence_kind, planned_experiment_ids}}.

    Used by EP-INV-3 (planned_experiment_ids => empirical) which needs the
    per-claim intended_evidence_kind, a field _build_manifest_index discards.
    """
    out: dict[tuple[str, str], dict[str, Any]] = {}
    for m in manifests:
        mid = m.get("manifest_id")
        if not isinstance(mid, str) or not mid:
            continue
        for c in _iter_dicts(m.get("claims")):
            cid = c.get("claim_id")
            if not isinstance(cid, str) or not cid:
                continue
            out[(mid, cid)] = {
                "intended_evidence_kind": c.get("intended_evidence_kind"),
                "planned_experiment_ids": c.get("planned_experiment_ids"),
            }
    return out


def _build_experiment_id_set(provenance: list[dict[str, Any]]) -> set[str]:
    """The set of well-formed experiment_id values across experiment_provenance[]."""
    ids: set[str] = set()
    for e in provenance:
        eid = e.get("experiment_id")
        if isinstance(eid, str) and eid:
            ids.add(eid)
    return ids


def _check_experiment_provenance_invariants(
    provenance: list[dict[str, Any]],
    manifests: list[dict[str, Any]],
    declaration: Any,
) -> list[Finding]:
    findings: list[Finding] = []

    # EP-INV-1: experiment_id unique within the passport.
    seen: dict[str, int] = {}
    for i, e in enumerate(provenance):
        eid = e.get("experiment_id")
        if not isinstance(eid, str) or not eid:
            continue  # schema-shape surfaces malformed/missing ids separately
        if eid in seen:
            findings.append(
                Finding("EP-INV-1", f"duplicate experiment_id={eid!r} (also at experiment_provenance[{seen[eid]}])")
            )
        else:
            seen[eid] = i

    experiment_ids = set(seen.keys())
    claim_detail = _build_claim_detail_index(manifests)

    # EP-INV-2 + EP-INV-3: walk each manifest claim's planned_experiment_ids.
    for (mid, cid), detail in claim_detail.items():
        planned = detail.get("planned_experiment_ids")
        if planned is None:
            continue  # optional-absent — nothing to check
        if not isinstance(planned, list):
            continue  # schema-shape surfaces the type error
        # EP-INV-2: every value resolves to exactly one provenance entry.
        for pid in planned:
            if not isinstance(pid, str):
                continue
            if pid not in experiment_ids:
                findings.append(
                    Finding(
                        "EP-INV-2",
                        f"planned_experiment_ids value {pid!r} on (manifest={mid!r}, claim={cid!r}) "
                        f"resolves to no experiment_provenance[] entry (dangling: rename-without-re-emit "
                        f"or writer ran ahead of intake)",
                    )
                )
        # EP-INV-3: presence => owning claim is empirical. Mixed evidence
        # (planned_refs AND planned_experiment_ids) is allowed — this only
        # forbids experiment ids on a non-empirical claim.
        kind = detail.get("intended_evidence_kind")
        if kind != "empirical":
            findings.append(
                Finding(
                    "EP-INV-3",
                    f"planned_experiment_ids present on (manifest={mid!r}, claim={cid!r}) but "
                    f"intended_evidence_kind={kind!r}; experiment ids require empirical (mixed "
                    f"literature+experiment is allowed, non-empirical is not)",
                )
            )

    # EP-INV-4: declaration <-> provenance symmetry. The deterministic
    # structural half of D7 FAIL conditions #2 and #3.
    status = None
    if isinstance(declaration, dict):
        status = declaration.get("status")
    has_provenance = len(provenance) > 0
    if status == "experiments_declared" and not has_provenance:
        findings.append(
            Finding(
                "EP-INV-4",
                "experiment_intake_declaration.status == experiments_declared but "
                "experiment_provenance[] is absent/empty",
            )
        )
    if status == "no_experiments_declared" and has_provenance:
        findings.append(
            Finding(
                "EP-INV-4",
                "experiment_intake_declaration.status == no_experiments_declared but "
                "experiment_provenance[] is non-empty (a populated array contradicts the declaration)",
            )
        )

    # EP-INV-5: when a declaration IS present, it must be well-formed. A
    # malformed declaration (bad status enum, wrong declared_by, missing/empty
    # declared_at) would otherwise pass silently — the symmetry checks above
    # only fire on the two known status literals, so `status: "garbage"` slips
    # through with no finding. This is the deterministic shape half of D7 the
    # symmetry check alone does not cover; it does NOT decide presence/absence
    # (the ars_version legacy gate, a Stage-1 gate check, owns that).
    if declaration is not None:
        if not isinstance(declaration, dict):
            findings.append(
                Finding(
                    "EP-INV-5",
                    f"experiment_intake_declaration must be a mapping; got {type(declaration).__name__}",
                )
            )
        else:
            allowed_status = {
                "experiments_declared",
                "no_experiments_declared",
                "legacy_unknown",
            }
            if status not in allowed_status:
                findings.append(
                    Finding(
                        "EP-INV-5",
                        f"experiment_intake_declaration.status={status!r} not in "
                        f"{sorted(allowed_status)}",
                    )
                )
            declared_by = declaration.get("declared_by")
            if declared_by != "scholar":
                findings.append(
                    Finding(
                        "EP-INV-5",
                        f"experiment_intake_declaration.declared_by={declared_by!r}; must be "
                        "'scholar' (an intake decision, never an agent emission)",
                    )
                )
            declared_at = declaration.get("declared_at")
            if not isinstance(declared_at, str) or not declared_at:
                findings.append(
                    Finding(
                        "EP-INV-5",
                        "experiment_intake_declaration.declared_at must be a non-empty "
                        f"date-time string; got {declared_at!r}",
                    )
                )

    return findings


def _check_experiment_alignment_invariants(
    entries: list[dict[str, Any]],
    manifest_index: dict[str, set[str]],
    experiment_ids: set[str],
) -> list[Finding]:
    findings: list[Finding] = []

    # EA-INV-1: finding_id uniqueness.
    seen: dict[str, int] = {}
    for i, e in enumerate(entries):
        fid = e.get("finding_id")
        if not isinstance(fid, str):
            continue
        if fid in seen:
            findings.append(
                Finding("EA-INV-1", f"duplicate finding_id={fid!r} (also at experiment_alignment_results[{seen[fid]}])")
            )
        else:
            seen[fid] = i

    # EA-INV-2: (scoped_manifest_id, claim_id) resolves to a real manifest claim
    # AND experiment_id resolves to a real experiment_provenance[] entry. A
    # dangling id is a structural FAIL here (and at EP-INV-2 from the manifest
    # side) — never represented as a judge verdict.
    for e in entries:
        fid = e.get("finding_id")
        smid = e.get("scoped_manifest_id")
        cid = e.get("claim_id")
        if not (isinstance(smid, str) and isinstance(cid, str)):
            continue  # schema-shape surfaces the type error
        if smid not in manifest_index or cid not in manifest_index[smid]:
            findings.append(
                Finding(
                    "EA-INV-2",
                    f"alignment row finding_id={fid!r} has ({smid!r}, {cid!r}) "
                    f"not present in any claim_intent_manifests[] entry",
                )
            )
        eid = e.get("experiment_id")
        if isinstance(eid, str) and eid and eid not in experiment_ids:
            findings.append(
                Finding(
                    "EA-INV-2",
                    f"alignment row finding_id={fid!r} references experiment_id={eid!r} "
                    f"with no matching experiment_provenance[] entry (structural FAIL, not a verdict)",
                )
            )

    return findings


# ---------------------------------------------------------------------------
# uncited_assertion invariants (U-INV-1..U-INV-4).
# ---------------------------------------------------------------------------


def _check_uncited_invariants(
    entries: list[dict[str, Any]],
    manifest_index: dict[str, set[str]],
) -> list[Finding]:
    findings: list[Finding] = []
    # U-INV-1: finding_id uniqueness. Non-string ids skipped per v3.8.1 round 2.
    seen: dict[str, int] = {}
    for i, e in enumerate(entries):
        fid = e.get("finding_id")
        if not isinstance(fid, str):
            continue
        if fid in seen:
            findings.append(
                Finding("U-INV-1", f"duplicate finding_id={fid!r} (also at uncited_assertions[{seen[fid]}])")
            )
        else:
            seen[fid] = i

    for e in entries:
        # U-INV-2: trigger_tokens non-empty (schema also enforces minItems=1).
        tokens = e.get("trigger_tokens", [])
        if not isinstance(tokens, list) or len(tokens) == 0:
            findings.append(Finding("U-INV-2", f"empty trigger_tokens on finding_id={e.get('finding_id')!r}"))

        # U-INV-3: rule_version literal.
        if e.get("rule_version") != "D4-c-v1":
            findings.append(
                Finding(
                    "U-INV-3",
                    f"rule_version={e.get('rule_version')!r} on finding_id={e.get('finding_id')!r}; must equal D4-c-v1",
                )
            )

        # U-INV-4: cross-array integrity.
        mcid = e.get("manifest_claim_id")
        smid = e.get("scoped_manifest_id")
        if mcid is None and smid is None:
            continue
        if mcid is not None and smid is None:
            findings.append(
                Finding(
                    "U-INV-4",
                    f"manifest_claim_id set but scoped_manifest_id null on finding_id={e.get('finding_id')!r}",
                )
            )
            continue
        if mcid is None and smid is not None:
            findings.append(
                Finding(
                    "U-INV-4",
                    f"scoped_manifest_id set but manifest_claim_id null on finding_id={e.get('finding_id')!r}",
                )
            )
            continue
        # Both non-null: must resolve.
        if smid not in manifest_index or mcid not in manifest_index[smid]:
            findings.append(
                Finding(
                    "U-INV-4",
                    f"dangling ({smid!r}, {mcid!r}) on finding_id={e.get('finding_id')!r}",
                )
            )

    return findings


# ---------------------------------------------------------------------------
# claim_drift invariants (D-INV-1..D-INV-4).
# ---------------------------------------------------------------------------


def _check_drift_invariants(
    entries: list[dict[str, Any]],
    uncited_entries: list[dict[str, Any]],
    manifest_index: dict[str, set[str]],
) -> list[Finding]:
    findings: list[Finding] = []

    # D-INV-1: finding_id uniqueness. Non-string ids skipped per v3.8.1 round 2.
    seen: dict[str, int] = {}
    for i, e in enumerate(entries):
        fid = e.get("finding_id")
        if not isinstance(fid, str):
            continue
        if fid in seen:
            findings.append(
                Finding("D-INV-1", f"duplicate finding_id={fid!r} (also at claim_drifts[{seen[fid]}])")
            )
        else:
            seen[fid] = i

    for e in entries:
        kind = e.get("drift_kind")
        mcid = e.get("manifest_claim_id")
        smid = e.get("scoped_manifest_id")
        section = e.get("section_path")
        fid = e.get("finding_id")

        # D-INV-2 by drift_kind.
        if kind == "INTENDED_NOT_EMITTED":
            if mcid is None or smid is None:
                findings.append(
                    Finding(
                        "D-INV-2",
                        f"INTENDED_NOT_EMITTED finding_id={fid!r} missing manifest_claim_id/scoped_manifest_id",
                    )
                )
            else:
                if smid not in manifest_index or mcid not in manifest_index[smid]:
                    findings.append(
                        Finding(
                            "D-INV-2",
                            f"INTENDED_NOT_EMITTED finding_id={fid!r}: dangling ({smid!r}, {mcid!r})",
                        )
                    )
        elif kind == "EMITTED_NOT_INTENDED":
            if mcid is not None or smid is not None:
                findings.append(
                    Finding(
                        "D-INV-2",
                        f"EMITTED_NOT_INTENDED finding_id={fid!r} has non-null manifest_claim_id/scoped_manifest_id",
                    )
                )
            if not section:
                findings.append(
                    Finding(
                        "D-INV-2",
                        f"EMITTED_NOT_INTENDED finding_id={fid!r} missing section_path",
                    )
                )

        # D-INV-3: rule_version literal.
        if e.get("rule_version") != "D4-a-v1":
            findings.append(
                Finding(
                    "D-INV-3",
                    f"rule_version={e.get('rule_version')!r} on finding_id={fid!r}; must equal D4-a-v1",
                )
            )

    # D-INV-4: a sentence cannot appear in BOTH uncited_assertions[] AND claim_drifts[].
    uncited_texts = {u.get("sentence_text") for u in uncited_entries if u.get("sentence_text")}
    for e in entries:
        text = e.get("claim_text")
        if text and text in uncited_texts:
            findings.append(
                Finding(
                    "D-INV-4",
                    f"finding_id={e.get('finding_id')!r}: claim_text overlaps with an uncited_assertion sentence",
                )
            )

    return findings


# ---------------------------------------------------------------------------
# constraint_violation invariants (CV-INV-1..CV-INV-4).
# ---------------------------------------------------------------------------


def _check_constraint_violation_invariants(
    entries: list[dict[str, Any]],
    constraint_index: dict[str, dict[str, dict[str, Any]]],
) -> list[Finding]:
    findings: list[Finding] = []

    # CV-INV-1: finding_id uniqueness. Non-string ids skipped per v3.8.1 round 2.
    seen: dict[str, int] = {}
    for i, e in enumerate(entries):
        fid = e.get("finding_id")
        if not isinstance(fid, str):
            continue
        if fid in seen:
            findings.append(
                Finding(
                    "CV-INV-1",
                    f"duplicate finding_id={fid!r} (also at constraint_violations[{seen[fid]}])",
                )
            )
        else:
            seen[fid] = i

    # CV-INV-4: a sentence MUST NOT appear in constraint_violations[] more than once
    # per (scoped_manifest_id, section_path, claim_text_hash, violated_constraint_id).
    # Step 13 R8 codex P2-1: scope dedupe by manifest_id so two manifests in the
    # same passport carrying colliding MNC-* / NC-* ids — each legitimately
    # violated on the same sentence text — do not false-positive as duplicates.
    # M-INV-4 permits manifest_id uniqueness across passport but constraint_id
    # uniqueness only within a manifest; dedupe must respect the same scope.
    # v3.8.1 round 2: coerce each key component to str so schema-invalid
    # non-string values (lists/dicts) don't crash hashlib.encode() or hash().
    def _safe_str(value: Any) -> str:
        return value if isinstance(value, str) else ""

    dedup: dict[tuple[str, str, str, str], int] = {}
    for i, e in enumerate(entries):
        key = (
            _safe_str(e.get("scoped_manifest_id")),
            _safe_str(e.get("section_path")),
            hashlib.sha256(_safe_str(e.get("claim_text")).encode("utf-8")).hexdigest(),
            _safe_str(e.get("violated_constraint_id")),
        )
        if key in dedup:
            findings.append(
                Finding(
                    "CV-INV-4",
                    f"finding_id={e.get('finding_id')!r}: duplicate (manifest, section, claim, constraint) with constraint_violations[{dedup[key]}]",
                )
            )
        else:
            dedup[key] = i

    for e in entries:
        cid = e.get("violated_constraint_id") or ""
        smid = e.get("scoped_manifest_id")
        mcid = e.get("manifest_claim_id")
        fid = e.get("finding_id")

        # CV-INV-2: (scoped_manifest_id, violated_constraint_id) MUST resolve.
        if smid not in constraint_index or cid not in constraint_index.get(smid, {}):
            findings.append(
                Finding(
                    "CV-INV-2",
                    f"finding_id={fid!r}: ({smid!r}, {cid!r}) not present in any manifest's constraint set",
                )
            )
        else:
            # CV-INV-2 (NC variant): manifest_claim_id MUST equal the C-{n} extracted from NC id.
            slot = constraint_index[smid][cid]
            if slot["kind"] == "NC":
                expected_claim = slot["claim_id"]
                if mcid != expected_claim:
                    findings.append(
                        Finding(
                            "CV-INV-2",
                            f"finding_id={fid!r}: NC violated_constraint_id={cid!r} scopes claim_id={expected_claim!r}, "
                            f"but manifest_claim_id={mcid!r}",
                        )
                    )

        # CV-INV-3: MNC -> manifest_claim_id null; NC -> manifest_claim_id non-null and matches.
        mnc_match = RE_MNC_CONSTRAINT.match(cid)
        nc_match = RE_NC_CONSTRAINT.match(cid)
        if mnc_match and mcid is not None:
            findings.append(
                Finding(
                    "CV-INV-3",
                    f"finding_id={fid!r}: MNC-* constraint with non-null manifest_claim_id={mcid!r}",
                )
            )
        if nc_match:
            expected_digits = nc_match.group(1)
            if mcid is None:
                findings.append(
                    Finding(
                        "CV-INV-3",
                        f"finding_id={fid!r}: NC-* constraint with null manifest_claim_id",
                    )
                )
            else:
                mcid_match = RE_CLAIM_ID.match(mcid)
                actual_digits = mcid_match.group(1) if mcid_match else None
                if actual_digits != expected_digits:
                    findings.append(
                        Finding(
                            "CV-INV-3",
                            f"finding_id={fid!r}: NC digits {expected_digits!r} vs manifest_claim_id digits {actual_digits!r}",
                        )
                    )

    return findings


# ---------------------------------------------------------------------------
# uncited_audit_failure invariants (UAF-INV-1..UAF-INV-6) — v3.8.2 / #118.
# Surfaces transient judge outages on the uncited path that pre-v3.8.2 were
# silently substituted as NOT_VIOLATED. Mirrors INV-14 semantics on the
# cited path but uses a dedicated aggregate because claim_audit_result.ref_slug
# is required. See docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md §3.6.
# ---------------------------------------------------------------------------


def _check_uaf_invariants(
    entries: list[dict[str, Any]],
    violations: list[dict[str, Any]],
    manifest_index: dict[str, set[str]],
) -> list[Finding]:
    findings: list[Finding] = []

    def _safe_str(value: Any) -> str:
        return value if isinstance(value, str) else ""

    # UAF-INV-1: finding_id uniqueness. Non-string ids skipped per v3.8.1 round 2
    # hardening pattern; schema validator surfaces type mismatch separately.
    seen: dict[str, int] = {}
    for i, e in enumerate(entries):
        fid = e.get("finding_id")
        if not isinstance(fid, str):
            continue
        if fid in seen:
            findings.append(
                Finding(
                    "UAF-INV-1",
                    f"duplicate finding_id={fid!r} (also at uncited_audit_failures[{seen[fid]}])",
                )
            )
        else:
            seen[fid] = i

    # UAF-INV-4: per-(sentence, manifest) dedup with key
    # (scoped_manifest_id, section_path, claim_text_hash). Two manifests both
    # failing on the same sentence text emit two distinct rows legitimately
    # (cross-manifest scope mirrors CV-INV-4).
    dedup: dict[tuple[str, str, str], int] = {}
    for i, e in enumerate(entries):
        key = (
            _safe_str(e.get("scoped_manifest_id")),
            _safe_str(e.get("section_path")),
            hashlib.sha256(_safe_str(e.get("claim_text")).encode("utf-8")).hexdigest(),
        )
        if key in dedup:
            findings.append(
                Finding(
                    "UAF-INV-4",
                    f"finding_id={e.get('finding_id')!r}: duplicate (manifest, section, claim) with uncited_audit_failures[{dedup[key]}]",
                )
            )
        else:
            dedup[key] = i

    for e in entries:
        fid = e.get("finding_id")
        smid = e.get("scoped_manifest_id")
        mcid = e.get("manifest_claim_id")
        rationale = e.get("rationale") or ""
        row_fault = e.get("fault_class")

        # UAF-INV-2: scoped_manifest_id cross-array integrity.
        manifest_resolved = isinstance(smid, str) and smid in manifest_index
        if not manifest_resolved:
            findings.append(
                Finding(
                    "UAF-INV-2",
                    f"finding_id={fid!r}: scoped_manifest_id={smid!r} not present in claim_intent_manifests[]",
                )
            )
            # Don't `continue` here — UAF-INV-5 (rationale prefix) is
            # orthogonal to manifest integrity and we want both findings
            # to surface together so the user fixes both in one pass
            # (Gemini cross-model review P1, 2026-05-17).

        # UAF-INV-3: (scoped_manifest_id, manifest_claim_id) pair integrity
        # when manifest_claim_id is non-null. Null is legitimate when the
        # failure was against MNCs only (no claim binding). Skip when the
        # manifest itself failed to resolve — the pair check would
        # otherwise always fire and double-report the same root cause.
        # Guard `mcid` with isinstance(str) before set membership: a
        # malformed passport with mcid as list/dict (schema flags this
        # separately) would raise TypeError in `mcid not in ...` and crash
        # the lint instead of returning a clean finding. Mirrors the v3.8.1
        # round-2 hardening pattern (Codex R2 P2-2, 2026-05-17).
        if manifest_resolved and mcid is not None and isinstance(mcid, str):
            claim_ids = manifest_index.get(smid, set())
            if mcid not in claim_ids:
                findings.append(
                    Finding(
                        "UAF-INV-3",
                        f"finding_id={fid!r}: (scoped_manifest_id={smid!r}, manifest_claim_id={mcid!r}) not present in any manifest's claims[]",
                    )
                )

        # UAF-INV-5: rationale MUST begin with this row's own fault_class
        # value followed by ":" (and " <detail>" when JudgeInvocationError
        # carried a non-empty detail). Mirrors INV-14 rationale prefix on
        # the cited path. We check against the row's fault_class field
        # (not any known tag) so a row with fault_class judge_timeout but
        # rationale starting with "judge_api_error: ..." still trips this
        # invariant — the prefix must match the row.
        # Guard `rationale` with isinstance(str): the row's raw rationale
        # may be list/dict on a malformed passport — schema flags it
        # separately and we should skip cleanly rather than crash on
        # `.startswith()` (Codex R2 P2-3, 2026-05-17). The `or ""`
        # initialization above only fallbacks on None/empty-string falsy
        # values; a truthy dict/list slips through and needs this guard.
        if (
            isinstance(row_fault, str)
            and row_fault in INV14_FAULT_CLASS_TAGS
            and isinstance(rationale, str)
        ):
            expected_prefix = f"{row_fault}:"
            if not rationale.startswith(expected_prefix):
                findings.append(
                    Finding(
                        "UAF-INV-5",
                        f"finding_id={fid!r}: rationale must begin with {expected_prefix!r} got {rationale[:60]!r}",
                    )
                )

    # UAF-INV-6: cross-aggregate exclusivity with constraint_violations[].
    # A sentence MUST NOT appear in both UAF and CV for the same
    # (scoped_manifest_id, section_path, claim_text_hash). VIOLATED (positive
    # verdict) and audit_tool_failure (no verdict) are mutually exclusive
    # verdict states at per-(sentence, manifest) level.
    cv_keys: set[tuple[str, str, str]] = set()
    for cv in violations:
        cv_keys.add(
            (
                _safe_str(cv.get("scoped_manifest_id")),
                _safe_str(cv.get("section_path")),
                hashlib.sha256(_safe_str(cv.get("claim_text")).encode("utf-8")).hexdigest(),
            )
        )
    for uaf in entries:
        key = (
            _safe_str(uaf.get("scoped_manifest_id")),
            _safe_str(uaf.get("section_path")),
            hashlib.sha256(_safe_str(uaf.get("claim_text")).encode("utf-8")).hexdigest(),
        )
        if key in cv_keys:
            findings.append(
                Finding(
                    "UAF-INV-6",
                    f"finding_id={uaf.get('finding_id')!r}: (manifest, section, claim) overlaps a constraint_violations[] row — UAF and CV are mutually exclusive verdict states",
                )
            )

    return findings


# ---------------------------------------------------------------------------
# audit_sampling_summary invariants (S-INV-1..S-INV-4).
# ---------------------------------------------------------------------------


def _check_sampling_invariants(entries: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    for e in entries:
        indices = e.get("audited_indices", []) or []
        count = e.get("audited_count")
        cap = e.get("max_claims_per_paper")
        total = e.get("total_citation_count")
        run_id = e.get("audit_run_id")

        # S-INV-1: audited_count == |audited_indices|.
        if isinstance(indices, list) and count != len(indices):
            findings.append(
                Finding(
                    "S-INV-1",
                    f"audit_run_id={run_id!r}: audited_count={count!r} != len(audited_indices)={len(indices)}",
                )
            )

        # S-INV-2: count ≤ cap AND count ≤ total.
        if isinstance(count, int):
            if isinstance(cap, int) and count > cap:
                findings.append(
                    Finding(
                        "S-INV-2",
                        f"audit_run_id={run_id!r}: audited_count={count} > max_claims_per_paper={cap}",
                    )
                )
            if isinstance(total, int) and count > total:
                findings.append(
                    Finding(
                        "S-INV-2",
                        f"audit_run_id={run_id!r}: audited_count={count} > total_citation_count={total}",
                    )
                )

        # S-INV-4: strictly ascending, no duplicates. Guard against mixed-type
        # indices (#119 R6 codex P2 + Step 13 R8 P2-2) — schema records the
        # type mismatch separately; if a non-int slips through we skip the
        # comparison rather than raising TypeError on `<=` between str and int.
        if isinstance(indices, list):
            for i in range(1, len(indices)):
                a, b = indices[i - 1], indices[i]
                if not (isinstance(a, int) and isinstance(b, int)):
                    continue
                if b <= a:
                    findings.append(
                        Finding(
                            "S-INV-4",
                            f"audit_run_id={run_id!r}: audited_indices not strictly ascending at position {i} "
                            f"({a!r} -> {b!r})",
                        )
                    )
                    break

    return findings


# ---------------------------------------------------------------------------
# Schema-shape validation (rule 1).
# ---------------------------------------------------------------------------


def _validate_against_schema(
    entries: Any,
    schema_key: str,
    aggregate_label: str,
) -> list[Finding]:
    """Validate every entry against the named schema.

    Accepts `Any` rather than `Iterable[dict]` because callers may hand us a
    malformed passport — `entries` could be non-list, or a list with
    non-dict elements. Both must surface as a clean schema finding rather
    than a TypeError / AttributeError traceback (Step 13 R4 codex P2 #4).
    """
    findings: list[Finding] = []
    if not isinstance(entries, list):
        findings.append(
            Finding(
                "schema",
                f"{aggregate_label}: aggregate must be a JSON array; got {type(entries).__name__}",
            )
        )
        return findings
    validator = _validator(schema_key)
    for i, entry in enumerate(entries):
        if not isinstance(entry, dict):
            findings.append(
                Finding(
                    "schema",
                    f"{aggregate_label}[{i}]: entry must be a JSON object; got {type(entry).__name__}",
                )
            )
            continue
        for err in validator.iter_errors(entry):
            findings.append(
                Finding(
                    "schema",
                    f"{aggregate_label}[{i}] {'.'.join(str(p) for p in err.absolute_path) or '<root>'}: {err.message}",
                )
            )
    return findings


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def validate_passport(body: Any) -> list[Finding]:
    """Run all 39 invariants + schema-shape against a passport body. Returns findings."""
    # Step 13 R7 codex P3: a syntactically valid JSON top level can still
    # be `[]`, `null`, or a scalar. `.get()` on those raises AttributeError;
    # surface a clean schema finding instead so the CLI can return findings
    # rather than tracing back.
    if not isinstance(body, dict):
        return [
            Finding(
                "schema",
                f"passport body must be a JSON object; got {type(body).__name__}",
            )
        ]
    # Raw aggregates — preserved for schema-shape validation below (which
    # records findings on non-list / non-dict-entry inputs). MUST NOT use
    # `or []` because a falsey but malformed value such as `{}`, `null`, `0`,
    # or `""` would silently be replaced with an empty list and bypass the
    # schema gate (Step 13 R5 codex P2 #1). Only a missing key falls back to
    # the empty-list default.
    manifests_raw = body.get("claim_intent_manifests", [])
    results_raw = body.get("claim_audit_results", [])
    uncited_raw = body.get("uncited_assertions", [])
    drifts_raw = body.get("claim_drifts", [])
    violations_raw = body.get("constraint_violations", [])
    samplings_raw = body.get("audit_sampling_summaries", [])
    uaf_raw = body.get("uncited_audit_failures", [])
    provenance_raw = body.get("experiment_provenance", [])  # #260
    alignment_raw = body.get("experiment_alignment_results", [])  # #260
    declaration = body.get("experiment_intake_declaration")  # #260 (object | None)

    def _coerce_aggregate(value: Any) -> list[dict[str, Any]]:
        """Reduce an aggregate to a list of dict entries.

        Schema-shape failures are surfaced separately by
        `_validate_against_schema` against the raw aggregate. The dict-only
        invariant loops below attempt `.get()` / dictionary indexing —
        passing a non-list or a list with non-dict entries would raise
        AttributeError and crash the lint with a traceback instead of
        returning a clean failure finding (Step 13 R4 codex P2 #4).
        """
        if not isinstance(value, list):
            return []
        return [e for e in value if isinstance(e, dict)]

    manifests = _coerce_aggregate(manifests_raw)
    results = _coerce_aggregate(results_raw)
    uncited = _coerce_aggregate(uncited_raw)
    drifts = _coerce_aggregate(drifts_raw)
    violations = _coerce_aggregate(violations_raw)
    samplings = _coerce_aggregate(samplings_raw)
    uaf = _coerce_aggregate(uaf_raw)
    provenance = _coerce_aggregate(provenance_raw)  # #260
    alignment = _coerce_aggregate(alignment_raw)  # #260

    findings: list[Finding] = []

    # Schema-shape — gives the lint a chance to surface malformed entries with
    # an actionable rendering before cross-field checks fan out spurious tags.
    findings.extend(_validate_against_schema(manifests_raw, "claim_intent_manifest", "claim_intent_manifests"))
    findings.extend(_validate_against_schema(results_raw, "claim_audit_result", "claim_audit_results"))
    findings.extend(_validate_against_schema(uncited_raw, "uncited_assertion", "uncited_assertions"))
    findings.extend(_validate_against_schema(drifts_raw, "claim_drift", "claim_drifts"))
    findings.extend(_validate_against_schema(violations_raw, "constraint_violation", "constraint_violations"))
    findings.extend(_validate_against_schema(samplings_raw, "audit_sampling_summary", "audit_sampling_summaries"))
    findings.extend(_validate_against_schema(uaf_raw, "uncited_audit_failure", "uncited_audit_failures"))
    findings.extend(_validate_against_schema(provenance_raw, "experiment_provenance_entry", "experiment_provenance"))
    findings.extend(_validate_against_schema(alignment_raw, "experiment_alignment_result", "experiment_alignment_results"))

    # Manifest invariants + index for downstream cross-array checks.
    findings.extend(_check_manifest_invariants(manifests))
    manifest_index = _build_manifest_index(manifests)
    constraint_index = _build_manifest_constraint_index(manifests)

    # claim_audit_result invariants.
    for e in results:
        findings.extend(_check_inv_1(e))
        findings.extend(_check_inv_2(e))
        findings.extend(_check_inv_3(e))
        findings.extend(_check_inv_4(e))
        findings.extend(_check_inv_5(e))
        findings.extend(_check_inv_6(e))
        findings.extend(_check_inv_7(e))
        findings.extend(_check_inv_8(e))
        findings.extend(_check_inv_9(e))
        findings.extend(_check_inv_10(e))
        findings.extend(_check_inv_11(e))
        findings.extend(_check_inv_12(e))
        findings.extend(_check_inv_13(e))
        findings.extend(_check_inv_14(e))
        findings.extend(_check_inv_15(e, manifest_index))
        findings.extend(_check_inv_16(e))
        findings.extend(_check_inv_18(e))
        findings.extend(_check_inv_19(e))
        findings.extend(_check_matrix(e))

    findings.extend(_check_uncited_invariants(uncited, manifest_index))
    findings.extend(_check_drift_invariants(drifts, uncited, manifest_index))
    findings.extend(_check_constraint_violation_invariants(violations, constraint_index))
    findings.extend(_check_sampling_invariants(samplings))
    findings.extend(_check_uaf_invariants(uaf, violations, manifest_index))

    # #260 experiment provenance / alignment cross-array invariants.
    findings.extend(_check_experiment_provenance_invariants(provenance, manifests, declaration))
    experiment_ids = _build_experiment_id_set(provenance)
    findings.extend(_check_experiment_alignment_invariants(alignment, manifest_index, experiment_ids))

    return findings


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument(
        "--passport",
        type=Path,
        required=True,
        help="Path to a passport-shaped JSON containing the six aggregates the lint reads.",
    )
    args = p.parse_args(argv)

    if not args.passport.is_file():
        print(f"passport not found: {args.passport}", file=sys.stderr)
        return 2

    try:
        body = json.loads(args.passport.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"malformed JSON in {args.passport}: {exc}", file=sys.stderr)
        return 2

    try:
        findings = validate_passport(body)
    except FileNotFoundError as exc:
        print(f"internal: {exc}", file=sys.stderr)
        return 2

    if not findings:
        return 0

    for f in findings:
        print(f.render())
    return 1


if __name__ == "__main__":
    sys.exit(main())
