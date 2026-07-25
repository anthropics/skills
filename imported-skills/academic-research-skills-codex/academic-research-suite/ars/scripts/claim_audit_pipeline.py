"""claim_audit_pipeline — Python implementation of the §4 Step 1-6 pipeline.

This module is the executable face of `claim_ref_alignment_audit_agent.md`.
The agent prompt narrates the pipeline contract; this module runs it
under test so cross-field invariants and emission routing can be pinned
without dispatching the agent to a live model.

Retrieval and judge invocation are dependency-injected (`retrieve_fn` /
`judge_fn`) so tests can drive every error and decision path — paywall,
audit_tool_failure, not_found, SUPPORTED, UNSUPPORTED with each
defect_stage hint, VIOLATED. Production callers wire these to real
retrieval/judge clients in their own dispatch layer.

The full spec is in
docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md §4-§5.
"""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Callable

# Allow both CLI invocations (`python3 scripts/claim_audit_pipeline.py`) AND
# package-style invocations (`python -m unittest scripts.test_*`) to resolve
# the shared constants module via the same import.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _claim_audit_constants import (  # noqa: E402
    DRIFT_RULE_VERSION,
    INV6_RATIONALE_PREFIX,
    JUDGE_PROMPT_SHA256,
    RE_NC_CONSTRAINT,
    SAMPLING_STRATEGY,
    SENTINEL_MANIFEST_ID,
    UAF_RULE_VERSION,
    UNCITED_RULE_VERSION,
    is_emittable_partial_breakdown,
)

# Permitted UNSUPPORTED defect_stages for non-constraint paths (§3.1 matrix).
_UNSUPPORTED_NON_CONSTRAINT_DEFECTS = {
    "source_description",
    "metadata",
    "citation_anchor",
    "synthesis_overclaim",
}

# Permitted AMBIGUOUS defect_stages (§3.1 matrix).
_AMBIGUOUS_DEFECTS = {"source_description", "citation_anchor", "synthesis_overclaim", None}


# ---------------------------------------------------------------------------
# Cache helpers.
# ---------------------------------------------------------------------------


def _stable_json(value: Any) -> str:
    """JCS-style canonicalization sufficient for cache-key hashing."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _hash_text(text: str | None) -> str:
    return hashlib.sha256((text or "").encode("utf-8")).hexdigest()


# claim_audit_result.rationale schema maxLength (#355 P2#3). A judge/retrieval
# failure detail that embeds the offending payload's repr must fit here, or the
# "clean inconclusive" fallback row it produces is itself schema-invalid. Every
# JudgeInvocationError / RetrievalInvocationError detail ends up in a row's
# rationale via `f"{fault_class}: {detail}"`, so the bound lives in those
# exceptions' constructors (single choke point) rather than at each raise site.
_RATIONALE_MAX_LEN = 2000
_RATIONALE_TRUNC_MARK = "…[truncated]"
# Widest fault-class prefix across both exception families ("retrieval_network_error: ").
_WIDEST_FAULT_PREFIX = "retrieval_network_error: "


def _clamp_to_rationale_budget(text: str, *, reserved: int) -> str:
    """Clamp `text` so that `reserved + len(result)` fits the rationale maxLength.

    Single length-budgeting choke point for every untrusted string that lands in
    a row's `rationale` (#355 P2#3 / #360). `reserved` is the number of chars the
    caller will prepend before this text reaches the rationale field:

    - Failure paths emit ``f"{fault_class}: {detail}"`` → reserved = widest
      fault-class prefix width, so the worst-case composed rationale still fits.
    - Success paths copy a judge's own `rationale` verbatim onto the row → no
      prefix → reserved = 0.

    Truncation preserves the diagnostic head (which says WHAT the string is) and
    marks the dropped tail, so a short string that already fits passes through
    byte-for-byte.
    """
    budget = _RATIONALE_MAX_LEN - reserved
    if len(text) <= budget:
        return text
    keep = budget - len(_RATIONALE_TRUNC_MARK)
    return text[:keep] + _RATIONALE_TRUNC_MARK


def _bounded_failure_detail(message: str) -> str:
    """Clamp a failure detail so ``f"{fault_class}: {detail}"`` fits the maxLength.

    A malformed payload's repr embedded in `message` (a >1000-char
    sub_claim_text, an over-decomposed breakdown, a giant non-string
    judgment/method) can push the detail past the rationale maxLength, making the
    fallback row schema-invalid (#355 P2#3). Budgets against the widest
    fault-class prefix so the composed rationale fits for every fault class.
    """
    return _clamp_to_rationale_budget(message, reserved=len(_WIDEST_FAULT_PREFIX))


def _bounded_judge_rationale(rationale: Any) -> str:
    """Clamp a judge-supplied `rationale` copied verbatim onto a SUCCESS-path row.

    The judge is an LLM with no pre-emission length guarantee; an over-long
    `rationale` makes a *clean* completed / constraint_violation row
    schema-invalid (#360 — the success-path parallel to the #359 fallback fix).
    No fault-class prefix is prepended on the success path, so reserved = 0.

    `_validate_judge_dict` only checks that the `rationale` key is present, not
    that its value is a string — a JSON-null (or otherwise non-string) rationale
    passes that gate. Return "" for a non-string value so each caller's existing
    fallback (`... or "(no rationale provided)"` / the constraint default) takes
    over, rather than calling len() on it and aborting the audit run.
    """
    if not isinstance(rationale, str):
        return ""
    return _clamp_to_rationale_budget(rationale, reserved=0)


def _active_constraints_for_claim(
    *,
    scoped_manifest_id: str,
    claim_id: str,
    claim_by_mc_id: dict[tuple[str, str], dict[str, Any]],
    mncs_by_manifest_id: dict[str, list[dict[str, Any]]],
) -> list[dict[str, Any]]:
    """Return the manifest-scoped + claim-scoped negative-constraint set for a citation.

    Reads from pre-built indexes (built once per audit run in
    `run_audit_pipeline`) instead of rescanning the manifest tree per
    citation — at realistic workloads (~150 citations × ~100 manifest
    claims) that saves ~30k Python ops per run with no behavioral delta.
    """
    constraints: list[dict[str, Any]] = []
    for mnc in mncs_by_manifest_id.get(scoped_manifest_id, []):
        constraints.append({"constraint_id": mnc["constraint_id"], "rule": mnc["rule"], "scope": "MNC"})
    claim = claim_by_mc_id.get((scoped_manifest_id, claim_id))
    if claim is not None:
        for nc in claim.get("negative_constraints", []) or []:
            constraints.append(
                {"constraint_id": nc["constraint_id"], "rule": nc["rule"], "scope": "NC"}
            )
    constraints.sort(key=lambda c: c["constraint_id"])
    return constraints


def _cache_key(
    *,
    claim_text: str,
    ref_slug: str,
    anchor_kind: str,
    anchor_value: str,
    retrieved_excerpt: str | None,
    active_constraints: list[dict[str, Any]],
    judge_model: str,
    prompt_version: str,
) -> str:
    payload = {
        "claim_text_hash": _hash_text(claim_text),
        "ref_slug": ref_slug,
        "anchor_kind": anchor_kind,
        "anchor_value_hash": _hash_text(anchor_value),
        "retrieved_excerpt_hash": _hash_text(retrieved_excerpt),
        "active_constraints_hash": _hash_text(
            _stable_json([{"constraint_id": c["constraint_id"], "rule": c["rule"]} for c in active_constraints])
        ),
        "judge_model": judge_model,
        # #361: a judge-prompt revision partitions the keyspace — a verdict
        # cached under one prompt is never served against new prompt logic.
        # judge_model and prompt_version stay separate components (independent
        # axes of judge behavior).
        "prompt_version": prompt_version,
    }
    return hashlib.sha256(_stable_json(payload).encode("utf-8")).hexdigest()


# ---------------------------------------------------------------------------
# Judge + retrieval invocation — wraps callables so transient failures become
# INV-14 audit_tool_failure rows instead of aborting the audit. Spec §4 step 2
# + INV-14 + Step 13 R1+R2 codex findings (transient errors on either external
# call must surface as MED-WARN advisory rows).
# ---------------------------------------------------------------------------

# Legal judge verdicts per path. claim_audit_result schema enum + constraint-side
# verdicts (VIOLATED / NOT_VIOLATED). Cited and uncited paths route different
# subsets — passing path-specific allow-lists into `_invoke_judge` rejects an
# off-path verdict at the invocation boundary instead of letting it propagate
# into _judge_result_entry where the ValueError would abort the audit
# (Step 13 R3 codex P2 #2).
_CITED_PATH_JUDGMENTS: frozenset[str] = frozenset(
    {"SUPPORTED", "UNSUPPORTED", "AMBIGUOUS", "PARTIAL", "VIOLATED"}
)
# PARTIAL is a cited-path-only verdict (a reference can support some sub-claims
# but not others). The uncited path has no reference to be partial against, so
# it stays the constraint VIOLATED/NOT_VIOLATED binary (#213).
_UNCITED_PATH_JUDGMENTS: frozenset[str] = frozenset({"VIOLATED", "NOT_VIOLATED"})


class _AuditInvocationError(Exception):
    """Base for audit-tool invocation failures (judge / retrieval).

    Carries an INV-14 fault-class tag + detail. The detail is bounded so the
    `f"{fault_class}: {detail}"` rationale it becomes fits the claim_audit_result
    schema maxLength (#355 P2#3) — every subclass's detail flows to a row
    rationale, so the bound lives here (single choke point).
    """

    def __init__(self, fault_class: str, detail: str) -> None:
        detail = _bounded_failure_detail(detail)
        super().__init__(f"{fault_class}: {detail}")
        self.fault_class = fault_class
        self.detail = detail


class JudgeInvocationError(_AuditInvocationError):
    """Raised by `_invoke_judge` when judge_fn fails or returns malformed output.

    Carries the INV-14 fault-class tag + detail so the caller can emit a
    `RETRIEVAL_FAILED + inconclusive + not_applicable + audit_tool_failure`
    row per spec §4 step 2 + INV-14 instead of letting the exception abort the
    audit pass.
    """


class RetrievalInvocationError(_AuditInvocationError):
    """Raised by `_invoke_retrieve` when retrieve_fn fails or returns malformed output.

    Mirrors JudgeInvocationError but tags faults with the INV-14 retrieval_*
    family (retrieval_api_error / retrieval_timeout / retrieval_network_error)
    so a transient retrieval outage surfaces as audit_tool_failure rather than
    aborting the audit pass (Step 13 R2 codex P2 finding).
    """


def _validate_judge_dict(
    result: Any,
    *,
    allowed_judgments: frozenset[str],
    active_constraint_ids: frozenset[str],
    source: str = "judge_fn",
) -> dict[str, Any]:
    """Validate a judge-output dict (fresh or cache-hit).

    Raises `JudgeInvocationError` with the appropriate fault-class tag for any
    shape violation. Pulled out of `_invoke_judge` so cache hits can reuse the
    same validation surface — without it a malformed cache entry would crash
    `_judge_result_entry` and abort the audit (Step 13 R3 codex P2 #4).

    Validation surface:
      - non-dict                                  → judge_parse_error
      - missing `judgment` or `rationale`         → judge_parse_error
      - judgment not in `allowed_judgments`       → judge_parse_error
      - VIOLATED without non-blank string id      → judge_parse_error
      - VIOLATED id not in `active_constraint_ids`→ judge_parse_error
        (Step 13 R3 codex P2 #1 — prevents formatter gate-refuse on a
        hallucinated constraint the author never declared)
    """
    if not isinstance(result, dict):
        raise JudgeInvocationError(
            "judge_parse_error",
            f"{source} returned {type(result).__name__}, expected dict",
        )
    if "judgment" not in result or "rationale" not in result:
        raise JudgeInvocationError(
            "judge_parse_error",
            f"{source} returned dict missing required key(s); got keys={sorted(result)}",
        )
    judgment = result.get("judgment")
    # Step 13 R8 codex P2-3: guard isinstance(str) before set membership so a
    # malformed return like {"judgment": [1, 2], ...} surfaces as a clean
    # judge_parse_error instead of bubbling TypeError("unhashable type") out
    # past the translation boundary and aborting the audit.
    if not isinstance(judgment, str):
        raise JudgeInvocationError(
            "judge_parse_error",
            f"{source} returned non-string judgment={judgment!r} (type={type(judgment).__name__}); expected one of {sorted(allowed_judgments)}",
        )
    if judgment not in allowed_judgments:
        raise JudgeInvocationError(
            "judge_parse_error",
            f"{source} returned judgment={judgment!r}; expected one of {sorted(allowed_judgments)} on this path",
        )
    if judgment == "VIOLATED":
        vcid = result.get("violated_constraint_id")
        if not isinstance(vcid, str) or not vcid.strip():
            raise JudgeInvocationError(
                "judge_parse_error",
                f"{source} returned VIOLATED without a valid violated_constraint_id (got {vcid!r}); INV-7 requires non-null id",
            )
        if vcid not in active_constraint_ids:
            raise JudgeInvocationError(
                "judge_parse_error",
                f"{source} returned VIOLATED with violated_constraint_id={vcid!r} outside the active constraint set {sorted(active_constraint_ids)}; rejecting hallucinated id (Step 13 R3 codex P2 #1)",
            )
    if judgment == "PARTIAL":
        # #213: a PARTIAL MUST carry a well-formed true-partial sub_claim_breakdown.
        # A malformed PARTIAL is a judge-output parse failure — routing it through
        # judge_parse_error yields the existing (RETRIEVAL_FAILED, inconclusive,
        # not_applicable, audit_tool_failure) row, never a silent bare UNSUPPORTED
        # (which would recreate the invisible-trap failure). The malformed-PARTIAL
        # path has no new matrix triple; it reuses the judge_parse_error contract.
        # is_emittable_*: true-partial mix AND every item schema-shaped (non-empty
        # sub_claim_text + valid sub_verdict). The item-shape half is required
        # because _judge_result_entry copies items onto a *completed* row; a
        # mix-valid-but-malformed item (e.g. missing sub_claim_text) would emit a
        # schema-invalid row instead of taking the judge_parse_error path
        # (ship-gate round-2 finding).
        if not is_emittable_partial_breakdown(result.get("sub_claim_breakdown")):
            raise JudgeInvocationError(
                "judge_parse_error",
                f"{source} returned PARTIAL without an emittable true-partial sub_claim_breakdown "
                f"(>=2 schema-shaped items, >=1 SUPPORTED AND >=1 non-SUPPORTED, each with a "
                f"non-empty sub_claim_text); got {result.get('sub_claim_breakdown')!r}",
            )
    return result


def _invoke_judge(
    judge_fn: Callable[..., dict[str, Any]],
    *,
    allowed_judgments: frozenset[str],
    active_constraint_ids: frozenset[str],
    **call_kwargs: Any,
) -> dict[str, Any]:
    """Invoke `judge_fn` and translate transient failures + malformed output into INV-14 tags.

    Exception → fault class mapping:
      - TimeoutError                          → judge_timeout
      - json.JSONDecodeError / ValueError     → judge_parse_error
      - any other Exception                   → judge_api_error

    Return-value validation delegates to `_validate_judge_dict` so cache hits
    reuse the same surface (Step 13 R3 codex P2 #4).

    `allowed_judgments` is path-specific: cited path passes
    `_CITED_PATH_JUDGMENTS`, uncited (constraint) path passes
    `_UNCITED_PATH_JUDGMENTS`. RETRIEVAL_FAILED / NOT_VIOLATED on the cited
    path is rejected here instead of crashing in `_judge_result_entry`
    (Step 13 R3 codex P2 #2).

    `active_constraint_ids` carries the in-scope MNC/NC ids for this call
    so a VIOLATED with a hallucinated id is rejected at the boundary
    (Step 13 R3 codex P2 #1).

    Does NOT swallow `SystemExit` / `KeyboardInterrupt`.
    """
    try:
        result = judge_fn(**call_kwargs)
    except TimeoutError as exc:
        raise JudgeInvocationError("judge_timeout", str(exc) or "judge timed out") from exc
    except (json.JSONDecodeError, ValueError) as exc:
        raise JudgeInvocationError("judge_parse_error", str(exc) or "judge returned malformed payload") from exc
    except Exception as exc:  # noqa: BLE001 — translation boundary; the source class is captured
        raise JudgeInvocationError("judge_api_error", f"{type(exc).__name__}: {exc}") from exc

    return _validate_judge_dict(
        result,
        allowed_judgments=allowed_judgments,
        active_constraint_ids=active_constraint_ids,
        source="judge_fn",
    )


def _invoke_retrieve(
    retrieve_fn: Callable[[dict[str, Any]], dict[str, Any]],
    citation: dict[str, Any],
) -> dict[str, Any]:
    """Invoke `retrieve_fn` and translate transient failures + malformed output into INV-14 retrieval_* tags.

    Exception → fault class mapping (mirrors `_invoke_judge`):
      - TimeoutError                          → retrieval_timeout
      - OSError / ConnectionError             → retrieval_network_error
      - json.JSONDecodeError / ValueError     → retrieval_api_error
      - any other Exception                   → retrieval_api_error

    Return-value validation:
      - non-dict                              → retrieval_api_error
      - missing `ref_retrieval_method` key    → retrieval_api_error
      - unknown `ref_retrieval_method` value  → retrieval_api_error

    Returns the retrieval dict on success; raises RetrievalInvocationError
    otherwise so the caller can map it to an audit_tool_failure row.
    """
    try:
        result = retrieve_fn(citation)
    except TimeoutError as exc:
        raise RetrievalInvocationError("retrieval_timeout", str(exc) or "retrieve_fn timed out") from exc
    except (ConnectionError, OSError) as exc:
        raise RetrievalInvocationError(
            "retrieval_network_error",
            f"{type(exc).__name__}: {exc}" if str(exc) else type(exc).__name__,
        ) from exc
    except (json.JSONDecodeError, ValueError) as exc:
        raise RetrievalInvocationError(
            "retrieval_api_error",
            str(exc) or "retrieve_fn returned malformed payload",
        ) from exc
    except Exception as exc:  # noqa: BLE001 — translation boundary
        raise RetrievalInvocationError("retrieval_api_error", f"{type(exc).__name__}: {exc}") from exc

    if not isinstance(result, dict):
        raise RetrievalInvocationError(
            "retrieval_api_error",
            f"retrieve_fn returned {type(result).__name__}, expected dict",
        )
    method = result.get("ref_retrieval_method")
    if method is None:
        raise RetrievalInvocationError(
            "retrieval_api_error",
            f"retrieve_fn return missing ref_retrieval_method; got keys={sorted(result)}",
        )
    # Step 13 R8 codex P2-4: guard isinstance(str) before set membership so a
    # malformed return like {"ref_retrieval_method": [...], ...} surfaces as a
    # clean retrieval_api_error instead of bubbling TypeError("unhashable type")
    # out past the translation boundary and aborting the audit (symmetric to
    # P2-3 on the judge side).
    if not isinstance(method, str):
        raise RetrievalInvocationError(
            "retrieval_api_error",
            f"retrieve_fn returned non-string ref_retrieval_method={method!r} (type={type(method).__name__})",
        )
    if method not in {"api", "manual_pdf", "failed", "not_found", "audit_tool_failure"}:
        raise RetrievalInvocationError(
            "retrieval_api_error",
            f"retrieve_fn returned unknown ref_retrieval_method={method!r}",
        )
    # Step 13 R3 codex P2 #3: a successful retrieval pathway MUST carry a
    # non-empty excerpt — otherwise the judge would be invoked with
    # `retrieved_excerpt=None`/empty and could mark a claim SUPPORTED with no
    # source text. Map this shape violation to retrieval_api_error so it
    # surfaces as audit_tool_failure instead of silently degrading the audit.
    if method in {"api", "manual_pdf"}:
        excerpt = result.get("retrieved_excerpt")
        if not isinstance(excerpt, str) or not excerpt.strip():
            raise RetrievalInvocationError(
                "retrieval_api_error",
                f"retrieve_fn returned ref_retrieval_method={method!r} with empty/missing retrieved_excerpt; successful retrievals must carry source text",
            )
    return result


# ---------------------------------------------------------------------------
# Emission helpers — each builds one entry dict.
# ---------------------------------------------------------------------------


def _anchorless_entry(citation: dict[str, Any], *, audit_run_id: str, now_iso: str, judge_model: str) -> dict[str, Any]:
    """§4 Step 1: anchor=none short-circuits to RETRIEVAL_FAILED+inconclusive+not_applicable+not_attempted.

    INV-6 sentinel: anchor_kind=none MUST carry anchor_value="" (empty sentinel
    per claim_audit_result.schema.json). We pin the empty string here rather
    than passing through citation.anchor_value — a stale residual anchor like
    "123" on an anchor_kind=none row violates the schema contract.
    """
    return {
        "claim_id": citation["claim_id"],
        "scoped_manifest_id": citation.get("scoped_manifest_id", SENTINEL_MANIFEST_ID),
        "claim_text": citation["claim_text"],
        "ref_slug": citation["ref_slug"],
        "anchor_kind": "none",
        "anchor_value": "",
        "judgment": "RETRIEVAL_FAILED",
        "audit_status": "inconclusive",
        "defect_stage": "not_applicable",
        "rationale": (
            f"{INV6_RATIONALE_PREFIX}: cited claim {citation['claim_id']} carries anchor=none; "
            "v3.7.3 finalizer should have gate-refused upstream — defense-in-depth row."
        ),
        "judge_model": judge_model,
        "judge_run_at": now_iso,
        "ref_retrieval_method": "not_attempted",
        "upstream_owner_agent": citation.get("upstream_owner_agent"),
        "audit_run_id": audit_run_id,
    }


def _retrieval_failure_entry(
    citation: dict[str, Any],
    *,
    method: str,
    audit_run_id: str,
    now_iso: str,
    judge_model: str,
    fault_class: str | None = None,
) -> dict[str, Any]:
    """§4 Step 2: retrieval-side failure routes that skip the judge."""
    if method == "failed":
        # D2 paywall — LOW-WARN advisory; INV-10.
        entry = {
            "judgment": "RETRIEVAL_FAILED",
            "audit_status": "inconclusive",
            "defect_stage": "not_applicable",
            "rationale": "Reference full text not retrievable (paywall / license-restricted access).",
        }
    elif method == "not_found":
        # Fabricated reference — HIGH-WARN; INV-12.
        entry = {
            "judgment": "RETRIEVAL_FAILED",
            "audit_status": "completed",
            "defect_stage": "retrieval_existence",
            "rationale": "Retrieval API reports the cited reference does not exist (suspected fabrication).",
        }
    elif method == "audit_tool_failure":
        # Transient infrastructure outage — MED-WARN; INV-14.
        tag = fault_class or "retrieval_api_error"
        entry = {
            "judgment": "RETRIEVAL_FAILED",
            "audit_status": "inconclusive",
            "defect_stage": "not_applicable",
            "rationale": f"{tag}: transient audit-infrastructure failure during retrieval; retry on next pipeline pass.",
        }
    else:  # pragma: no cover — should be unreachable given Step 2 caller dispatch
        raise ValueError(f"_retrieval_failure_entry called with non-failure method={method!r}")

    return {
        "claim_id": citation["claim_id"],
        "scoped_manifest_id": citation.get("scoped_manifest_id", SENTINEL_MANIFEST_ID),
        "claim_text": citation["claim_text"],
        "ref_slug": citation["ref_slug"],
        "anchor_kind": citation["anchor_kind"],
        "anchor_value": citation.get("anchor_value", ""),
        "judgment": entry["judgment"],
        "audit_status": entry["audit_status"],
        "defect_stage": entry["defect_stage"],
        "rationale": entry["rationale"],
        "judge_model": judge_model,
        "judge_run_at": now_iso,
        "ref_retrieval_method": method,
        "upstream_owner_agent": citation.get("upstream_owner_agent"),
        "audit_run_id": audit_run_id,
    }


def _judge_result_entry(
    citation: dict[str, Any],
    *,
    judge_result: dict[str, Any],
    ref_retrieval_method: str,
    audit_run_id: str,
    now_iso: str,
    judge_model: str,
) -> dict[str, Any]:
    """§4 Steps 5-6: route judge verdict to the right (judgment, defect_stage) row."""
    verdict = judge_result["judgment"]
    # #360: a judge is an LLM with no length guarantee; clamp its rationale to
    # the schema maxLength before it lands on the completed row (success path).
    rationale = _bounded_judge_rationale(judge_result.get("rationale", ""))

    if verdict == "SUPPORTED":
        judgment, defect_stage, violated_id = "SUPPORTED", None, None
    elif verdict == "AMBIGUOUS":
        hint = judge_result.get("defect_stage_hint")
        if hint not in _AMBIGUOUS_DEFECTS:
            hint = None  # AMBIGUOUS+disallowed defect → coerce to null (INV-3 protection)
        judgment, defect_stage, violated_id = "AMBIGUOUS", hint, None
    elif verdict == "UNSUPPORTED":
        hint = judge_result.get("defect_stage_hint") or "source_description"
        if hint not in _UNSUPPORTED_NON_CONSTRAINT_DEFECTS:
            hint = "source_description"
        judgment, defect_stage, violated_id = "UNSUPPORTED", hint, None
    elif verdict == "VIOLATED":
        # Cited constraint violation — INV-7/INV-8 path.
        judgment = "UNSUPPORTED"
        defect_stage = "negative_constraint_violation"
        violated_id = judge_result.get("violated_constraint_id")
    elif verdict == "PARTIAL":
        # #213 B1 normalization: a prompt-verdict PARTIAL becomes
        # judgment=UNSUPPORTED, defect_stage=source_description, carrying the
        # sub_claim_breakdown[] (the machine-readable partial signal). Routing
        # to UNSUPPORTED puts the unsupported sub-claim through the same
        # gate-refuse path a fully-unsupported claim takes. The breakdown shape
        # was validated true-partial in _validate_judge_dict, so INV-19 holds on
        # the emitted completed row.
        judgment = "UNSUPPORTED"
        defect_stage = "source_description"
        violated_id = None
    else:
        raise ValueError(f"unknown judge verdict: {verdict!r}")

    entry: dict[str, Any] = {
        "claim_id": citation["claim_id"],
        "scoped_manifest_id": citation.get("scoped_manifest_id", SENTINEL_MANIFEST_ID),
        "claim_text": citation["claim_text"],
        "ref_slug": citation["ref_slug"],
        "anchor_kind": citation["anchor_kind"],
        "anchor_value": citation.get("anchor_value", ""),
        "judgment": judgment,
        "audit_status": "completed",
        "defect_stage": defect_stage,
        "rationale": rationale or "(no rationale provided)",
        "judge_model": judge_model,
        "judge_run_at": now_iso,
        "ref_retrieval_method": ref_retrieval_method,
        "upstream_owner_agent": citation.get("upstream_owner_agent"),
        "audit_run_id": audit_run_id,
    }
    if violated_id is not None:
        entry["violated_constraint_id"] = violated_id
    if verdict == "PARTIAL":
        # Carry the decomposition onto the emitted row. Normalize each item to
        # the schema item shape (sub_claim_text, sub_verdict, optional
        # evidence_pointer), dropping any extra keys the judge added so the
        # additionalProperties:false item schema holds. Presence of this field
        # is the machine-readable partial-support signal (#213).
        entry["sub_claim_breakdown"] = [
            {
                "sub_claim_text": item.get("sub_claim_text"),
                "sub_verdict": item.get("sub_verdict"),
                **(
                    {"evidence_pointer": item["evidence_pointer"]}
                    if "evidence_pointer" in item
                    else {}
                ),
            }
            for item in judge_result["sub_claim_breakdown"]
            if isinstance(item, dict)
        ]
    return entry


def _uncited_audit_failure_entry(
    *,
    sentence: dict[str, Any],
    scoped_manifest_id: str,
    manifest_claim_id: str | None,
    fault_class: str,
    detail: str,
    finding_id: str,
    judge_model: str,
    now_iso: str,
) -> dict[str, Any]:
    """§3.6 (v3.8.2 / #118): uncited sentence × manifest pair where the
    constraint judge raised JudgeInvocationError. Mirrors INV-14 row on the
    cited path but rides in the uncited_audit_failures[] aggregate because
    claim_audit_result.ref_slug is required."""
    rationale = f"{fault_class}: {detail}" if detail else f"{fault_class}:"
    return {
        "finding_id": finding_id,
        "claim_text": sentence["sentence_text"],
        "section_path": sentence.get("section_path", ""),
        "scoped_manifest_id": scoped_manifest_id,
        "manifest_claim_id": manifest_claim_id,
        "fault_class": fault_class,
        "rationale": rationale,
        "judge_model": judge_model,
        "judge_run_at": now_iso,
        "rule_version": UAF_RULE_VERSION,
        "upstream_owner_agent": sentence.get("upstream_owner_agent"),
    }


def _constraint_violation_entry(
    *,
    sentence: dict[str, Any],
    judge_result: dict[str, Any],
    scoped_manifest_id: str,
    finding_id: str,
    judge_model: str,
    now_iso: str,
) -> dict[str, Any]:
    """§3.5 / §5 stream (d): uncited claim with VIOLATED judge verdict."""
    violated_id = judge_result.get("violated_constraint_id")
    manifest_claim_id = None
    if violated_id:
        nc_match = RE_NC_CONSTRAINT.match(violated_id)
        if nc_match:
            manifest_claim_id = f"C-{nc_match.group(1)}"
    return {
        "finding_id": finding_id,
        "claim_text": sentence["sentence_text"],
        "section_path": sentence.get("section_path", ""),
        "violated_constraint_id": violated_id,
        "scoped_manifest_id": scoped_manifest_id,
        "manifest_claim_id": manifest_claim_id,
        "judge_verdict": "VIOLATED",
        # #360: clamp the judge-supplied rationale (success path) to maxLength;
        # `or` default catches a missing/null/empty rationale (schema minLength=1).
        "rationale": _bounded_judge_rationale(judge_result.get("rationale"))
        or "Constraint violated by uncited claim.",
        "judge_model": judge_model,
        "judge_run_at": now_iso,
        "rule_version": DRIFT_RULE_VERSION,
        "upstream_owner_agent": sentence.get("upstream_owner_agent"),
    }


def _uncited_assertion_entry(
    *,
    sentence: dict[str, Any],
    finding_id: str,
    now_iso: str,
    trigger_tokens: list[str] | None = None,
) -> dict[str, Any]:
    # Resolve trigger_tokens with strict semantics: prefer the explicit
    # keyword arg, fall back to the sentence dict, and raise if both are
    # absent. The prior `["uncited"]` sentinel passed U-INV-2 minItems=1
    # but carried no semantic content — callers who skipped the detector
    # silently emitted meaningless tokens into the passport. Raise instead
    # so the contract is enforced at write-time, not discovered at audit-
    # read-time (per codex R1 P1-4).
    tokens = trigger_tokens or sentence.get("trigger_tokens")
    if not tokens:
        raise ValueError(
            f"_uncited_assertion_entry: finding_id={finding_id!r} has no "
            "trigger_tokens. Caller must pre-process draft sentences "
            "through detect_uncited_assertions (or supply trigger_tokens "
            "explicitly); the schema's U-INV-2 minItems=1 invariant is "
            "an audit-quality contract, not a placeholder slot."
        )
    manifest_claim_id = sentence.get("manifest_claim_id")
    # Step 7 codex R1 CO-3 / U-INV-4 pair rule: scoped_manifest_id is the
    # disambiguator for a specific manifest claim. When no claim_id is bound
    # (the uncited sentence is in scope for a manifest-level MNC but is NOT
    # itself a manifest claim — runtime contract for stream-d uncited
    # constraint-violation routing), the uncited_assertion row MUST drop the
    # manifest scope. The companion constraint_violations[] row owns the
    # manifest pointer in that case; carrying scope on both rows would fail
    # U-INV-4 (manifest_claim_id null ↔ scoped_manifest_id null).
    scoped_manifest_id = (
        sentence.get("scoped_manifest_id") if manifest_claim_id is not None else None
    )
    return {
        "finding_id": finding_id,
        "sentence_text": sentence["sentence_text"],
        "section_path": sentence.get("section_path", ""),
        "trigger_tokens": tokens,
        "detected_at": now_iso,
        "rule_version": UNCITED_RULE_VERSION,
        "upstream_owner_agent": sentence.get("upstream_owner_agent"),
        "manifest_claim_id": manifest_claim_id,
        "scoped_manifest_id": scoped_manifest_id,
    }


def _claim_drift_entry(
    *,
    drift_kind: str,
    claim_text: str,
    finding_id: str,
    now_iso: str,
    manifest_claim_id: str | None = None,
    scoped_manifest_id: str | None = None,
    section_path: str | None = None,
) -> dict[str, Any]:
    entry = {
        "finding_id": finding_id,
        "drift_kind": drift_kind,
        "claim_text": claim_text,
        "detected_at": now_iso,
        "rule_version": DRIFT_RULE_VERSION,
        "manifest_claim_id": manifest_claim_id,
        "scoped_manifest_id": scoped_manifest_id,
        "section_path": section_path,
    }
    return entry


# ---------------------------------------------------------------------------
# Sampling helper.
# ---------------------------------------------------------------------------


def _stratified_bucket_indices(total: int, cap: int) -> list[int]:
    """Pick `cap` indices in [0, total) via stratified buckets in document order.

    Divides [0, total) into `cap` equal-ish buckets and picks the first index of
    each bucket. The result is strictly ascending and has length min(cap, total).

    Why two-stage fill: a naive `int(i * width)` for `width = total / cap`
    silently collapses adjacent picks when `total/cap < 2` (e.g. N=101,
    cap=100 → `int(99 * 1.01) == int(100 * 1.0)`-class duplicates after
    dedup). The S-INV-1 invariant ties `audited_count` to `len(audited_indices)`
    so a silent dedup would shrink audited_count below cap with no surface.
    We dedup first, then fill the remaining slots from un-picked indices in
    ascending document order — keeping the bucket-first-pick bias for spread
    while honoring the contract that `audited_count == min(cap, N)` whenever
    that is achievable.
    """
    if total <= 0 or cap <= 0:
        return []
    k = min(cap, total)
    width = total / k
    picks: set[int] = set()
    for i in range(k):
        picks.add(int(i * width))
    # Fill missing slots from un-picked indices in ascending order so the
    # final result is exactly k strictly-ascending unique picks whenever
    # k ≤ total (which is guaranteed by `k = min(cap, total)`).
    if len(picks) < k:
        for j in range(total):
            if j not in picks:
                picks.add(j)
                if len(picks) == k:
                    break
    return sorted(picks)


# ---------------------------------------------------------------------------
# Drift detection (manifest set-diff).
# ---------------------------------------------------------------------------


def _detect_drifts(
    *,
    manifests: list[dict[str, Any]],
    emitted_citations: list[dict[str, Any]],
    uncited_sentence_texts: set[str],
    constraint_absorbed_claim_ids: set[tuple[str, str]],
    constraint_absorbed_manifest_scopes: set[str],
    now_iso: str,
    next_finding_id: Callable[[], str],
) -> list[dict[str, Any]]:
    """§4 step 5 manifest set-diff producing claim_drift entries.

    Precedence:
      - T-P8 + Step 13 R5 codex P3: constraint-violation absorbs drift in
        **full** for the violating manifest. `constraint_absorbed_claim_ids`
        captures (manifest, declared-claim-id) pairs; `constraint_absorbed_manifest_scopes`
        captures the manifest_id itself so a same-manifest citation with a
        drifted (non-manifest) claim_id is also suppressed — preserves the
        "absorbed in full" spec promise. A violation in manifest A does NOT
        silence drift in manifest B.
      - T-P10 / D-INV-4: uncited sentence takes precedence over drift — no
        drift entry whose claim_text matches an uncited sentence_text.

    MANIFEST-MISSING fallback (Step 13 R5 codex P2 #2): when no manifest
    carries any claims, there's no pre-commitment baseline to drift FROM —
    every emitted citation would be classified EMITTED_NOT_INTENDED, layering
    spurious LOW-WARN noise on top of the MANIFEST-MISSING advisory the
    formatter already surfaces. Short-circuit and return no drifts so the
    fallback run remains audit-only.
    """
    has_baseline = any((m.get("claims") or []) for m in manifests)
    if not has_baseline:
        return []
    drifts: list[dict[str, Any]] = []

    # Index emitted citations by (scoped_manifest_id, claim_id) — these are
    # the "supported" set candidates the prose actually produced. Use
    # .get(SENTINEL_MANIFEST_ID) so MANIFEST-MISSING callers that omit
    # scoped_manifest_id still build a coherent emitted_pairs set per the
    # sentinel fallback contract (Step 13 R4 codex P2 #3).
    emitted_pairs: set[tuple[str, str]] = {
        (c.get("scoped_manifest_id", SENTINEL_MANIFEST_ID), c.get("claim_id", ""))
        for c in emitted_citations
    }
    emitted_texts = {c.get("claim_text", "") for c in emitted_citations}

    # INTENDED_NOT_EMITTED — manifest claims missing from emitted set.
    # D6 defines Emitted as a set of claim_text values; the dropped-claim side
    # MUST mirror that. A stale or re-numbered claim_id where the claim_text
    # still appears in the draft would otherwise show up as INTENDED_NOT_EMITTED
    # even though the prose carries the claim — a false drift signal
    # (Step 13 R2 codex P2 finding).
    for m in manifests:
        mid = m.get("manifest_id")
        # If this manifest had any constraint violation, absorb ALL of its
        # drift — Step 13 R5 codex P3. The (mid, cid) pair-level absorption
        # below is preserved for backwards compat, but the scope-level skip
        # is the load-bearing rule per "absorbed in full".
        if mid in constraint_absorbed_manifest_scopes:
            continue
        for claim in m.get("claims", []) or []:
            cid = claim.get("claim_id")
            claim_text = claim.get("claim_text", "")
            if (mid, cid) in emitted_pairs:
                continue
            if claim_text and claim_text in emitted_texts:
                # The draft carries the claim under a different claim_id (e.g.
                # claim_id was re-numbered between manifest emission and prose).
                # D6 set-of-text semantics — not a drop.
                continue
            if (mid, cid) in constraint_absorbed_claim_ids:
                continue
            if claim_text in uncited_sentence_texts:
                # Step 7 codex R1 CO-1 / D-INV-4 cross-aggregate exclusivity:
                # when a manifest claim appears as an uncited sentence in the
                # draft, the uncited_assertion row takes priority. Emitting an
                # INTENDED_NOT_EMITTED drift alongside would fail the D-INV-4
                # consistency lint (one finding per sentence across both
                # aggregates). Mirrors the EMITTED_NOT_INTENDED skip in the
                # loop below.
                continue
            drifts.append(
                _claim_drift_entry(
                    drift_kind="INTENDED_NOT_EMITTED",
                    claim_text=claim_text,
                    finding_id=next_finding_id(),
                    now_iso=now_iso,
                    manifest_claim_id=cid,
                    scoped_manifest_id=mid,
                    section_path=None,
                )
            )

    # EMITTED_NOT_INTENDED — emitted citations whose claim_text is not in any
    # manifest's claim_text set. D6 defines Emitted as a SET of claim_text
    # values, so a drifted claim that carries multiple citations (e.g. one
    # sentence with two ref markers) MUST emit ONE drift row, not one per
    # citation. We dedupe by claim_text here while keeping the first
    # encountered section_path as the representative (Step 13 R1 codex P2).
    all_manifest_texts: set[str] = set()
    for m in manifests:
        for claim in m.get("claims", []) or []:
            text = claim.get("claim_text")
            if text:
                all_manifest_texts.add(text)

    seen_drift_texts: set[str] = set()
    for c in emitted_citations:
        text = c.get("claim_text", "")
        if text in all_manifest_texts:
            continue
        c_scope = c.get("scoped_manifest_id", SENTINEL_MANIFEST_ID)
        c_claim_id = c.get("claim_id", "")
        if c_scope in constraint_absorbed_manifest_scopes:
            # Step 13 R5 codex P3 — manifest scope absorbed in full when any
            # citation in it violated a negative constraint. Suppresses
            # same-manifest drift for emitted citations whose claim_id was
            # NOT in the manifest's declared claim set.
            continue
        if (c_scope, c_claim_id) in constraint_absorbed_claim_ids:
            continue
        if text in uncited_sentence_texts:
            # Precedence rule 3 / D-INV-4 — uncited takes priority.
            continue
        if text in seen_drift_texts:
            # D6 set semantics — one drift row per drifted claim_text.
            continue
        seen_drift_texts.add(text)
        drifts.append(
            _claim_drift_entry(
                drift_kind="EMITTED_NOT_INTENDED",
                claim_text=text,
                finding_id=next_finding_id(),
                now_iso=now_iso,
                manifest_claim_id=None,
                scoped_manifest_id=None,
                section_path=c.get("section_path", "unknown"),
            )
        )

    return drifts


# ---------------------------------------------------------------------------
# Public entry point.
# ---------------------------------------------------------------------------


def run_audit_pipeline(
    *,
    citations: list[dict[str, Any]],
    manifests: list[dict[str, Any]],
    # Reserved for the production retrieval-driver wiring per spec §4 step 2.
    # The current implementation injects retrieval via `retrieve_fn` so the
    # corpus is read inside that callback; keeping the parameter on the
    # signature lets the orchestrator pass corpus through without changing
    # the public API when the production retrieve_fn lands.
    corpus: list[dict[str, Any]] | None = None,
    config: dict[str, Any],
    retrieve_fn: Callable[[dict[str, Any]], dict[str, Any]],
    judge_fn: Callable[..., dict[str, Any]],
    audit_run_id: str,
    now_iso: str,
    cache: dict[str, Any] | None = None,
    uncited_sentences: list[dict[str, Any]] | None = None,
    all_uncited_sentences: list[dict[str, Any]] | None = None,
) -> dict[str, list[dict[str, Any]]]:
    """Run §4 Step 1-6 + manifest set-diff over caller-supplied inputs.

    Two uncited streams (Step 13 R4 codex P1 #2):

    - `uncited_sentences`: D4-c detector positives — output of
      `detect_uncited_assertions` (sentences matching the quantifier /
      empirical-trigger filter). Drives `uncited_assertions[]` LOW-WARN
      advisory emission only.
    - `all_uncited_sentences`: the full uncited sentence set (every draft
      sentence with no in-text citation marker). Drives stream (d) —
      constraint judging for `constraint_violations[]` HIGH-WARN. The full
      set is needed because a manifest negative constraint like "No causal
      language" can be violated by a sentence ("The program caused
      improvement") that the D4-c detector filters OUT (no quantifier, no
      empirical trigger token). Routing constraint judging through the
      D4-c-filtered subset silently drops those HIGH-WARN cases.

    When `all_uncited_sentences` is omitted, it defaults to
    `uncited_sentences` (legacy callers preserved — but a warning band:
    those callers miss the R4 P1 expansion and should pass both).

    The uncited token-rule detector
    (`scripts/uncited_assertion_detector.py`, §"Uncited-assertion detector
    (D4-c)" in claim_ref_alignment_audit_agent.md) is NOT invoked here.
    Callers pre-process the full uncited set through
    `detect_uncited_assertions` to get `uncited_sentences`; pass the raw
    full set as `all_uncited_sentences`. `scripts/test_e2e_claim_audit.py`
    exercises the full detector → pipeline → finalizer chain end-to-end.

    Sentence-dict shape:
      - `uncited_sentences[]`: `sentence_text` + `section_path` +
        `trigger_tokens` (non-empty per U-INV-2). D4-c output guarantees
        these fields.
      - `all_uncited_sentences[]`: `sentence_text` + `section_path` only.
        Constraint judging does not consult `trigger_tokens`.

    Returns:
        dict with six aggregate arrays keyed by passport-aggregate name:
        claim_audit_results, uncited_assertions, claim_drifts,
        constraint_violations, audit_sampling_summaries, plus
        claim_intent_manifests (echoed for downstream consumption).

    Raises:
        ValueError: when config validation fails (e.g. max_claims_per_paper <= 0).
    """
    # Intentional no-op: `corpus` is reserved for the production retrieval-driver
    # wiring (spec §4 step 2). Mark as read so static analysers (ruff ARG002,
    # mypy strict unused-arg) do not flag the forward-compat parameter.
    _ = corpus

    # ---- Config sanity ----
    cap = config.get("max_claims_per_paper", 100)
    if not isinstance(cap, int) or cap <= 0:
        raise ValueError(
            f"max_claims_per_paper must be positive integer; got {cap!r} "
            "(spec §4 step 3 + S-INV-2 / T-P11 cap=0 rejected)"
        )
    judge_model = config.get("judge_model", "gpt-5.5-xhigh")
    # #361: prompt_version is a judge-cache-key component. Absent key → default
    # to JUDGE_PROMPT_SHA256, the prompt's own fingerprint and the SINGLE SOURCE
    # OF TRUTH for cache invalidation: check_judge_prompt_version.py keeps this
    # hash in lockstep with the judge-prompt text, so any prompt edit changes the
    # hash and AUTOMATICALLY invalidates stale entries (the human-readable
    # JUDGE_PROMPT_VERSION label is decoupled and must NOT gate the cache).
    # Present-but-None → the caller declares the prompt version UNKNOWN; fail
    # CLOSED by binding a run-local component (audit_run_id is per-run unique) so
    # a stale entry is never served across an unknown-version boundary — cross-run
    # hits are disabled, but within-run dedup for repeated citations still holds.
    prompt_version = config.get("judge_prompt_version", JUDGE_PROMPT_SHA256)
    if prompt_version is None:
        prompt_version = f"__unknown__:{audit_run_id}"

    # Build the three lookup indexes once per run. Used by per-citation
    # constraint resolution + manifest-level absorption + drift detection.
    manifests_by_id: dict[str, dict[str, Any]] = {
        m["manifest_id"]: m for m in manifests if m.get("manifest_id")
    }
    claim_by_mc_id: dict[tuple[str, str], dict[str, Any]] = {
        (m["manifest_id"], claim["claim_id"]): claim
        for m in manifests
        if m.get("manifest_id")
        for claim in (m.get("claims") or [])
        if claim.get("claim_id")
    }
    mncs_by_manifest_id: dict[str, list[dict[str, Any]]] = {
        m["manifest_id"]: list(m.get("manifest_negative_constraints") or [])
        for m in manifests
        if m.get("manifest_id")
    }
    cache = cache if cache is not None else {}
    uncited_sentences = uncited_sentences or []
    # Step 13 R4 codex P1 #2: constraint judging needs the FULL uncited set,
    # not the D4-c-filtered subset. When the caller omits the full set we
    # fall back to the D4-c subset for backwards compatibility — but that
    # path silently drops constraint violations on sentences outside D4-c
    # trigger tokens. New callers should pass both.
    all_uncited_sentences = (
        all_uncited_sentences if all_uncited_sentences is not None else list(uncited_sentences)
    )

    # ---- Sampling decision ----
    total = len(citations)
    if total > cap:
        sampled_indices = _stratified_bucket_indices(total, cap)
        audited_citations = [citations[i] for i in sampled_indices]
        sampling_summaries = [
            {
                "audit_run_id": audit_run_id,
                "max_claims_per_paper": cap,
                "total_citation_count": total,
                "audited_count": len(sampled_indices),
                "audited_indices": sampled_indices,
                "sampling_strategy": SAMPLING_STRATEGY,
                "emitted_at": now_iso,
            }
        ]
    else:
        audited_citations = list(citations)
        sampling_summaries = []

    # ---- Per-citation §4 Step 1-6 ----
    claim_audit_results: list[dict[str, Any]] = []
    constraint_violations: list[dict[str, Any]] = []
    constraint_absorbed_claim_ids: set[tuple[str, str]] = set()
    # Step 13 R5 codex P3: track manifest_id scopes whose drift is absorbed
    # "in full". A constraint violation in manifest M suppresses ALL of M's
    # drift — declared claims (by id), the violating citation's pair (which
    # may itself be drifted), AND any other emitted citation in M with a
    # non-manifest claim_id.
    constraint_absorbed_manifest_scopes: set[str] = set()

    def _written_scope_for(citation: dict[str, Any]) -> str:
        """Return the scoped_manifest_id that goes onto the claim_audit_result row.

        Step 7 codex R1 CO-2: a drifted-cited citation's `claim_id` is not in
        any manifest, but the citation still arrives with the active
        `scoped_manifest_id` for runtime constraint resolution (so global MNCs
        still apply per M-INV-3). The row written to the passport, however,
        MUST carry the sentinel manifest id whenever the (scope, claim_id)
        pair is not present in the manifest index — otherwise INV-15 dangling
        check rejects the passport. Runtime constraint lookup stays untouched
        (it reads citation.scoped_manifest_id directly); only the persisted
        row is normalized.
        """
        runtime_scope = citation.get("scoped_manifest_id", SENTINEL_MANIFEST_ID)
        cid = citation.get("claim_id")
        if runtime_scope == SENTINEL_MANIFEST_ID:
            return SENTINEL_MANIFEST_ID
        if (runtime_scope, cid) in claim_by_mc_id:
            return runtime_scope
        return SENTINEL_MANIFEST_ID

    for citation in audited_citations:
        anchor_kind = citation.get("anchor_kind")
        scoped_manifest_id = citation.get("scoped_manifest_id", SENTINEL_MANIFEST_ID)
        claim_id = citation.get("claim_id")
        written_scope = _written_scope_for(citation)

        # Step 1 — anchor=none firm-rule short-circuit.
        if anchor_kind == "none":
            entry = _anchorless_entry(
                citation,
                audit_run_id=audit_run_id,
                now_iso=now_iso,
                judge_model=judge_model,
            )
            entry["scoped_manifest_id"] = written_scope
            claim_audit_results.append(entry)
            continue

        # Step 2 — retrieval. Wrap in `_invoke_retrieve` so transient failures
        # surface as INV-14 retrieval_* audit_tool_failure rows instead of
        # aborting the pass (Step 13 R2 codex P2 finding, symmetric to the
        # R1 _invoke_judge wrapper).
        try:
            retrieval = _invoke_retrieve(retrieve_fn, citation)
        except RetrievalInvocationError as ret_err:
            entry = _retrieval_failure_entry(
                citation,
                method="audit_tool_failure",
                audit_run_id=audit_run_id,
                now_iso=now_iso,
                judge_model=judge_model,
                fault_class=ret_err.fault_class,
            )
            entry["rationale"] = f"{ret_err.fault_class}: {ret_err.detail}"
            entry["scoped_manifest_id"] = written_scope
            claim_audit_results.append(entry)
            continue
        method = retrieval["ref_retrieval_method"]
        excerpt = retrieval.get("retrieved_excerpt")

        if method in {"failed", "not_found", "audit_tool_failure"}:
            entry = _retrieval_failure_entry(
                citation,
                method=method,
                audit_run_id=audit_run_id,
                now_iso=now_iso,
                judge_model=judge_model,
                fault_class=retrieval.get("fault_class"),
            )
            entry["scoped_manifest_id"] = written_scope
            claim_audit_results.append(entry)
            continue

        if method not in {"api", "manual_pdf"}:
            raise ValueError(f"unexpected ref_retrieval_method: {method!r}")

        # Step 3 — cache lookup. Active constraints scoped by (manifest, claim).
        active_constraints = _active_constraints_for_claim(
            scoped_manifest_id=scoped_manifest_id,
            claim_id=claim_id,
            claim_by_mc_id=claim_by_mc_id,
            mncs_by_manifest_id=mncs_by_manifest_id,
        )
        key = _cache_key(
            claim_text=citation["claim_text"],
            ref_slug=citation["ref_slug"],
            anchor_kind=anchor_kind,
            anchor_value=citation.get("anchor_value", ""),
            retrieved_excerpt=excerpt,
            active_constraints=active_constraints,
            judge_model=judge_model,
            prompt_version=prompt_version,
        )
        # In-scope constraint ids for this call. Both fresh judge invocations
        # AND cache hits validate VIOLATED ids against this set so a
        # hallucinated id never reaches `_judge_result_entry` (Step 13 R3
        # codex P2 #1).
        active_ids: frozenset[str] = frozenset(
            c["constraint_id"] for c in active_constraints if c.get("constraint_id")
        )

        cached = cache.get(key)
        try:
            if cached is not None:
                # Step 13 R3 codex P2 #4: cache may carry a corrupted/partial
                # dict from a prior session. Re-validate every hit through the
                # same surface as fresh invocations so a stale entry surfaces
                # as cache_corruption instead of crashing in
                # `_judge_result_entry`.
                judge_result = _validate_judge_dict(
                    cached,
                    allowed_judgments=_CITED_PATH_JUDGMENTS,
                    active_constraint_ids=active_ids,
                    source="cache",
                )
            else:
                # Step 4-5 — passage location is implicit (excerpt is the
                # located passage); invoke judge. Wrap in `_invoke_judge` so
                # transient failures surface as INV-14 `audit_tool_failure`
                # rows instead of aborting the audit (Step 13 R1 codex).
                judge_result = _invoke_judge(
                    judge_fn,
                    allowed_judgments=_CITED_PATH_JUDGMENTS,
                    active_constraint_ids=active_ids,
                    claim_text=citation["claim_text"],
                    retrieved_excerpt=excerpt,
                    anchor_kind=anchor_kind,
                    anchor_value=citation.get("anchor_value", ""),
                    active_constraints=active_constraints,
                    judge_model=judge_model,
                )
                cache[key] = judge_result
        except JudgeInvocationError as judge_err:
            # Cache-hit validation failures map to cache_corruption per INV-14.
            fault_class = "cache_corruption" if cached is not None else judge_err.fault_class
            entry = _retrieval_failure_entry(
                citation,
                method="audit_tool_failure",
                audit_run_id=audit_run_id,
                now_iso=now_iso,
                judge_model=judge_model,
                fault_class=fault_class,
            )
            entry["rationale"] = f"{fault_class}: {judge_err.detail}"
            entry["scoped_manifest_id"] = written_scope
            claim_audit_results.append(entry)
            continue

        # Step 6 — defect_stage routing + emission.
        entry = _judge_result_entry(
            citation,
            judge_result=judge_result,
            ref_retrieval_method=method,
            audit_run_id=audit_run_id,
            now_iso=now_iso,
            judge_model=judge_model,
        )
        entry["scoped_manifest_id"] = written_scope
        claim_audit_results.append(entry)

        # Precedence rule 1: cited constraint violation absorbs the drift signal.
        # Spec §6 lint rule 6 + §7.2 T-P8: when a citation in this manifest
        # judges VIOLATED, that manifest's drift findings are absorbed in
        # full — the constraint violation has already surfaced the L3
        # faithfulness failure at HIGH-WARN, so layering LOW-WARN drift
        # noise on top of it just reports the same paper-level problem twice.
        # Absorption is manifest-scoped (not global) so VIOLATED in
        # manifest A does NOT silence legitimate drift signal in manifest B.
        if entry["defect_stage"] == "negative_constraint_violation":
            manifest = manifests_by_id.get(scoped_manifest_id)
            if manifest is not None:
                for claim in manifest.get("claims", []) or []:
                    cid_in_manifest = claim.get("claim_id")
                    if cid_in_manifest:
                        constraint_absorbed_claim_ids.add(
                            (scoped_manifest_id, cid_in_manifest)
                        )
            # Also absorb the emitted citation's own (manifest, claim) pair
            # so a drifted-yet-violated citation does not produce a
            # companion EMITTED_NOT_INTENDED row.
            constraint_absorbed_claim_ids.add((scoped_manifest_id, claim_id))
            # Step 13 R5 codex P3 — record the full manifest scope so any
            # other emitted citation in M with a drifted claim_id is also
            # absorbed by the drift detector.
            constraint_absorbed_manifest_scopes.add(scoped_manifest_id)

    # ---- Stream (d): uncited constraint judging over FULL uncited set ----
    # Step 13 R4 codex P1 #2: constraint judging MUST see every uncited
    # sentence (not just D4-c detector positives). An MNC like "No causal
    # language" can be violated by an uncited sentence that the D4-c filter
    # drops (no quantifier, no empirical trigger token), so routing
    # constraint judging through the LOW-WARN advisory loop below would
    # silently miss HIGH-WARN cases. We run constraint judging here on
    # `all_uncited_sentences` and emit LOW-WARN uncited_assertion rows
    # separately on `uncited_sentences` (the D4-c subset).
    #
    # Step 13 R6 codex P1: the documented Stage 4 draft sentence shape carries
    # only `sentence_text` / `section_path` / optional `adjacent_text` — NOT
    # a sentence-level `scoped_manifest_id`. Pre-fix this loop required the
    # caller to populate scope on every sentence; absent that, the
    # constraint judge was skipped and the HIGH-WARN-CONSTRAINT-VIOLATION-UNCITED
    # gate was a no-op for orchestrator callers following the contract.
    # The runtime now derives a default scope set per sentence: if the caller
    # provides `scoped_manifest_id` on the sentence dict, only that manifest's
    # MNCs apply; otherwise the pipeline applies EVERY manifest's MNCs
    # (uncited sentences have no claim-level binding, so manifest-scoped
    # MNCs reach them universally per spec §3.5 D4-c stream (d) semantics).
    # Per-manifest constraint sets — MNCs (manifest-wide) PLUS, when the
    # sentence carries a `manifest_claim_id`, that claim's NC-C entries.
    # NC-C (claim-level) is the R7 codex P1 gap: spec §3.5 D4-c stream (d)
    # covers BOTH MNC and NC-C for uncited violations, but the R6 closure
    # only wired MNCs. We resolve NC-C from claim_by_mc_id at call time
    # when the sentence binds a claim_id.
    #
    # Step 13 R7 codex P2 also applies here: when MNC ids collide across
    # manifests (two manifests both have "MNC-1"), passing a flat list to
    # one judge call makes the returned `violated_constraint_id` ambiguous
    # — we'd have to first-match-wins which mis-attributes the row to the
    # wrong manifest. Solution: run the judge ONCE PER MANIFEST, with that
    # manifest's MNC + NC-C set. Each return is unambiguous by construction;
    # cost is N judge calls per sentence (cf. cited path where each
    # citation already takes one judge call).
    manifest_mncs_by_id: dict[str, list[dict[str, Any]]] = {}
    for m in manifests:
        mid = m.get("manifest_id")
        if not mid:
            continue
        mncs_for_mid: list[dict[str, Any]] = []
        for mnc in m.get("manifest_negative_constraints") or []:
            if mnc.get("constraint_id"):
                mncs_for_mid.append(
                    {"constraint_id": mnc["constraint_id"], "rule": mnc["rule"], "scope": "MNC"}
                )
        manifest_mncs_by_id[mid] = mncs_for_mid

    constraint_violation_texts: set[str] = set()
    cv_counter = 1
    # v3.8.2 / #118 — uncited_audit_failures[] aggregate for JudgeInvocationError
    # on the uncited constraint-judging path. Mirrors INV-14 audit_tool_failure
    # on the cited path. Pre-v3.8.2 the failure was silently substituted as
    # NOT_VIOLATED, suppressing HIGH-WARN constraint checks; the UAF aggregate
    # surfaces the operational signal at MED-WARN advisory tier without
    # dropping audit coverage (option 4 — re-raise and abort — was rejected
    # for that exact coverage reason). See spec §3.6.
    uncited_audit_failures: list[dict[str, Any]] = []
    uaf_counter = 1
    for sentence in all_uncited_sentences:
        scoped_manifest_id_for_sentence = sentence.get("scoped_manifest_id")
        sentence_claim_id = sentence.get("manifest_claim_id")

        # Decide which manifests this sentence is constraint-judged against.
        # Caller-pinned scope → that one manifest. Otherwise every manifest.
        if scoped_manifest_id_for_sentence:
            target_manifest_ids = [scoped_manifest_id_for_sentence] if scoped_manifest_id_for_sentence in manifest_mncs_by_id else []
        else:
            target_manifest_ids = list(manifest_mncs_by_id.keys())

        if not target_manifest_ids:
            continue

        # One judge call per (sentence, manifest) pair so MNC id collisions
        # across manifests cannot misattribute the violation (R7 codex P2).
        sentence_violation_recorded = False
        for mid in target_manifest_ids:
            per_manifest_constraints: list[dict[str, Any]] = list(manifest_mncs_by_id[mid])
            # R7 codex P1: also include NC-C for this manifest's bound claim.
            # v3.8.2 / #118 codex P2-2 + R2 P2-1: only set the UAF row's
            # manifest_claim_id when THIS manifest actually owns the claim
            # binding AND at least one NC constraint was added. When sentence
            # carries a sentence_claim_id but the current manifest doesn't
            # have that claim_id, OR the claim exists but has no NC entries
            # (so the failed judge call was MNC-only), the UAF row's
            # manifest_claim_id MUST stay null — the failure is MNC-only at
            # that point and a non-null binding would mislabel downstream
            # consumers about which constraint set the outage hit.
            uaf_manifest_claim_id: str | None = None
            if sentence_claim_id:
                claim = claim_by_mc_id.get((mid, sentence_claim_id))
                if claim is not None:
                    for nc in claim.get("negative_constraints") or []:
                        cid = nc.get("constraint_id")
                        if cid:
                            per_manifest_constraints.append(
                                {"constraint_id": cid, "rule": nc["rule"], "scope": "NC"}
                            )
                            # Only mark NC-C binding when at least one NC
                            # constraint actually entered the judge call.
                            uaf_manifest_claim_id = sentence_claim_id

            if not per_manifest_constraints:
                continue

            applicable_ids: frozenset[str] = frozenset(
                c["constraint_id"] for c in per_manifest_constraints if c.get("constraint_id")
            )
            # Wrap in `_invoke_judge` so transient failures don't abort the
            # uncited stream. v3.8.2 / #118 — JudgeInvocationError now routes
            # to an uncited_audit_failures[] row (MED-WARN advisory, gate
            # passes) instead of synthesising a NOT_VIOLATED verdict. The
            # synthesis substitution shipped pre-v3.8.2 was silently
            # suppressing HIGH-WARN constraint checks on transient judge
            # outage — see spec §3.6 + §4 step 9 fourth bullet for routing,
            # and the design memo at docs/superpowers/plans/2026-05-17-issue-118-*
            # for the option 1-4 trade-off analysis.
            try:
                judge_result = _invoke_judge(
                    judge_fn,
                    allowed_judgments=_UNCITED_PATH_JUDGMENTS,
                    active_constraint_ids=applicable_ids,
                    claim_text=sentence["sentence_text"],
                    retrieved_excerpt=None,
                    anchor_kind=None,
                    anchor_value=None,
                    active_constraints=per_manifest_constraints,
                    judge_model=judge_model,
                )
            except JudgeInvocationError as judge_err:
                uncited_audit_failures.append(
                    _uncited_audit_failure_entry(
                        sentence=sentence,
                        scoped_manifest_id=mid,
                        manifest_claim_id=uaf_manifest_claim_id,
                        fault_class=judge_err.fault_class,
                        detail=judge_err.detail,
                        finding_id=f"UAF-{uaf_counter:03d}",
                        judge_model=judge_model,
                        now_iso=now_iso,
                    )
                )
                uaf_counter += 1
                continue  # no fake NOT_VIOLATED, no CV row, skip to next manifest
            if judge_result.get("judgment") == "VIOLATED":
                constraint_violations.append(
                    _constraint_violation_entry(
                        sentence=sentence,
                        judge_result=judge_result,
                        scoped_manifest_id=mid,
                        finding_id=f"CV-{cv_counter:03d}",
                        judge_model=judge_model,
                        now_iso=now_iso,
                    )
                )
                cv_counter += 1
                sentence_violation_recorded = True

        if sentence_violation_recorded:
            constraint_violation_texts.add(sentence["sentence_text"])

    # ---- Step 6 stream (uncited_assertion LOW-WARN advisory) ----
    # D4-c detector positives only — uncited_sentences is the filtered set.
    uncited_assertions: list[dict[str, Any]] = []
    uncited_sentence_texts: set[str] = set()
    ua_counter = 1

    for sentence in uncited_sentences:
        uncited_sentence_texts.add(sentence["sentence_text"])
        # Always emit uncited_assertion (LOW-WARN advisory). CV-INV-4
        # explicitly permits a sentence to appear in both uncited_assertions[]
        # and constraint_violations[] simultaneously.
        uncited_assertions.append(
            _uncited_assertion_entry(
                sentence=sentence,
                finding_id=f"UA-{ua_counter:03d}",
                now_iso=now_iso,
            )
        )
        ua_counter += 1

    # Also surface uncited_sentence_texts for any constraint-violation
    # sentence text that wasn't a D4-c positive but did violate an MNC.
    # The drift detector reads `uncited_sentence_texts` to apply the
    # D-INV-4 uncited-takes-precedence rule; without including CV-text
    # entries here, a sentence outside D4-c but matching a manifest claim
    # would produce both a constraint_violation row AND a drift row,
    # violating D-INV-4.
    uncited_sentence_texts.update(constraint_violation_texts)

    # ---- Manifest set-diff drift detection ----
    cd_counter = 1

    def _next_cd() -> str:
        nonlocal cd_counter
        out = f"CD-{cd_counter:03d}"
        cd_counter += 1
        return out

    # Step 7 codex R1 CO-4: drift detection's emitted-side index MUST use
    # the FULL citation list, not the sampled subset. Sampling caps judge
    # invocations (spec §4 step 3) — it does NOT shrink the prose visible to
    # the manifest set-diff. Passing audited_citations here made every
    # unsampled-but-present citation look dropped from manifest, producing
    # false INTENDED_NOT_EMITTED rows in proportion to (total - cap).
    claim_drifts = _detect_drifts(
        manifests=manifests,
        emitted_citations=citations,
        uncited_sentence_texts=uncited_sentence_texts,
        constraint_absorbed_claim_ids=constraint_absorbed_claim_ids,
        constraint_absorbed_manifest_scopes=constraint_absorbed_manifest_scopes,
        now_iso=now_iso,
        next_finding_id=_next_cd,
    )

    return {
        "claim_intent_manifests": manifests,
        "claim_audit_results": claim_audit_results,
        "uncited_assertions": uncited_assertions,
        "claim_drifts": claim_drifts,
        "constraint_violations": constraint_violations,
        "audit_sampling_summaries": sampling_summaries,
        "uncited_audit_failures": uncited_audit_failures,
    }
