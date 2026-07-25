"""Shared constants for v3.8 claim-faithfulness audit.

Single source of truth for the literals + regexes that appear in BOTH the
lint (`check_claim_audit_consistency.py`) and the pipeline runtime
(`claim_audit_pipeline.py`). Re-declaring these in both places opens a
drift hole — a spec bump that updates the lint without updating the
runtime would change one side silently. Tests cover both call sites; the
shared import binds them.

See docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md §3.1
(matrix + INV catalogue) and §4 step 3 (sampling) for canonical
definitions.
"""
from __future__ import annotations

import re

# Canonical sentinel for the MANIFEST-MISSING fallback path (spec §3.1 INV-15).
SENTINEL_MANIFEST_ID = "M-0000-00-00T00:00:00Z-0000"

# INV-6 canonical rationale prefix (v3.7.3 R-L3-1-A firm rule).
INV6_RATIONALE_PREFIX = "v3.7.3 R-L3-1-A violation"

# INV-14 audit-tool-failure rationale fault-class tags.
INV14_FAULT_CLASS_TAGS: tuple[str, ...] = (
    "judge_timeout",
    "judge_api_error",
    "judge_parse_error",
    "cache_corruption",
    "retrieval_api_error",
    "retrieval_timeout",
    "retrieval_network_error",
)

# Sampling strategy literal (S-INV schema constant).
SAMPLING_STRATEGY = "stratified_buckets_v1"

# Sub-claim breakdown sub_verdict enum (claim_audit_result.schema.json #213).
# The "non-SUPPORTED" set is the valid OPPOSING verdicts only — a missing or
# out-of-enum sub_verdict must NOT count as non-SUPPORTED, or a degenerate
# breakdown `[SUPPORTED, <missing>]` would masquerade as true-partial.
SUBCLAIM_VERDICTS: frozenset[str] = frozenset({"SUPPORTED", "UNSUPPORTED", "AMBIGUOUS"})
SUBCLAIM_NON_SUPPORTED: frozenset[str] = frozenset({"UNSUPPORTED", "AMBIGUOUS"})


def is_true_partial_breakdown(breakdown: object) -> bool:
    """True iff `breakdown` is a well-formed true-partial decomposition (#213).

    Single source of truth for the INV-19 true-partial test, shared by the lint
    (`check_claim_audit_consistency.py`), the runtime
    (`claim_audit_pipeline.py` PARTIAL normalization + judge-output validation),
    and the calibration subset metric (`claim_audit_calibration.py`). A list of
    >=2 dict items whose sub_verdicts include >=1 SUPPORTED AND >=1 valid
    non-SUPPORTED ({UNSUPPORTED, AMBIGUOUS}). A missing / out-of-enum sub_verdict
    is NOT counted as non-SUPPORTED.

    NOTE: this is the *content-shape* gate only. The lint additionally pins the
    enclosing row's judgment/defect_stage (INV-19) and the calibration subset
    metric additionally matches the breakdown against each fixture's expected
    sub-claims — neither of those belongs here.
    """
    if not isinstance(breakdown, list) or len(breakdown) < 2:
        return False
    verdicts = [item.get("sub_verdict") for item in breakdown if isinstance(item, dict)]
    has_supported = any(v == "SUPPORTED" for v in verdicts)
    has_non_supported = any(v in SUBCLAIM_NON_SUPPORTED for v in verdicts)
    return has_supported and has_non_supported


def _is_schema_shaped_item(item: object) -> bool:
    """True iff a breakdown item satisfies the schema item shape (#213).

    Each item MUST be a dict with a non-empty-string `sub_claim_text` and a
    `sub_verdict` in the closed enum. The runtime needs this BEFORE it copies an
    item onto an emitted row — `is_true_partial_breakdown` only checks the verdict
    *mix*, so a degenerate item like `{"sub_verdict": "UNSUPPORTED"}` (no text)
    passes the mix gate but would emit `sub_claim_text: None`, a schema-invalid
    completed row (ship-gate round-2 finding).

    Validates the fields the runtime COPIES onto the row against the
    claim_audit_result.schema.json item shape: non-empty string sub_claim_text
    (<=1000), sub_verdict in the enum, and evidence_pointer — if present — a
    string (<=1000) or null. Extra keys are not rejected here because the runtime
    copy keeps only these three; but the copied fields' TYPES must be valid or a
    wrong-typed evidence_pointer (e.g. a number) would reach a completed row and
    violate the schema (ship-gate round-3 finding).
    """
    if not isinstance(item, dict):
        return False
    text = item.get("sub_claim_text")
    if not isinstance(text, str) or not text.strip() or len(text) > 1000:
        return False
    if item.get("sub_verdict") not in SUBCLAIM_VERDICTS:
        return False
    if "evidence_pointer" in item:
        ep = item["evidence_pointer"]
        if ep is not None and (not isinstance(ep, str) or len(ep) > 1000):
            return False
    return True


def is_emittable_partial_breakdown(breakdown: object) -> bool:
    """True iff `breakdown` is true-partial AND every item is schema-shaped (#213).

    The runtime validation gate before a PARTIAL is normalized onto a *completed*
    row: it must be a genuine partial (`is_true_partial_breakdown`) AND every item
    must carry a non-empty sub_claim_text + valid sub_verdict, so the copied row
    satisfies the item schema. A breakdown that is true-partial by mix but has a
    malformed item is a judge parse failure, NOT a completed row.
    """
    if not is_true_partial_breakdown(breakdown):
        return False
    return all(_is_schema_shaped_item(item) for item in breakdown)

# rule_version literals for v3.8.0 release. Future revisions bump the literal
# and require re-lint per spec §3.3 / §3.4 / §3.5.
UNCITED_RULE_VERSION = "D4-c-v1"
DRIFT_RULE_VERSION = "D4-a-v1"
# v3.8.2 / #118 — uncited_audit_failure rule_version literal (§3.6).
# Distinct prefix from D4-c-v1 (uncited_assertion D4-c detector) and
# D4-a-v1 (constraint_violation) so the lint can route by literal.
UAF_RULE_VERSION = "D4-c-v1-uaf-v1"

# #361 — judge-prompt version, a HUMAN-READABLE LABEL ONLY. The judge prompt
# text lives in academic-pipeline/agents/claim_ref_alignment_audit_agent.md
# (### Step 5 — Judge invocation) and is supplied to the pipeline via an injected
# judge_fn, so the pipeline cannot hash the prompt text itself. This literal is a
# friendly name for the current prompt revision (e.g. the #213 Step-0
# sub-claim-decomposition prompt); BUMP IT whenever the judge prompt changes so
# logs/diffs read clearly. It is NO LONGER the judge-cache-key source of truth —
# the cache key tracks JUDGE_PROMPT_SHA256 below (the prompt fingerprint), which
# the lint keeps in lockstep with the prompt text. Decoupling the two means a
# forgotten label bump can never leave stale cache entries valid.
JUDGE_PROMPT_VERSION = "step0-decomp-v1"

# #361 backstop: SHA-256 of the canonical judge-prompt section (the text between
# the JUDGE-PROMPT-CANONICAL-START/END markers in
# academic-pipeline/agents/claim_ref_alignment_audit_agent.md, stripped).
# scripts/check_judge_prompt_version.py recomputes this hash and fails CI if it
# drifts — forcing a human to update this hash whenever the prompt text changes.
# This hash DOUBLES AS the judge-cache-key prompt component (the single source of
# truth for cache invalidation): claim_audit_pipeline.py defaults
# prompt_version to this value, so because the lint pins the hash to the prompt
# text, any prompt edit automatically changes the cache key and invalidates stale
# entries — no reliance on a separate human-readable label bump.
JUDGE_PROMPT_SHA256 = "cdd5ba2d681ea6d6422a017fb122f36a9d62edb32f9d27bd98dbaad1f807b058"

# Constraint id parse rules (spec §3.2 + INV-17 canonical form).
RE_NC_CONSTRAINT = re.compile(r"^NC-C([0-9]{3,})-([0-9]+)$")
RE_MNC_CONSTRAINT = re.compile(r"^MNC-([0-9]+)$")
RE_CLAIM_ID = re.compile(r"^C-([0-9]{3,})$")

# Schema rejects this pattern, but for malformed-on-purpose fixtures the lint
# surfaces INV-17 explicitly before schema validation runs.
RE_NC_INNER_HYPHEN = re.compile(r"^NC-C-[0-9]+-[0-9]+$")

# ---------------------------------------------------------------------------
# D4-c uncited-assertion detector constants (spec §"Uncited-assertion
# detector (D4-c)" in claim_ref_alignment_audit_agent.md).
#
# Centralised here so pipeline runtime, lint, and detector share one source
# of truth — a spec bump touches one literal, not three.
# ---------------------------------------------------------------------------

# Condition 1: empirical-claim verbs (case-insensitive whole-word match).
# Spec list: showed, demonstrated, observed, proved, confirmed.
UNCITED_EMPIRICAL_VERBS: frozenset[str] = frozenset(
    {"showed", "demonstrated", "observed", "proved", "confirmed"}
)

# Condition 1: fuzzy English quantifier words (case-insensitive whole-word).
# Spec list: most, several, two-thirds. Kept literal; numerical / percent
# quantifiers are caught by RE_NUMERIC_QUANTIFIER below.
UNCITED_FUZZY_QUANTIFIERS: frozenset[str] = frozenset(
    {"most", "several", "two-thirds"}
)

# Condition 1: numerical quantifier regex. Spec line 250 lists three numeric
# classes — `numbers / percentages / explicit quantifiers (50%, 67 of 100)`.
# All three fire D4-c condition 1; the detector then applies a guard pass
# (RE_NUMERIC_QUANTIFIER_GUARD below) that rejects matches whose surrounding
# context proves them to be years, version triples, or section numbers
# instead of quantifiers. Splitting into match-broadly + guard-narrowly is
# easier to read and to test than stuffing every exclusion into a single
# regex's negative lookaheads. The detector concatenates the matched
# substring into trigger_tokens verbatim so the schema's minItems=1
# invariant holds.
RE_NUMERIC_QUANTIFIER = re.compile(
    # Order matters: longest-prefix-first so percent and "N of M" bind
    # before the bare-number branch swallows the leading digits.
    r"\b\d+(?:\.\d+)?%"                  # percent quantifier
    r"|\b\d+(?:\.\d+)?\s+of\s+\d+\b"     # "N of M" quantifier idiom
    r"|\b\d+(?:\.\d+)*\b"                # bare number, possibly dotted
                                          # (3+ segments routed to guard
                                          # as version/section)
)

# Condition 1 guard: rejects bare-number matches whose surrounding context
# identifies them as years, version triples, or section numbers — none of
# those are quantitative claims, and treating them as such produced
# false-positive LOW-WARN advisories before the guard landed (see codex
# R1 P1-3). Applied AFTER RE_NUMERIC_QUANTIFIER to the matched substring +
# its character offsets in the sentence; bare-number matches that satisfy
# any guard branch are dropped, percent and `N of M` matches always pass
# through.
#
# Guard branches:
#   1. Standalone 4-digit year in plausible academic range (1900-2099).
#   2. Version triple `X.Y.Z` (dotted form with 3+ segments — the broad
#      regex captures only the first two segments, so we re-scan).
#   3. Dotted section number `X.Y[.Z…]` (treated as section ref, not
#      quantifier). Distinguished from version by `section` / `§` /
#      `chapter` / `figure` / `table` cue word within a 24-char left
#      window, OR by `v` immediately preceding (version literal).
RE_BARE_NUMERIC_YEAR = re.compile(r"^(19|20)\d{2}$")
RE_DOTTED_TRIPLE_OR_MORE = re.compile(r"^\d+(?:\.\d+){2,}$")
RE_DOTTED_PAIR = re.compile(r"^\d+\.\d+$")
RE_SECTION_CUE = re.compile(
    r"(?:section|chapter|figure|table|fig\.|tbl\.|step|appendix|§)\s*$",
    re.IGNORECASE,
)
RE_VERSION_PREFIX = re.compile(r"v\s*$", re.IGNORECASE)
# Catches the case where Python's `\b` fails between a letter and a digit
# (both are \w characters) — e.g. `v3.7.3` has no \b between `v` and `3`,
# so RE_NUMERIC_QUANTIFIER starts matching from the SECOND segment (`7.3`)
# and the guard never sees the version-triple shape. This pattern detects
# a digit-then-dot prefix immediately attached to the left of the match.
# Requires exactly one digit-run + `.` ending the window — combined with
# the surrounding match (also dotted or bare number), this signals a
# multi-segment dotted form that should be treated as a version/section
# reference rather than a quantifier.
RE_NUMERIC_LEFT_ATTACHED = re.compile(r"\d+\.$")

# Condition 2: three-layer-citation ref-marker probe. Presence probe
# WITHIN the v3.7.3 ref-marker namespace — accepts any `<!--ref:...-->`
# shape where the slug payload begins with a non-whitespace character,
# rejects HTML comments that happen to start with `ref:` but use it as
# a label rather than a citation marker (e.g.
# `<!-- ref: $internal.notebook.cell -->`).
#
# Iteration history:
#   R0 `[^-]+`                                — rejected hyphenated slugs.
#   R1 `[A-Za-z][A-Za-z0-9_:-]* + 0-2 tokens` — rejected digit-leading
#                                                 slugs, plus-sign slugs,
#                                                 and 3+ status tokens.
#   R2 `[^>]*?`                                — too broad; matched
#                                                 `<!-- ref: $analysis -->`
#                                                 and similar code/internal
#                                                 ref comments (codex
#                                                 R3 P2-NEW-A).
#   R3 `[^\s>][^>]*?`                          — current. Slug must begin
#                                                 with a non-whitespace
#                                                 non-`>` character; the
#                                                 v3.7.3 strict validator
#                                                 in
#                                                 scripts/check_v3_7_3_three_layer_citation.py
#                                                 catches any remaining
#                                                 shape errors.
RE_REF_MARKER = re.compile(r"<!--\s*ref:[^\s>][^>]*?-->")

# Condition 3: definitional-phrase substrings (case-insensitive). Spec list:
# `refers to`, `is defined as`, `we define`, `for the purposes of`.
UNCITED_DEFINITION_PHRASES: tuple[str, ...] = (
    "refers to",
    "is defined as",
    "we define",
    "for the purposes of",
)
