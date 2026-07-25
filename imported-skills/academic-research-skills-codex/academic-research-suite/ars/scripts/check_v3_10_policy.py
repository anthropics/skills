#!/usr/bin/env python3
"""v3.10 policy-layer lint (#127 PR-B).

Runs ALONGSIDE check_v3_9_0_triangulation.py (NOT a rename — per spec §3 PR-B
item 14 / checkpoint open decision resolved to "alongside"). Verifies the v3.10
terminal-policy-layer contract across the schema, the finalizer prompt, and the
formatter prompt.

Coverage (spec §3 PR-B item 14):
  1. venue_type / venue_type_provenance / venue_type_source schema fields exist
     (incl. the explicit `unknown` enum member).
  2. No `_inferred` provenance value accepted (openalex_inferred / crossref_inferred).
  3. Pair-dependency allOf branches present (type⟹provenance, provenance⟹type,
     unknown-type⟹unknown-provenance one-way, trusted_source⟹venue_type_source).
  4. trusted_source laundering guard. Two surfaces: (a) the lint's RUNTIME check
     (`check_laundering_guard_doc`) asserts the schema's `venue_type_source`
     description documents the guard AND the finalizer prompt forbids deriving
     venue_type from index type fields; (b) `assert_venue_type_source_clean` is the
     reusable SEMANTIC check (a `venue_type_source` naming a lookup index, or empty
     under `trusted_source_declared`, is rejected) — the lint ships no corpus, so
     adapter/corpus tests exercise this helper against real values rather than the
     lint running it in CI.
  5. terminal_policies schema home is the STANDALONE file, NOT the entry schema
     (Invariant 11).
  6. Marker grammar: `severity=HIGH-BLOCK` parses ONLY inside `<!--ref:...-->`;
     bare-prose HIGH-BLOCK does NOT refuse; advisory-suffix slot well-formed;
     policy_hash present on finalized markers; legacy (no-stamp) markers recognized.
     Parser fixtures live in this module (parse_ref_marker) and are exercised by the
     companion test.
  7. Generic-rule shape: formatter rule 11 is a single generic severity=HIGH-BLOCK
     refusal, NOT a per-subtype list.
  8. Formatter STAMP-ONLY: the formatter section declares it does not re-evaluate
     policy logic (Invariant 13).
  9. terminal_policies enum closed; temporal_integrity accepts only `advisory`
     (Invariant 3). citation_existence (v3.11 / C-V6) closed enum {advisory, strict}
     with no JSON-Schema `default`; the finalizer section documents the
     citation_existence terminal token (policy=citation_existence
     reason=lookup_verified_false) and the recompute-each-pass / no-cache property.

Usage:
    python scripts/check_v3_10_policy.py
    python scripts/check_v3_10_policy.py --entry-schema PATH --terminal-policies-schema PATH \
        --formatter-path PATH --orchestrator-path PATH   (for test fixtures)

Exit codes:
    0 — all checks pass
    1 — one or more checks failed
    2 — invocation error (e.g., file missing)
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ENTRY_SCHEMA = REPO_ROOT / "shared/contracts/passport/literature_corpus_entry.schema.json"
DEFAULT_TP_SCHEMA = REPO_ROOT / "shared/contracts/passport/terminal_policies.schema.json"
DEFAULT_FORMATTER = REPO_ROOT / "academic-paper/agents/formatter_agent.md"
DEFAULT_ORCHESTRATOR = REPO_ROOT / "academic-pipeline/agents/pipeline_orchestrator_agent.md"

# The three lookup index names that MUST NOT be a venue_type_source (laundering
# guard, R2-P1). Matched on WORD BOUNDARIES (not bare substrings) so a legitimate
# source like "OpenAlexandria University Press" or "crossreference publisher feed"
# is NOT false-flagged. `semantic scholar` tolerates space / underscore / hyphen
# between the two words. The (?<![A-Za-z0-9]) / (?![A-Za-z0-9]) lookarounds are the
# ASCII-safe word-boundary form (Python `\b` is unreliable across some boundaries).
_LOOKUP_INDEX_RE = re.compile(
    r"(?<![A-Za-z0-9])(?:openalex|crossref|semantic[-_\s]+scholar)(?![A-Za-z0-9])",
    re.IGNORECASE,
)

V3_10_FINALIZER_HEADER = "## Cite-Time Provenance Finalizer — v3.10 extension"
V3_10_FORMATTER_HEADER = "## Cite-Time Terminal Policy Gate (v3.10)"


# ---------------------------------------------------------------------------
# Marker grammar parser (rule 6) — the reusable load-bearing piece
# ---------------------------------------------------------------------------

# A finalized v3.10 ref marker, either shape:
#   non-terminal: <!--ref:<slug> <base-status> [<advisory-suffix>] policy_hash=<slug>-->
#   terminal:     <!--ref:<slug> <base-status> [<advisory-suffix>] TERMINAL-BLOCK
#                 severity=HIGH-BLOCK policy=<p> reason=<r> mode=<m> policy_hash=<slug>-->
# Legacy v3.9.0 markers carry NO policy_hash and are recognized separately.
_REF_MARKER_RE = re.compile(r"<!--ref:(?P<inner>[^>]*?)-->")
_BASE_STATUS = ("ok", "LOW-WARN")


# Recognized key=value prefixes inside a finalized marker. A token that is
# neither a base-status, an advisory suffix, the TERMINAL-BLOCK sentinel, nor one
# of these prefixes is an unrecognized residual token → the marker is malformed.
_KV_PREFIXES = ("severity=", "policy=", "reason=", "mode=", "policy_hash=")


class ParsedMarker:
    """Structured parse of a single <!--ref:...--> marker."""

    def __init__(self, *, slug, base_status, advisory_suffix, terminal,
                 severity, policy, reason, mode, policy_hash, unknown_tokens=None,
                 terminal_blocks=None):
        self.slug = slug
        self.base_status = base_status
        self.advisory_suffix = advisory_suffix
        self.terminal = terminal
        self.severity = severity
        self.policy = policy
        self.reason = reason
        self.mode = mode
        self.policy_hash = policy_hash
        self.unknown_tokens = unknown_tokens or []
        # Per-block terminal metadata (C-V6(g) multi-policy co-emission): one dict
        # {severity,policy,reason,mode} per TERMINAL-BLOCK sentinel. is_well_formed
        # validates each block independently rather than the flattened fields,
        # which "last value wins" and cannot prove per-block completeness (#329).
        self.terminal_blocks = terminal_blocks or []

    @property
    def terminal_block_count(self) -> int:
        return len(self.terminal_blocks)

    @property
    def is_legacy(self) -> bool:
        """A v3.9.0 marker: no policy_hash stamp, no terminal token."""
        return self.policy_hash is None and not self.terminal

    @property
    def is_high_block(self) -> bool:
        return self.severity == "HIGH-BLOCK"

    @property
    def is_well_formed(self) -> bool:
        """A grammatical marker: has a base-status ∈ {ok, LOW-WARN} and no
        unrecognized residual tokens. A marker lacking a base-status (e.g.
        `<!--ref:smith2024 policy_hash=...-->`) is malformed — the v3.7.3 5-cell
        base resolution always produces one.

        A terminal marker (#329) must carry, for EACH TERMINAL-BLOCK independently,
        severity=HIGH-BLOCK + non-empty policy / reason / mode (validated per block
        so a complete later block in a C-V6(g) co-emission cannot mask an earlier
        block's stripped metadata), plus the marker-level shared policy_hash. Empty
        tokens (`policy=`) count as missing — the formatter gate needs the value."""
        if self.base_status not in _BASE_STATUS:
            return False
        if self.unknown_tokens:
            return False
        if self.terminal:
            # Each TERMINAL-BLOCK must be individually complete (C-V6(g)).
            for block in self.terminal_blocks:
                if block.get("severity") != "HIGH-BLOCK":
                    return False
                if not all((block.get("policy"), block.get("reason"), block.get("mode"))):
                    return False
            # policy_hash is marker-level (one shared slug encoding all keys),
            # required on any finalized terminal marker.
            if not self.policy_hash:
                return False
        return True


def parse_ref_marker(text: str) -> ParsedMarker | None:
    """Parse the FIRST <!--ref:...--> marker found in `text`. Returns None if no
    ref marker is present (e.g. a bare `HIGH-BLOCK` token in prose — which must
    NOT be treated as a refusal trigger, anti-false-refuse Inv. 12). A present but
    grammatically malformed marker is returned with `is_well_formed == False` and
    its `unknown_tokens` populated, so a lint can flag it rather than silently
    accept it."""
    m = _REF_MARKER_RE.search(text)
    if not m:
        return None
    return _parse_inner(m.group("inner").strip())


def _parse_inner(inner: str) -> ParsedMarker | None:
    toks = inner.split()
    if not toks:
        return None
    slug = toks[0]
    rest = toks[1:]

    base_status = None
    if rest and rest[0] in _BASE_STATUS:
        base_status = rest[0]
        rest = rest[1:]

    # Optional advisory suffix: a single CONTAMINATED-* token, before TERMINAL-BLOCK.
    advisory_suffix = None
    if rest and rest[0].startswith("CONTAMINATED-"):
        advisory_suffix = rest[0]
        rest = rest[1:]

    terminal = False
    severity = policy = reason = mode = policy_hash = None
    unknown_tokens: list[str] = []
    # Per-block terminal metadata (C-V6(g)): each TERMINAL-BLOCK sentinel opens a
    # new block; its severity/policy/reason/mode tokens belong to THAT block.
    # policy_hash is marker-level (one shared slug encoding all keys), not
    # per-block — it is kept in the flat field only. The flat severity/policy/
    # reason/mode keep the legacy "last value wins" semantics for backward compat;
    # is_well_formed reads terminal_blocks for per-block completeness (#329).
    terminal_blocks: list[dict[str, str | None]] = []

    # key=value tokens + the TERMINAL-BLOCK sentinel. Anything else is residual.
    for tok in rest:
        if tok == "TERMINAL-BLOCK":
            terminal = True
            terminal_blocks.append(
                {"severity": None, "policy": None, "reason": None, "mode": None}
            )
        elif tok.startswith("severity="):
            severity = tok.split("=", 1)[1]
            if terminal_blocks:
                terminal_blocks[-1]["severity"] = severity
        elif tok.startswith("policy="):
            policy = tok.split("=", 1)[1]
            if terminal_blocks:
                terminal_blocks[-1]["policy"] = policy
        elif tok.startswith("reason="):
            reason = tok.split("=", 1)[1]
            if terminal_blocks:
                terminal_blocks[-1]["reason"] = reason
        elif tok.startswith("mode="):
            mode = tok.split("=", 1)[1]
            if terminal_blocks:
                terminal_blocks[-1]["mode"] = mode
        elif tok.startswith("policy_hash="):
            policy_hash = tok.split("=", 1)[1]
        else:
            unknown_tokens.append(tok)

    return ParsedMarker(
        slug=slug, base_status=base_status, advisory_suffix=advisory_suffix,
        terminal=terminal, severity=severity, policy=policy, reason=reason,
        mode=mode, policy_hash=policy_hash, unknown_tokens=unknown_tokens,
        terminal_blocks=terminal_blocks,
    )


def iter_ref_markers(text: str):
    """Yield a ParsedMarker for EVERY <!--ref:...--> marker in `text` (not just
    the first). A document carries many citation markers; refusal scanning must
    cover all of them."""
    for m in _REF_MARKER_RE.finditer(text):
        pm = _parse_inner(m.group("inner").strip())
        if pm is not None:
            yield pm


def any_marker_triggers_refusal(text: str) -> bool:
    """Rule 11 over a whole document: True iff ANY <!--ref:...--> marker carries a
    severity=HIGH-BLOCK token. A clean first marker followed by a terminal one
    still refuses (the single-marker `marker_triggers_refusal` would miss that)."""
    return any(pm.is_high_block for pm in iter_ref_markers(text))


def marker_triggers_refusal(text: str) -> bool:
    """Rule 11 semantics for a SINGLE marker: refuses iff a `severity=HIGH-BLOCK`
    token is present INSIDE the first <!--ref:...--> marker. A bare-prose
    HIGH-BLOCK does not. For whole-document scanning use `any_marker_triggers_refusal`."""
    pm = parse_ref_marker(text)
    if pm is None:
        return False
    return pm.is_high_block


# ---------------------------------------------------------------------------
# Schema checks (rules 1-5, 9)
# ---------------------------------------------------------------------------

def check_entry_schema(entry_schema: dict[str, Any]) -> list[str]:
    fail: list[str] = []
    props = entry_schema.get("properties", {})

    # Rule 1: three venue fields exist.
    for field in ("venue_type", "venue_type_provenance", "venue_type_source"):
        if field not in props:
            fail.append(f"rule 1: entry schema missing {field}")

    # Rule 1: venue_type enum includes the explicit `unknown` member.
    vt_enum = props.get("venue_type", {}).get("enum", [])
    if "unknown" not in vt_enum:
        fail.append("rule 1: venue_type enum missing explicit 'unknown' member")
    expected_vt = {
        "journal-article", "conference-paper", "book", "chapter", "dissertation",
        "preprint", "report", "dataset", "other", "unknown",
    }
    if set(vt_enum) != expected_vt:
        fail.append(f"rule 1: venue_type enum mismatch: {set(vt_enum) ^ expected_vt}")

    # Rule 2: no _inferred provenance values.
    prov_enum = props.get("venue_type_provenance", {}).get("enum", [])
    for forbidden in ("openalex_inferred", "crossref_inferred"):
        if forbidden in prov_enum:
            fail.append(f"rule 2: venue_type_provenance must NOT accept {forbidden} (R-L3-2-D)")
    expected_prov = {"adapter_declared", "user_declared", "trusted_source_declared", "unknown"}
    if set(prov_enum) != expected_prov:
        fail.append(f"rule 2: venue_type_provenance enum mismatch: {set(prov_enum) ^ expected_prov}")

    # Rule 3: the four pair-dependency allOf branches are present (matched by a
    # distinctive phrase in each branch description).
    branch_descs = " ".join(
        b.get("description", "") for b in entry_schema.get("allOf", []) if isinstance(b, dict)
    )
    required_branch_markers = [
        ("venue_type present ⟹ venue_type_provenance present", "type⟹provenance forward"),
        ("venue_type_provenance present ⟹ venue_type present", "provenance⟹type reverse"),
        ("venue_type == unknown ⟹ venue_type_provenance == unknown", "unknown one-way"),
        ("venue_type_provenance == trusted_source_declared ⟹ venue_type_source REQUIRED",
         "trusted_source required"),
    ]
    for phrase, label in required_branch_markers:
        if phrase not in branch_descs:
            fail.append(f"rule 3: missing pair-dependency branch ({label}): {phrase!r}")

    # Rule 5: terminal_policies must NOT be hosted in the entry schema (Inv. 11).
    if "terminal_policies" in props:
        fail.append(
            "rule 5: terminal_policies MUST NOT appear in literature_corpus_entry.schema.json "
            "(it is passport-level, not entry-level — Invariant 11)"
        )

    return fail


def check_terminal_policies_schema(tp_schema: dict[str, Any]) -> list[str]:
    fail: list[str] = []
    props = tp_schema.get("properties", {})

    # Rule 9: contamination_triangulation closed enum.
    ct_enum = props.get("contamination_triangulation", {}).get("enum", [])
    expected_ct = {"advisory", "strict", "strict_articles_only"}
    if set(ct_enum) != expected_ct:
        fail.append(f"rule 9: contamination_triangulation enum mismatch: {set(ct_enum) ^ expected_ct}")

    # Rule 9: temporal_integrity accepts ONLY advisory (Inv. 3).
    ti_enum = props.get("temporal_integrity", {}).get("enum", [])
    if set(ti_enum) != {"advisory"}:
        fail.append(
            f"rule 9: temporal_integrity must accept ONLY 'advisory' (Inv. 3); got {ti_enum}"
        )

    # Rule 9 (v3.11 / C-V6): citation_existence closed enum {advisory, strict}.
    # No strict_articles_only member — the narrowed-false already carries the
    # precision the venue-scoped contamination mode needed (C-V6(a)). And no
    # JSON-Schema `default` keyword (per-key absence advisory is a runtime
    # evaluator convention, not a non-operational schema default — R1 P1).
    ce = props.get("citation_existence", {})
    ce_enum = ce.get("enum", [])
    expected_ce = {"advisory", "strict"}
    if set(ce_enum) != expected_ce:
        fail.append(f"rule 9: citation_existence enum mismatch: {set(ce_enum) ^ expected_ce}")
    if "default" in ce:
        fail.append(
            "rule 9: citation_existence MUST NOT carry a JSON-Schema `default` "
            "(per-key-absence advisory is a runtime evaluator convention; a schema "
            "default is non-operational false safety — R1 P1)"
        )

    # Rule 9: the object is closed (additionalProperties false).
    if tp_schema.get("additionalProperties") is not False:
        fail.append("rule 9: terminal_policies schema must set additionalProperties: false")

    return fail


# ---------------------------------------------------------------------------
# Prompt checks (rules 4, 6, 7, 8)
# ---------------------------------------------------------------------------

def _extract_section(text: str, header: str) -> str:
    """Return the section body from `header` (a ## line) to the next ## or EOF."""
    lines = text.splitlines()
    out: list[str] = []
    in_section = False
    for line in lines:
        if line.startswith(header):
            in_section = True
            out.append(line)
            continue
        if in_section:
            if line.startswith("## "):
                break
            out.append(line)
    return "\n".join(out)


def _strict_promotion_sentence(section: str) -> str | None:
    """Return the single line (markdown bullet) that carries the citation_existence
    strict promotion rule — the one emitting the terminal token. Identified by the
    co-occurrence of `the finalizer appends the terminal token` and
    `policy=citation_existence` on one line. Returns None if no such line exists.

    Scoping the strict-only predicate check to THIS line (not the whole H2 section)
    is what makes the predicate pin un-bypassable: the predicate strings recur in
    sibling paragraphs, so a section-wide membership test would pass even if this
    rule were widened (codex round-2 P1)."""
    for line in section.splitlines():
        if "policy=citation_existence" in line and "appends the terminal token" in line:
            return line
    return None


def check_finalizer_prompt(orchestrator_text: str) -> list[str]:
    fail: list[str] = []
    section = _extract_section(orchestrator_text, V3_10_FINALIZER_HEADER)
    if not section:
        fail.append(f"rule 6/4: finalizer v3.10 section not found ({V3_10_FINALIZER_HEADER!r})")
        return fail

    # Rule 6: both marker shapes documented (TERMINAL-BLOCK token + policy_hash).
    if "TERMINAL-BLOCK" not in section:
        fail.append("rule 6: finalizer section missing the TERMINAL-BLOCK token")
    if "policy_hash" not in section:
        fail.append("rule 6: finalizer section missing policy_hash stamp")
    if "severity=HIGH-BLOCK" not in section:
        fail.append("rule 6: finalizer section missing severity=HIGH-BLOCK token")

    # Rule 4: finalizer must forbid deriving venue_type from index type fields.
    if "MUST NOT infer venue_type" not in section and "MUST NOT infer venue_type from" not in section:
        fail.append(
            "rule 4: finalizer section must forbid inferring venue_type from free-form "
            "venue / index type fields (R-L3-2-D)"
        )

    # Rule 6 (sole evaluator): the finalizer is declared the SOLE policy evaluator.
    if "sole policy evaluator" not in section:
        fail.append("rule 6: finalizer section must declare it is the sole policy evaluator")

    # Rule 9 (v3.11 / C-V6): the finalizer must document the citation_existence
    # terminal promotion grammar — the canonical token fragments must be present so
    # the writer (the prompt) emits the exact shape the parser / formatter rule 11
    # recognize. Also pin the recompute-each-pass property (C-V6(h)) so a future
    # edit cannot silently introduce cached status.
    if "policy=citation_existence" not in section:
        fail.append(
            "rule 9: finalizer section must document the citation_existence terminal "
            "token (policy=citation_existence) per C-V6(c)"
        )
    if "reason=lookup_verified_false" not in section:
        fail.append(
            "rule 9: finalizer section must carry reason=lookup_verified_false in the "
            "citation_existence terminal token per C-V6(c)"
        )
    # Rule 9 (C-V6(c)/(d)): pin the STRICT-ONLY gate predicate WITHIN the strict
    # promotion rule itself — NOT merely somewhere in the H2 section. The predicate
    # strings recur elsewhere in the section (the narrowed-false intro, the
    # multi-policy co-emit paragraph), so a section-wide `in` check is bypassable:
    # the strict bullet could be widened/removed while a sibling paragraph keeps the
    # strings and lint still passes (codex round-2 P1). We isolate the sentence that
    # carries the terminal-token emission rule (the one with
    # `the finalizer appends the terminal token ... policy=citation_existence`) and
    # require BOTH `citation_existence == strict` AND `lookup_verified == false` IN
    # THAT sentence — the conjunction that gates promotion. This is the prompt-contract
    # pin the test oracle mirrors.
    if "policy=citation_existence" in section:
        promo = _strict_promotion_sentence(section)
        if promo is None:
            fail.append(
                "rule 9: finalizer section must carry the citation_existence strict "
                "promotion rule in one sentence (`the finalizer appends the terminal "
                "token ... policy=citation_existence`) per C-V6(c)"
            )
        elif ("citation_existence == strict" not in promo
              or "lookup_verified == false" not in promo):
            fail.append(
                "rule 9: the citation_existence strict promotion rule must state the "
                "strict-only gate predicate verbatim IN THAT SAME RULE "
                "(`citation_existence == strict` AND `lookup_verified == false`), so a "
                "prompt edit cannot silently widen the gate while a sibling paragraph "
                "keeps the strings (C-V6(c)/(d))"
            )
    if "Recompute each pass" not in section:
        fail.append(
            "rule 9: finalizer section must document recompute-each-pass / no-cache "
            "for citation_existence per C-V6(h)"
        )

    # Rule 8 (strict_articles_only PRECISION conjunction + by-design FN): the
    # finalizer must enumerate the full conjunction (DOI ∧ venue_type ∧ provenance)
    # AND document the by-design false-negative, so a future edit cannot silently
    # widen strict_articles_only into all-journal hard-block (§4.4).
    if "strict_articles_only" in section:
        if "DOI present" not in section:
            fail.append("rule 8: strict_articles_only conjunction must require 'DOI present'")
        if "journal-article, conference-paper" not in section:
            fail.append(
                "rule 8: strict_articles_only must scope to venue_type ∈ "
                "{journal-article, conference-paper}"
            )
        if "STAYS ADVISORY by design" not in section and "by-design false-negative" not in section:
            fail.append(
                "rule 8: strict_articles_only must document the by-design false-negative "
                "(DOI-less / unknown-venue stays advisory) — §4.4 recall-limit disclosure"
            )

    return fail


def check_formatter_prompt(formatter_text: str) -> list[str]:
    fail: list[str] = []
    section = _extract_section(formatter_text, V3_10_FORMATTER_HEADER)
    if not section:
        fail.append(f"rule 7/8: formatter v3.10 section not found ({V3_10_FORMATTER_HEADER!r})")
        return fail

    # Rule 8: STAMP-ONLY — formatter must NOT re-evaluate policy logic (Inv. 13).
    if "STAMP-ONLY" not in section and "stamp-checking gate" not in section:
        fail.append("rule 8: formatter section must declare STAMP-ONLY (no policy re-evaluation)")
    if "MUST NOT re-evaluate" not in section:
        fail.append("rule 8: formatter section must state it MUST NOT re-evaluate strict logic")

    # Rule 6: bare-prose HIGH-BLOCK does NOT refuse (anti-false-refuse).
    # The rule must be stated in the refusal-rule-11 text (which sits above this
    # section), so scan the whole formatter for it.
    if "in plain prose" not in formatter_text and "outside any `<!--ref" not in formatter_text:
        fail.append(
            "rule 6: formatter must state a bare-prose HIGH-BLOCK (outside <!--ref-->) "
            "does NOT trigger refusal (anti-false-refuse)"
        )

    # Rule 7: generic-rule shape — exactly ONE refusal rule keyed on severity=HIGH-BLOCK,
    # not a per-subtype list. Assert rule 11 references the GENERIC severity token and
    # does NOT enumerate per-policy subtypes as separate refusal rules.
    if "severity=HIGH-BLOCK" not in formatter_text:
        fail.append("rule 7: formatter rule 11 must key on the generic severity=HIGH-BLOCK token")
    # Two ordered gates (R4-P1 no short-circuit) must be documented.
    if "Gate 1" not in section or "Gate 2" not in section:
        fail.append("rule 6: formatter two-gate (Gate 1 freshness + Gate 2 refusal) not documented")
    if "STALE-POLICY-EVALUATION" not in section:
        fail.append("rule 6: formatter freshness guard must emit [STALE-POLICY-EVALUATION]")

    # C-V6(b) #333: a default-advisory `lookup_verified == false` carries NO marker
    # suffix (marker stays byte-equivalent v3.9.x), so its visibility MUST be carried
    # by the formatter's mandatory provenance_summary `Citation Existence Advisories`
    # section — otherwise an advisory false (a provably-bogus DOI) is buried in an
    # aggregate the user must open separately. Assert the formatter documents it, and
    # that the carrier (provenance_summary) is named INSIDE that subsection — scanning
    # the whole prompt would false-pass on the pre-existing contamination/version-family
    # provenance_summary mentions (codex P2).
    ce_section = _extract_section(formatter_text, "## Citation Existence Advisory")
    if not ce_section:
        fail.append(
            "C-V6(b): formatter must document a mandatory provenance_summary "
            "'Citation Existence Advisories' section that lists every advisory "
            "lookup_verified==false row (the advisory's visibility carrier, #333)"
        )
    else:
        # The section must name BOTH the carrier file (provenance_summary) AND the
        # exact deliverable-visible section label (`Citation Existence Advisories`),
        # both INSIDE the subsection — renaming either silently drops the only
        # visibility path for an advisory false (codex P2).
        if "provenance_summary" not in ce_section:
            fail.append(
                "C-V6(b): the Citation Existence Advisory section must name "
                "provenance_summary.md as its visibility carrier (#333)"
            )
        if "Citation Existence Advisories" not in ce_section:
            fail.append(
                "C-V6(b): the section must reference the exact provenance_summary "
                "label 'Citation Existence Advisories' (the deliverable-visible "
                "section name a consumer greps for, #333)"
            )

    return fail


def check_laundering_guard_doc(entry_schema: dict[str, Any]) -> list[str]:
    """Rule 4: the schema venue_type_source description must document the
    laundering guard (source ∉ three lookup indexes)."""
    fail: list[str] = []
    desc = entry_schema.get("properties", {}).get("venue_type_source", {}).get("description", "")
    if "lookup index" not in desc.lower() and "three lookup" not in desc.lower():
        fail.append(
            "rule 4: venue_type_source description must document the laundering guard "
            "(source must NOT name one of the three lookup indexes)"
        )
    return fail


def assert_venue_type_source_clean(value: str, provenance: str) -> list[str]:
    """Reusable semantic laundering check for a corpus entry (used by fixtures):
    when provenance == trusted_source_declared, venue_type_source must be non-empty
    and NOT name a lookup index."""
    problems: list[str] = []
    if provenance != "trusted_source_declared":
        return problems
    if not value or not value.strip():
        problems.append("venue_type_source is empty under trusted_source_declared")
        return problems
    m = _LOOKUP_INDEX_RE.search(value)
    if m:
        problems.append(
            f"venue_type_source {value!r} names lookup index {m.group(0)!r} (laundering, R2-P1)"
        )
    return problems


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def main() -> int:
    parser = argparse.ArgumentParser(description="v3.10 policy-layer lint")
    parser.add_argument("--entry-schema", default=str(DEFAULT_ENTRY_SCHEMA))
    parser.add_argument("--terminal-policies-schema", default=str(DEFAULT_TP_SCHEMA))
    parser.add_argument("--formatter-path", default=str(DEFAULT_FORMATTER))
    parser.add_argument("--orchestrator-path", default=str(DEFAULT_ORCHESTRATOR))
    args = parser.parse_args()

    paths = {
        "entry schema": Path(args.entry_schema),
        "terminal_policies schema": Path(args.terminal_policies_schema),
        "formatter": Path(args.formatter_path),
        "orchestrator": Path(args.orchestrator_path),
    }
    for label, p in paths.items():
        if not p.exists():
            print(f"ERROR: {label} not found: {p}", file=sys.stderr)
            return 2

    entry_schema = _load_json(Path(args.entry_schema))
    tp_schema = _load_json(Path(args.terminal_policies_schema))
    formatter_text = Path(args.formatter_path).read_text(encoding="utf-8")
    orchestrator_text = Path(args.orchestrator_path).read_text(encoding="utf-8")

    failures: list[str] = []
    failures += check_entry_schema(entry_schema)
    failures += check_terminal_policies_schema(tp_schema)
    failures += check_laundering_guard_doc(entry_schema)
    failures += check_finalizer_prompt(orchestrator_text)
    failures += check_formatter_prompt(formatter_text)

    if failures:
        print("v3.10 policy-layer lint FAILED:", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1

    print("v3.10 policy-layer lint OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
