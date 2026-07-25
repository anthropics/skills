#!/usr/bin/env python3
"""Tests for the citation-existence terminal policy (Delta 3 + INVARIANT C-V6).

Renamed from the original `test_default_blocking_gate.py` (the v3.10 blocking-default
form was withdrawn by the v3.11 C-V6 amendment in favour of the opt-in
`terminal_policies.citation_existence` model). Spec:
docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 3 + §0(4) +
INVARIANT C-V6, deliverable 13.

WHAT IS DETERMINISTICALLY TESTABLE HERE. The finalizer that co-emits the terminal
token and gates output is an LLM agent prompt (pipeline_orchestrator_agent.md), not
a Python function — it cannot be unit-called. So this file pins the deterministic,
machine-checkable substrate the prompt is bound to:

  1. SCHEMA (D-7): the `citation_existence` enum is closed {advisory, strict}, the
     object stays closed, and there is no JSON-Schema `default` (the per-key-absence
     advisory default is a runtime evaluator convention).
  2. MARKER GRAMMAR: the canonical `policy=citation_existence` terminal token parses
     and is caught by the SAME generic severity=HIGH-BLOCK refusal that already
     handles contamination (C-V6(g) — no per-policy enumeration). Reuses the
     production parser in check_v3_10_policy.parse_ref_marker.
  3. REDUCER (C-V6(a)/(f)): the narrowed-`false` 3-class verdict the gate consumes,
     reusing the production reducer citation_verification_summary.reduce_lookup_verified.
  4. POLICY ORACLES (C-V6(b)/(c)/(d)/(g)/(h)): two small pure helpers in THIS file —
     `policy_hash_slug` and `would_terminal_block` — are the executable expression of
     the spec's slug-join rule and the strict-only gate rule. They are the contract
     the prompt MUST follow; they are NOT the production evaluator (that is the
     prompt). Mutation M2 mutates the gate ORACLE to prove the (d) assertion is not
     trivially-passing — see `feedback_schema_mutation_test_for_constraints` and
     `feedback_reverse_invariant_writer_boundary_pin` (the prompt is the writer; the
     oracle pins what it must emit).
"""
from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

from scripts.check_v3_10_policy import (
    parse_ref_marker,
    any_marker_triggers_refusal,
    check_terminal_policies_schema,
    check_finalizer_prompt,
    _extract_section,
    V3_10_FINALIZER_HEADER,
    DEFAULT_TP_SCHEMA,
    DEFAULT_ORCHESTRATOR,
    DEFAULT_FORMATTER,
)
from scripts.citation_verification_summary import reduce_lookup_verified


# ===========================================================================
# Resolver-outcome builders (production shape: status + queried_by)
# ===========================================================================

def _ro(**overrides):
    """All four resolver keys, default skipped/null; override individual ones with
    a (status, queried_by) tuple or a dict."""
    ro = {r: {"status": "skipped", "queried_by": None}
          for r in ("crossref", "openalex", "semantic_scholar", "arxiv")}
    for k, v in overrides.items():
        ro[k] = v if isinstance(v, dict) else {"status": v[0], "queried_by": v[1]}
    return ro


# ===========================================================================
# Policy oracles — the executable expression of the C-V6 prompt contract.
# NOT the production evaluator (the finalizer is an LLM prompt). See module docstring.
# ===========================================================================

# The advisory default for any key absent from the block. Per-key absence ⟹ advisory
# (C-V6(b)); a key whose value equals this default contributes nothing to the slug.
_ADVISORY = "advisory"


_CITATION_TIME_KEYS = frozenset({
    "contamination_triangulation", "citation_existence", "temporal_integrity",
})


def policy_hash_slug(terminal_policies: dict | None) -> str | None:
    """C-V6 / v3.10 slug rule: join each NON-advisory CITATION-TIME key as
    `key.value`, sorted by key name, separated by `+`. Returns None when
    citation-time-advisory (absent block, or every citation-time key advisory)
    — the absence of a stamp IS the advisory signal (no `.advisory` sentinel).
    The package-level `submission_package` key (#394 slice 4) NEVER enters the
    slug — its carrier is the verifier report's policy_slug + fingerprint, not
    ref markers. This mirrors the rule in pipeline_orchestrator_agent.md and
    is the oracle the prompt's policy_hash stamp must match."""
    tp = terminal_policies or {}
    non_advisory = sorted(
        f"{k}.{v}" for k, v in tp.items()
        if v != _ADVISORY and k in _CITATION_TIME_KEYS
    )
    if not non_advisory:
        return None
    return "+".join(non_advisory)


def would_terminal_block(lookup_verified: str, citation_existence: str) -> bool:
    """C-V6(c)/(d): a citation_existence terminal HIGH-BLOCK fires iff the policy is
    `strict` AND lookup_verified == 'false' (the narrowed C-V6(a) false). Advisory
    never blocks; `unresolvable`/`true` never block under any policy. This is the
    strict-only gate the finalizer must enforce — symmetric with contamination."""
    return citation_existence == "strict" and lookup_verified == "false"


def citation_existence_terminal_token(policy_hash: str) -> str:
    """The canonical co-emitted terminal token shape (C-V6(c))."""
    return (
        "TERMINAL-BLOCK severity=HIGH-BLOCK policy=citation_existence "
        f"reason=lookup_verified_false mode=strict policy_hash={policy_hash}"
    )


# ===========================================================================
# 1. SCHEMA (D-7)
# ===========================================================================

@pytest.fixture(scope="module")
def tp_schema():
    with DEFAULT_TP_SCHEMA.open(encoding="utf-8") as f:
        return json.load(f)


@pytest.fixture(scope="module")
def tp_validator(tp_schema):
    Draft202012Validator.check_schema(tp_schema)
    return Draft202012Validator(tp_schema)


def test_schema_citation_existence_enum_closed(tp_schema):
    enum = tp_schema["properties"]["citation_existence"]["enum"]
    assert set(enum) == {"advisory", "strict"}


def test_schema_citation_existence_no_strict_articles_only(tp_validator):
    # citation needs no venue subdivision (the narrowed false carries the precision).
    errs = list(tp_validator.iter_errors({"citation_existence": "strict_articles_only"}))
    assert errs, "citation_existence must reject strict_articles_only"


def test_schema_citation_existence_no_json_schema_default(tp_schema):
    # Per-key absence advisory is a RUNTIME convention, not a JSON-Schema default
    # (JSON-Schema default is non-operational — would be false safety).
    assert "default" not in tp_schema["properties"]["citation_existence"]


def test_schema_object_stays_closed_with_new_key(tp_validator):
    errs = list(tp_validator.iter_errors(
        {"citation_existence": "strict", "bogus_key": "x"}))
    assert errs, "terminal_policies must stay a closed object"


def test_schema_advisory_and_strict_both_valid(tp_validator):
    assert list(tp_validator.iter_errors({"citation_existence": "advisory"})) == []
    assert list(tp_validator.iter_errors({"citation_existence": "strict"})) == []


def test_lint_helper_accepts_citation_existence(tp_schema):
    # The extended check_v3_10_policy lint must pass on the real schema.
    assert check_terminal_policies_schema(tp_schema) == []


# ===========================================================================
# 2. MARKER GRAMMAR — the policy=citation_existence terminal token (C-V6(c)/(g))
# ===========================================================================

def test_citation_existence_terminal_marker_parses_and_refuses():
    """Canonical co-emit: advisory annotation slot + citation_existence terminal
    token. Caught by the SAME generic severity=HIGH-BLOCK refusal as contamination."""
    marker = (
        f"<!--ref:bogus2024 ok "
        f"{citation_existence_terminal_token('citation_existence.strict')}-->")
    pm = parse_ref_marker(marker)
    assert pm is not None
    assert pm.slug == "bogus2024"
    assert pm.base_status == "ok"
    assert pm.terminal is True
    assert pm.is_high_block is True
    assert pm.policy == "citation_existence"
    assert pm.reason == "lookup_verified_false"
    assert pm.mode == "strict"
    assert pm.policy_hash == "citation_existence.strict"
    assert pm.is_well_formed is True
    assert any_marker_triggers_refusal(marker) is True


def test_citation_existence_advisory_marker_does_not_refuse():
    """C-V6(b): under advisory there is NO terminal token AND no citation_existence
    advisory suffix on the marker — the ref marker is byte-equivalent v3.9.x (here a
    plain base-status). The `false` signal's ack-able surface is the
    citation_verification_summary[] aggregate, NOT a marker annotation. The marker
    therefore does not refuse."""
    marker = "<!--ref:unindexed2019 LOW-WARN-->"
    pm = parse_ref_marker(marker)
    assert pm.is_high_block is False
    assert any_marker_triggers_refusal(marker) is False


def test_two_policy_co_emit_dedupes_to_one_affected_ref():
    """C-V6(g): a ref hit by BOTH contamination=strict (k=3) AND citation_existence=
    strict (false) carries TWO TERMINAL-BLOCK tokens (one per policy=) but is counted
    ONCE in any affected-ref aggregate (dedupe by ref slug across policy buckets)."""
    marker = (
        "<!--ref:doublefail2024 LOW-WARN CONTAMINATED-TRIANGULATION-UNMATCHED "
        "TERMINAL-BLOCK severity=HIGH-BLOCK policy=contamination_triangulation "
        "reason=k3_all_indexes_unmatched mode=strict "
        "TERMINAL-BLOCK severity=HIGH-BLOCK policy=citation_existence "
        "reason=lookup_verified_false mode=strict "
        "policy_hash=citation_existence.strict+contamination_triangulation.strict-->")
    pm = parse_ref_marker(marker)
    assert pm is not None
    assert pm.is_high_block is True
    assert any_marker_triggers_refusal(marker) is True
    # Dedupe-by-slug: the affected-ref set holds the slug once even though two
    # terminal tokens are present (mirrors the contamination terminal_blocked[]
    # non-additive rule).
    affected = {pm.slug}
    assert len(affected) == 1


def test_bare_prose_citation_existence_token_does_not_refuse():
    """Anti-false-refuse (Invariant 12): a HIGH-BLOCK token in plain prose, outside
    any <!--ref:...--> comment, is NOT a refusal trigger."""
    prose = ("The reviewer noted a TERMINAL-BLOCK severity=HIGH-BLOCK "
             "policy=citation_existence concern in passing.")
    assert parse_ref_marker(prose) is None
    assert any_marker_triggers_refusal(prose) is False


# ===========================================================================
# 3. REDUCER (C-V6(a)/(f)) — the narrowed-false verdict the gate consumes
# ===========================================================================

def test_reducer_case_a_id_keyed_unmatched_is_false():
    """C-V6(a): an ID-keyed (DOI/arXiv) unmatched with no matched ⟹ false (provably-
    bogus identifier = fabrication evidence)."""
    assert reduce_lookup_verified(_ro(crossref=("unmatched", "id"))) == "false"


def test_reducer_case_a_title_only_unmatched_is_unresolvable_not_false():
    """C-V6(a): a title-only unmatched (no resolvable identifier to key on) ⟹
    unresolvable, NEVER false (real-but-unindexed coverage gap). This is the case the
    narrowing was designed to protect — it must not block under strict."""
    assert reduce_lookup_verified(_ro(crossref=("unmatched", "title"))) == "unresolvable"


def test_reducer_case_f_manual_all_skipped_is_unresolvable():
    """C-V6(f): a manual entry whose resolvers are all skipped ⟹ unresolvable
    (empty adjudicating set), never false."""
    assert reduce_lookup_verified(_ro()) == "unresolvable"


def test_reducer_matched_wins_is_true():
    assert reduce_lookup_verified(
        _ro(crossref=("matched", "id"), openalex=("unmatched", "id"))) == "true"


# ===========================================================================
# 4. POLICY ORACLES (C-V6(b)/(c)/(d)/(g)/(h))
# ===========================================================================

def test_oracle_b_d_advisory_never_blocks():
    """C-V6(b)/(d): under advisory (or absent key), a false row never blocks."""
    assert would_terminal_block("false", "advisory") is False
    # whole-object absent ⟹ advisory for this key
    assert would_terminal_block("false", _ADVISORY) is False


def test_oracle_c_d_strict_blocks_only_false():
    """C-V6(c)/(d): strict blocks iff lookup_verified == false; true/unresolvable
    never block even under strict (symmetric opt-in, narrowed false)."""
    assert would_terminal_block("false", "strict") is True
    assert would_terminal_block("unresolvable", "strict") is False
    assert would_terminal_block("true", "strict") is False


def test_oracle_f_unresolvable_never_blocks_under_strict():
    """C-V6(f): the title-only / manual unresolvable row never blocks, even strict."""
    assert would_terminal_block("unresolvable", "strict") is False


def test_oracle_slug_single_policy():
    assert policy_hash_slug({"citation_existence": "strict"}) == "citation_existence.strict"


def test_oracle_slug_two_policies_sorted_by_key():
    """C-V6(g) slug: two non-advisory keys join sorted by key name. 'citation_existence'
    sorts before 'contamination_triangulation'."""
    slug = policy_hash_slug({
        "citation_existence": "strict",
        "contamination_triangulation": "strict",
    })
    assert slug == "citation_existence.strict+contamination_triangulation.strict"


def test_oracle_slug_advisory_key_omitted():
    """A key whose value is the advisory default contributes nothing to the slug."""
    assert policy_hash_slug({
        "citation_existence": "advisory",
        "contamination_triangulation": "strict",
    }) == "contamination_triangulation.strict"


def test_oracle_slug_all_advisory_is_none():
    """C-V6(b): all-advisory ⟹ no slug (absence of a stamp IS the advisory signal)."""
    assert policy_hash_slug({"citation_existence": "advisory"}) is None
    assert policy_hash_slug({}) is None
    assert policy_hash_slug(None) is None


def test_oracle_slug_submission_package_never_enters():
    """#394 slice 4: submission_package is a PACKAGE-level policy — its
    carrier is the verifier report (policy_slug + package_fingerprint), not
    ref markers. A submission_package-only strict passport stamps nothing,
    and a mixed passport's slug omits it (codex slice-4 review P2: without
    this scope, package-only strict mode would force unrelated ref-marker
    stamping and stale-refuse legacy markers)."""
    assert policy_hash_slug({"submission_package": "strict"}) is None
    assert policy_hash_slug({
        "submission_package": "strict",
        "citation_existence": "strict",
    }) == "citation_existence.strict"


def test_oracle_h_recompute_is_pure_no_cache():
    """C-V6(h): both the slug and the gate are pure functions of (current policy,
    current verdict) — recomputed each pass, never cached. Same inputs ⟹ same outputs
    (idempotent); flipping advisory→strict re-derives a different result with NO
    inherited stale state."""
    summary_false = reduce_lookup_verified(_ro(crossref=("unmatched", "id")))
    # idempotent: byte-equivalent on re-run
    assert reduce_lookup_verified(_ro(crossref=("unmatched", "id"))) == summary_false
    # flip advisory→strict re-derives (no stale 'ready' survives)
    assert would_terminal_block(summary_false, "advisory") is False
    assert would_terminal_block(summary_false, "strict") is True
    assert policy_hash_slug({"citation_existence": "advisory"}) is None
    assert policy_hash_slug({"citation_existence": "strict"}) == "citation_existence.strict"


# ===========================================================================
# REVERSE-INVARIANT PROMPT PINS — the finalizer (D-8) and formatter (D-3) are LLM
# prompts; these tests pin what the prompt files MUST (and MUST NOT) contain, so the
# oracle above cannot silently drift away from the writer. feedback_reverse_invariant_
# writer_boundary_pin.
# ===========================================================================

@pytest.fixture(scope="module")
def orchestrator_text():
    return DEFAULT_ORCHESTRATOR.read_text(encoding="utf-8")


@pytest.fixture(scope="module")
def formatter_text():
    return DEFAULT_FORMATTER.read_text(encoding="utf-8")


def test_finalizer_prompt_declares_citation_existence_terminal(orchestrator_text):
    """D-8: the finalizer prompt must co-emit the citation_existence terminal token
    under strict — the canonical token fragments must be present verbatim so the
    grammar the parser/oracle pin is actually emitted by the writer."""
    assert "policy=citation_existence" in orchestrator_text
    assert "reason=lookup_verified_false" in orchestrator_text
    # symmetric-with-contamination opt-in must be stated (C-V6(c)/(d))
    assert "citation_existence" in orchestrator_text


def test_finalizer_prompt_declares_recompute_each_pass(orchestrator_text):
    """C-V6(h): the finalizer must state the gate is recomputed each finalize pass
    and never inherits a stale ready certification across resume."""
    # The existing finalizer idempotency prose + the new C-V6 subsection jointly
    # carry this; assert the citation-existence subsection ties to recompute/resume.
    assert "citation_existence" in orchestrator_text
    # the no-stale-ready property must be explicit somewhere in the finalizer prose
    lowered = orchestrator_text.lower()
    assert "recompute" in lowered or "re-evaluat" in lowered or "recomputed" in lowered


def test_finalizer_lint_passes_with_citation_existence(orchestrator_text):
    """The extended check_v3_10_policy finalizer lint must pass on the real
    orchestrator (D-8 + D-14)."""
    assert check_finalizer_prompt(orchestrator_text) == []


def test_formatter_has_no_per_policy_citation_existence_refusal(formatter_text):
    """D-3 (formatter zero-change): the formatter must NOT add a citation_existence-
    specific refusal RULE. The generic severity=HIGH-BLOCK Rule 11 already catches the
    token (C-V6(g) + Invariant 13 STAMP-ONLY). A mention inside an explanatory note is
    allowed; what is forbidden is a NEW numbered refusal rule enumerating the policy.
    Guard: there must be no '## Rule 12' / 'Rule 12' citation-existence refusal heading,
    and the generic Rule 11 severity token must still be the refusal key."""
    assert "severity=HIGH-BLOCK" in formatter_text  # generic rule still present
    # No per-policy refusal RULE introduced for citation_existence. (An explanatory
    # mention is fine; a numbered 'Rule 12' refusal class is not.)
    assert "Rule 12" not in formatter_text
    assert "rule 12" not in formatter_text


# ===========================================================================
# MUTATION CHECKS (spec line 158 — two mandatory) — prove the assertions above
# are not trivially-passing. feedback_schema_mutation_test_for_constraints.
# ===========================================================================

def test_mutation_M1_title_only_as_false_must_fail_case_a():
    """M1 (spec line 158): a trivial reducer that treats a title-only unmatched as
    `false` MUST break case (a) — the unindexed-real-paper protection. We assert the
    trivial verdict FAILS the case-(a) assertion, proving the real reducer's narrowing
    is load-bearing (not incidentally satisfied)."""
    def trivial_reduce_unmatched_is_false(ro):
        outcomes = [v or {} for v in ro.values()]
        applicable = [o for o in outcomes if o.get("status") != "skipped"]
        if any(o.get("status") == "matched" for o in applicable):
            return "true"
        # BUG: any unmatched ⟹ false, ignoring queried_by (the un-narrowed form).
        if any(o.get("status") == "unmatched" for o in applicable):
            return "false"
        return "unresolvable"

    title_only = _ro(crossref=("unmatched", "title"))
    # real reducer protects it:
    assert reduce_lookup_verified(title_only) == "unresolvable"
    # trivial mutant breaks the protection — the case-(a) assertion would FAIL:
    assert trivial_reduce_unmatched_is_false(title_only) == "false"
    with pytest.raises(AssertionError):
        assert trivial_reduce_unmatched_is_false(title_only) == "unresolvable"


def test_mutation_M2_accept_all_ignores_policy_must_fail_case_d():
    """M2 (spec line 158): the strict-only gate must be load-bearing against the
    SHIPPED system. The production "evaluator" is the finalizer PROMPT, so the
    load-bearing pin is `check_finalizer_prompt` — it must catch a prompt that drops
    the strict-only predicate (the accept-all / always-advisory mutation).

    Two layers, both asserted:
      (1) PROMPT-CONTRACT mutation (the real one): a finalizer section that carries
          the citation_existence token + recompute prose but DROPS the
          `citation_existence == strict` / `lookup_verified == false` conjunction
          (i.e. would promote regardless of policy, or never block) MUST be flagged
          by check_finalizer_prompt. This pins the writer, not a test helper.
      (2) ORACLE consistency: the test oracle `would_terminal_block` mirrors that
          contract; an accept-all mutant of it diverges from case (d). Kept as a
          sanity check on the oracle, NOT as the load-bearing assertion."""
    # (1) Load-bearing: mutate the REAL prompt — widen the strict promotion rule by
    # dropping its `citation_existence == strict` / `lookup_verified == false`
    # conjunction, WHILE LEAVING the sibling paragraphs (the narrowed-false intro and
    # the multi-policy co-emit paragraph) — which also contain those strings —
    # intact. A section-wide membership check would be fooled by those siblings; the
    # lint must isolate the strict promotion RULE and still flag the widening
    # (codex round-2 P1: too-synthetic mutations miss this bypass).
    real = DEFAULT_ORCHESTRATOR.read_text(encoding="utf-8")
    section = _extract_section(real, V3_10_FINALIZER_HEADER)
    strict_line = next(
        ln for ln in section.splitlines()
        if "policy=citation_existence" in ln and "appends the terminal token" in ln
    )
    widened_line = strict_line.replace(
        "when `terminal_policies.citation_existence == strict` AND the ref's "
        "`lookup_verified == false`,",
        "when citation-existence is enabled,",
    )
    assert widened_line != strict_line, "fixture drift: strict-line predicate text changed"
    mutated_prompt = real.replace(strict_line, widened_line)
    fails = check_finalizer_prompt(mutated_prompt)
    assert any("strict-only gate predicate" in f for f in fails), (
        "check_finalizer_prompt must flag a widened strict promotion rule even when "
        "sibling paragraphs still carry the predicate strings (the bypass codex caught)")
    # the real prompt, by contrast, carries the predicate IN THE RULE and passes:
    assert check_finalizer_prompt(real) == []

    # (2) Oracle-consistency sanity check (not the load-bearing layer).
    def trivial_accept_all(lookup_verified, citation_existence):
        return False  # ignores policy, never blocks
    assert would_terminal_block("false", "strict") is True
    assert trivial_accept_all("false", "strict") is False
