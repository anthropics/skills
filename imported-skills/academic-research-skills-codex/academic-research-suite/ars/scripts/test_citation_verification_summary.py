#!/usr/bin/env python3
"""Tests for citation_verification_summary — schema + reducer (Delta 4).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 4
+ §0(4a) / INVARIANT C-V6(a) (narrowed-false).

This file covers BOTH the JSON-Schema (this section) and the Python reducer
(the ReduceLookupVerified section). The reducer is the single source of truth
for lookup_verified; run_evals.py imports it.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

SCHEMA_PATH = (
    REPO_ROOT / "shared" / "contracts" / "passport"
    / "citation_verification_summary.schema.json"
)


@pytest.fixture(scope="module")
def schema():
    with SCHEMA_PATH.open(encoding="utf-8") as f:
        return json.load(f)


@pytest.fixture(scope="module")
def validator(schema):
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def _entry(**overrides):
    # Production-shaped: all four resolver keys present (the summary contract is
    # fully-populated; absent != skipped). crossref matched, the rest skipped.
    base = {
        "citation_key": "vaswani2017",
        "ref_slug": "vaswani-2017-attention",
        "lookup_verified": "true",
        "anchor_present": True,
        "verification_timestamp": "2026-06-04T12:00:00Z",
        "resolver_outcomes": {
            "crossref": {"status": "matched", "queried_by": "id",
                         "response_summary": None},
            "openalex": {"status": "skipped", "queried_by": None,
                         "response_summary": None},
            "semantic_scholar": {"status": "skipped", "queried_by": None,
                                 "response_summary": None},
            "arxiv": {"status": "skipped", "queried_by": None,
                      "response_summary": None},
        },
    }
    base.update(overrides)
    return base


def _full_ro(**overrides):
    """All four resolver keys, default skipped/null; override individual ones."""
    ro = {r: {"status": "skipped", "queried_by": None, "response_summary": None}
          for r in ("crossref", "openalex", "semantic_scholar", "arxiv")}
    ro.update(overrides)
    return ro


# ---------- Schema self-consistency ----------


def test_schema_is_valid_draft_2020_12(schema):
    Draft202012Validator.check_schema(schema)


def test_minimal_valid_entry(validator):
    assert list(validator.iter_errors(_entry())) == []


def test_lookup_verified_enum_is_three_class(validator):
    for v in ("true", "false", "unresolvable"):
        assert list(validator.iter_errors(_entry(lookup_verified=v))) == [], v
    assert any(validator.iter_errors(_entry(lookup_verified="maybe")))
    # The string "true" not a boolean — guard against boolean coercion.
    assert any(validator.iter_errors(_entry(lookup_verified=True)))


def test_required_fields_enforced(validator):
    for field in ("citation_key", "ref_slug", "lookup_verified",
                  "anchor_present", "verification_timestamp", "resolver_outcomes"):
        bad = _entry()
        del bad[field]
        assert any(validator.iter_errors(bad)), f"{field} must be required"


def test_verification_timestamp_never_null(validator):
    assert any(validator.iter_errors(_entry(verification_timestamp=None)))


def test_resolver_outcome_status_enum(validator):
    # status enum exercised with a coherent queried_by per status (ran→id,
    # skipped/unreachable→null), against the full four-resolver shape.
    for s, q in (("matched", "id"), ("unmatched", "id"),
                 ("unreachable", None), ("skipped", None)):
        e = _entry(lookup_verified="true", resolver_outcomes=_full_ro(
            crossref={"status": s, "queried_by": q, "response_summary": None}))
        assert list(validator.iter_errors(e)) == [], s
    bad = _entry(resolver_outcomes=_full_ro(crossref={
        "status": "bogus", "queried_by": "id", "response_summary": None}))
    assert any(validator.iter_errors(bad))


def test_resolver_outcome_queried_by_enum(validator):
    """queried_by ∈ {id, title, null} — the C-V6(a) ID-keyed signal. (Status is
    'unmatched' so id/title are both coherent; null is rejected by the
    status-dependent rule, covered separately.)"""
    for q in ("id", "title"):
        e = _entry(lookup_verified="false", resolver_outcomes=_full_ro(
            crossref={"status": "unmatched", "queried_by": q,
                      "response_summary": None}))
        assert list(validator.iter_errors(e)) == [], repr(q)
    bad = _entry(resolver_outcomes=_full_ro(crossref={
        "status": "unmatched", "queried_by": "doi", "response_summary": None}))
    assert any(validator.iter_errors(bad)), "queried_by must reject 'doi' (use 'id')"


def test_resolver_outcomes_closed_to_four_resolvers(validator):
    bad = _entry(resolver_outcomes={"scopus": {
        "status": "matched", "queried_by": "id", "response_summary": None}})
    assert any(validator.iter_errors(bad)), "unknown resolver must be rejected"


def test_resolver_outcomes_requires_all_four_resolver_keys(validator):
    """The summary contract is fully-populated: all four resolver keys must be
    present (each carrying its own status, incl. 'skipped'), so a consumer never
    has to disambiguate 'absent key' from 'resolver did not run'. A partial
    resolver_outcomes object is a contract violation."""
    bad = _entry(resolver_outcomes={"crossref": {
        "status": "matched", "queried_by": "id", "response_summary": None}})
    assert any(validator.iter_errors(bad)), "must require all 4 resolver keys"


def test_resolver_outcome_requires_queried_by(validator):
    """queried_by is the load-bearing C-V6(a) signal; making it optional lets a
    producer emit an ambiguous unmatched that silently reduces to unresolvable
    instead of false. It must be required (value may be null for skipped /
    pure-unreachable)."""
    bad_ro = {r: {"status": "skipped", "queried_by": None,
                  "response_summary": None}
              for r in ("crossref", "openalex", "semantic_scholar", "arxiv")}
    # drop queried_by from one outcome
    del bad_ro["crossref"]["queried_by"]
    bad = _entry(lookup_verified="unresolvable", resolver_outcomes=bad_ro)
    assert any(validator.iter_errors(bad)), "queried_by must be required"


def test_matched_and_unmatched_require_non_null_queried_by(validator):
    """status ∈ {matched, unmatched} demands queried_by ∈ {id, title} — a ran
    resolver always knows what it keyed on. queried_by=null with a ran status is
    the exact ambiguity the narrowed-false reducer can be fooled by."""
    bad = _entry(lookup_verified="false", resolver_outcomes=_full_ro(
        crossref={"status": "unmatched", "queried_by": None,
                  "response_summary": None}))
    assert any(validator.iter_errors(bad)), \
        "unmatched with queried_by=null must be rejected"
    good = _entry(lookup_verified="false", resolver_outcomes=_full_ro(
        crossref={"status": "unmatched", "queried_by": "id",
                  "response_summary": None}))
    assert list(validator.iter_errors(good)) == []


def test_skipped_and_unreachable_require_null_queried_by(validator):
    """status ∈ {skipped, unreachable} → no meaningful query completed →
    queried_by MUST be null. A skipped row claiming queried_by=id is incoherent."""
    bad = _entry(lookup_verified="unresolvable", resolver_outcomes=_full_ro(
        crossref={"status": "skipped", "queried_by": "id",
                  "response_summary": None}))
    assert any(validator.iter_errors(bad)), \
        "skipped with queried_by=id must be rejected"
    bad2 = _entry(lookup_verified="unresolvable", resolver_outcomes=_full_ro(
        crossref={"status": "unreachable", "queried_by": "title",
                  "response_summary": None}))
    assert any(validator.iter_errors(bad2)), \
        "unreachable with non-null queried_by must be rejected"


def test_resolver_outcome_object_is_closed(validator):
    bad = _entry(resolver_outcomes={"crossref": {
        "status": "matched", "queried_by": "id", "response_summary": None,
        "extra": 1}})
    assert any(validator.iter_errors(bad))


def test_top_level_additional_properties_false(validator):
    assert any(validator.iter_errors(_entry(surprise="x")))


# ---------- reduce_lookup_verified (single source of truth, C-V6(a)) ----------


def _ro(**resolvers):
    """Build a resolver_outcomes dict. Each kwarg value is a (status, queried_by)
    tuple, or a bare status string (queried_by defaults to None)."""
    out = {}
    for name, v in resolvers.items():
        if isinstance(v, tuple):
            status, queried_by = v
        else:
            status, queried_by = v, None
        out[name] = {"status": status, "queried_by": queried_by,
                     "response_summary": None}
    return out


def test_reduce_matched_wins_true():
    from citation_verification_summary import reduce_lookup_verified
    # matched WINS even when another applicable resolver is unmatched.
    assert reduce_lookup_verified(_ro(
        crossref=("matched", "id"),
        openalex=("unmatched", "id"),
    )) == "true"


def test_reduce_id_keyed_unmatched_is_false():
    from citation_verification_summary import reduce_lookup_verified
    # ID-keyed unmatched, no matched → false (fabrication evidence, C-V6(a)).
    assert reduce_lookup_verified(_ro(
        crossref=("unmatched", "id"),
        openalex=("unmatched", "id"),
    )) == "false"


def test_reduce_title_only_unmatched_is_unresolvable_NOT_false():
    """THE narrowed-false case (C-V6(a)): only title-only unmatched (no
    resolvable ID) → unresolvable, never false. The real-but-unindexed paper."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref=("unmatched", "title"),
        openalex=("unmatched", "title"),
    )) == "unresolvable"


def test_reduce_mixed_id_and_title_unmatched_is_false():
    """At least one ID-keyed unmatched → false, even if others are title-only."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref=("unmatched", "id"),
        openalex=("unmatched", "title"),
    )) == "false"


def test_reduce_anti_fabrication_bias_id_unmatched_plus_unreachable():
    """3 ID-keyed unmatched + 1 unreachable → false (one outage doesn't cancel
    positive non-existence evidence). Spec Delta 4 anti-fabrication bias."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref=("unmatched", "id"),
        openalex=("unmatched", "id"),
        semantic_scholar=("unmatched", "id"),
        arxiv="unreachable",
    )) == "false"


def test_reduce_title_unmatched_plus_unreachable_is_unresolvable():
    """Partial outage whose only unmatched are title-only → unresolvable, not
    false (C-V6(a) / OQ-4 amendment)."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref=("unmatched", "title"),
        openalex="unreachable",
    )) == "unresolvable"


def test_reduce_all_unreachable_is_unresolvable():
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref="unreachable",
        openalex="unreachable",
    )) == "unresolvable"


def test_reduce_all_skipped_is_unresolvable():
    """Manual entry: all resolvers skipped → empty adjudicating set →
    unresolvable."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref="skipped",
        openalex="skipped",
        semantic_scholar="skipped",
        arxiv="skipped",
    )) == "unresolvable"


def test_reduce_skipped_excluded_matched_still_true():
    """skipped is excluded from classification; a matched among skips → true."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref=("matched", "id"),
        arxiv="skipped",  # arXiv skipped on a non-arXiv citation
    )) == "true"


def test_reduce_by_design_false_negative_no_id_bogus_title():
    """OQ-5 by-design FN: a fabricated citation with NO DOI/arXiv ID and only a
    bogus title resolves to unresolvable, NOT false — the acknowledged recall
    limit (a no-identifier fabrication is caught by the v3.8 audit + human
    review, not the existence gate). MUST stay unresolvable."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(_ro(
        crossref=("unmatched", "title"),
        openalex=("unmatched", "title"),
        semantic_scholar=("unmatched", "title"),
    )) == "unresolvable"


def test_reduce_empty_outcomes_is_unresolvable():
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified({}) == "unresolvable"


def test_reduce_legacy_unmatched_missing_queried_by_is_unresolvable():
    """Defensive: a legacy/partial outcome with status=unmatched but NO
    queried_by key must NOT be treated as ID-keyed. It safely reduces to
    unresolvable (the reducer keys on queried_by=='id', so a missing key is
    fail-safe-toward-not-false, never false). The schema now forbids this shape,
    but the reducer stays robust to upstream data drift."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified(
        {"crossref": {"status": "unmatched"}}) == "unresolvable"


def test_reduce_none_valued_outcome_is_ignored():
    """A None resolver value (v or {} guard) must not crash and must not be
    treated as evidence; with only a None outcome → unresolvable."""
    from citation_verification_summary import reduce_lookup_verified
    assert reduce_lookup_verified({"crossref": None}) == "unresolvable"
