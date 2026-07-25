#!/usr/bin/env python3
"""Tests for the verification_gate API (Delta 5).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 5.

verify_citation composes the four resolvers, maps each resolver's execution to a
{status, queried_by} outcome, derives lookup_verified via the Delta 4 reducer
(narrowed-false, C-V6(a)), reads anchor_present, and stamps verification_timestamp.
Clients are dependency-injected so tests run without network.
"""
from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))


_DEFAULT_REF_SLUG = "vaswani-2017-attention"


def _entry(**overrides):
    # Production-shaped corpus entry: schema-valid against
    # literature_corpus_entry.schema.json (additionalProperties:False). It carries
    # NEITHER ref_slug NOR anchor — both live in writer prose and are passed to
    # verify_citation as explicit params, never read off the corpus entry. Carries
    # all five required corpus fields (citation_key/title/authors/year/source_pointer)
    # so the fixture matches the real shape the gate sees in production.
    base = {
        "citation_key": "vaswani2017",
        "title": "Attention Is All You Need",
        "authors": [{"family": "Vaswani", "given": "Ashish"}],
        "year": 2017,
        "source_pointer": "kb://refs/vaswani2017",
        "doi": "10.5555/abc",
        "obtained_via": "folder-scan",
    }
    base.update(overrides)
    return base


_PAGE_ANCHOR = {"kind": "page", "value": "1"}


def _clients(*, crossref=None, openalex=None, semantic_scholar=None, arxiv=None):
    """Build a clients dict of MagicMocks. Pass a configured mock per resolver,
    or None to get a default (all lookups miss)."""
    def default():
        m = MagicMock()
        m.doi_lookup_with_title_check.return_value = None
        m.title_search.return_value = None
        m.arxiv_id_lookup.return_value = None
        m.lookup.return_value = {"matched": False}
        return m
    return {
        "crossref": crossref or default(),
        "openalex": openalex or default(),
        "semantic_scholar": semantic_scholar or default(),
        "arxiv": arxiv or default(),
    }


# ---------- verify_citation ----------


def test_matched_yields_true_and_id_queried():
    from verification_gate import verify_citation

    cr = MagicMock()
    cr.doi_lookup_with_title_check.return_value = {"title": ["X"]}  # match
    outcome = verify_citation(_entry(), _clients(crossref=cr), ref_slug=_DEFAULT_REF_SLUG)

    assert outcome["lookup_verified"] == "true"
    assert outcome["resolver_outcomes"]["crossref"]["status"] == "matched"
    assert outcome["resolver_outcomes"]["crossref"]["queried_by"] == "id"


def test_id_keyed_unmatched_yields_false():
    from verification_gate import verify_citation
    # All resolvers miss; entry has a DOI → ID-keyed unmatched → false.
    outcome = verify_citation(_entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG)
    assert outcome["lookup_verified"] == "false"
    assert outcome["resolver_outcomes"]["crossref"]["queried_by"] == "id"


def test_title_only_unmatched_yields_unresolvable():
    from verification_gate import verify_citation
    # No DOI → title-only unmatched everywhere → unresolvable (C-V6(a)).
    outcome = verify_citation(_entry(doi=None), _clients(), ref_slug=_DEFAULT_REF_SLUG)
    assert outcome["lookup_verified"] == "unresolvable"
    assert outcome["resolver_outcomes"]["crossref"]["queried_by"] == "title"


def test_resolver_outage_is_unreachable():
    from verification_gate import verify_citation
    from crossref_client import CrossrefUnavailable

    cr = MagicMock()
    cr.doi_lookup_with_title_check.side_effect = CrossrefUnavailable("down")
    # other three also miss (id-keyed) → false stands (anti-fabrication bias).
    outcome = verify_citation(_entry(), _clients(crossref=cr), ref_slug=_DEFAULT_REF_SLUG)
    assert outcome["resolver_outcomes"]["crossref"]["status"] == "unreachable"
    assert outcome["resolver_outcomes"]["crossref"]["queried_by"] is None
    assert outcome["lookup_verified"] == "false"


def test_all_unreachable_is_unresolvable():
    from verification_gate import verify_citation
    from crossref_client import CrossrefUnavailable
    from openalex_client import OpenAlexUnavailable
    from arxiv_client import ArxivUnavailable
    from contamination_signals import SemanticScholarUnavailable

    cr = MagicMock(); cr.doi_lookup_with_title_check.side_effect = CrossrefUnavailable("x")
    oa = MagicMock(); oa.doi_lookup_with_title_check.side_effect = OpenAlexUnavailable("x")
    s2 = MagicMock(); s2.lookup.side_effect = SemanticScholarUnavailable("x")
    ax = MagicMock(); ax.arxiv_id_lookup.side_effect = ArxivUnavailable("x")
    outcome = verify_citation(
        _entry(arxiv_id="1706.03762"),
        _clients(crossref=cr, openalex=oa, semantic_scholar=s2, arxiv=ax),
        ref_slug=_DEFAULT_REF_SLUG,
    )
    assert outcome["lookup_verified"] == "unresolvable"
    for r in ("crossref", "openalex", "semantic_scholar", "arxiv"):
        assert outcome["resolver_outcomes"][r]["status"] == "unreachable"


def test_manual_entry_all_skipped_unresolvable():
    from verification_gate import verify_citation
    outcome = verify_citation(_entry(obtained_via="manual"), _clients(), ref_slug=_DEFAULT_REF_SLUG)
    assert outcome["lookup_verified"] == "unresolvable"
    for r in ("crossref", "openalex", "semantic_scholar", "arxiv"):
        assert outcome["resolver_outcomes"][r]["status"] == "skipped"


def test_arxiv_skipped_on_non_arxiv_citation():
    from verification_gate import verify_citation
    cr = MagicMock(); cr.doi_lookup_with_title_check.return_value = {"title": ["X"]}
    outcome = verify_citation(_entry(), _clients(crossref=cr), ref_slug=_DEFAULT_REF_SLUG)  # no arxiv_id
    assert outcome["resolver_outcomes"]["arxiv"]["status"] == "skipped"


def test_anchor_present_true_for_page_kind():
    from verification_gate import verify_citation
    # anchor is an EXPLICIT param (prose-sourced, joined by ref_slug upstream).
    outcome = verify_citation(_entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG, anchor=_PAGE_ANCHOR)
    assert outcome["anchor_present"] is True


def test_anchor_present_false_for_none_kind():
    from verification_gate import verify_citation
    outcome = verify_citation(
        _entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG,
        anchor={"kind": "none", "value": None})
    assert outcome["anchor_present"] is False


def test_anchor_present_false_when_anchor_omitted():
    from verification_gate import verify_citation
    # No anchor param (the prose join found no anchor for this ref_slug) → False.
    outcome = verify_citation(_entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG)
    assert outcome["anchor_present"] is False


def test_anchor_is_not_read_off_the_corpus_entry():
    """Anti-regression for the latent shape mismatch: even if a corpus entry
    erroneously carries an 'anchor' key, it MUST be ignored — anchor_present
    derives ONLY from the explicit param. This pins that we don't silently
    resurrect the entry.get('anchor') path (the anchor lives in writer prose,
    not in literature_corpus)."""
    from verification_gate import verify_citation
    e = _entry(anchor={"kind": "page", "value": "99"})  # decoy on the entry
    outcome = verify_citation(e, _clients(), ref_slug=_DEFAULT_REF_SLUG)  # no anchor param
    assert outcome["anchor_present"] is False


def test_outcome_carries_keys_and_timestamp():
    from verification_gate import verify_citation
    outcome = verify_citation(_entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG)
    assert outcome["citation_key"] == "vaswani2017"
    assert outcome["ref_slug"] == "vaswani-2017-attention"
    assert outcome["verification_timestamp"]  # never null/empty


def test_outcome_validates_against_summary_schema():
    """The outcome must validate against citation_verification_summary.schema.

    The fixture (_entry) is schema-valid against literature_corpus_entry.schema
    (no ref_slug — additionalProperties:False), so ref_slug comes ONLY from the
    explicit param. Before #332 this passed spuriously because the fixture stuffed
    an illegal ref_slug into the entry; with a production-shaped entry it now
    actually exercises the contract (ref_slug must be a non-null string)."""
    import json
    from jsonschema import Draft202012Validator
    from verification_gate import verify_citation

    schema = json.loads((
        REPO_ROOT / "shared" / "contracts" / "passport"
        / "citation_verification_summary.schema.json"
    ).read_text(encoding="utf-8"))
    outcome = verify_citation(_entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG)
    errors = list(Draft202012Validator(schema).iter_errors(outcome))
    assert errors == [], f"outcome must validate: {errors}"


def test_ref_slug_is_not_read_off_the_corpus_entry():
    """Anti-regression for #332: even if a corpus entry erroneously carries a
    'ref_slug' key, it MUST be ignored — the emitted ref_slug derives ONLY from
    the explicit param (the ref_slug lives in writer prose, not in
    literature_corpus, whose schema forbids the field). Pins that we don't
    resurrect the entry.get('ref_slug') path that emitted ref_slug: None on every
    schema-valid passport."""
    from verification_gate import verify_citation
    e = _entry(ref_slug="decoy-off-the-entry")  # illegal decoy on the entry
    outcome = verify_citation(e, _clients(), ref_slug="from-prose")
    assert outcome["ref_slug"] == "from-prose"


def test_corpus_fixture_is_schema_valid():
    """Guard the guard: the _entry fixture must itself validate against
    literature_corpus_entry.schema.json (the masking bug in #332 was a fixture
    that carried a field the corpus schema forbids). If this fails, the schema
    tests above are testing a shape production never sees."""
    import json
    from jsonschema import Draft202012Validator
    schema = json.loads((
        REPO_ROOT / "shared" / "contracts" / "passport"
        / "literature_corpus_entry.schema.json"
    ).read_text(encoding="utf-8"))
    errors = list(Draft202012Validator(schema).iter_errors(_entry()))
    assert errors == [], f"_entry fixture must be a valid corpus entry: {errors}"


# ---------- verify_passport ----------


def test_verify_passport_runs_each_entry():
    from verification_gate import verify_passport

    cr = MagicMock(); cr.doi_lookup_with_title_check.return_value = {"title": ["X"]}
    passport = {
        "literature_corpus": [
            _entry(citation_key="a"),
            _entry(citation_key="b", doi=None),
        ]
    }
    outcomes = verify_passport(
        passport, clients=_clients(crossref=cr),
        ref_slug_by_key={"a": "slug-a", "b": "slug-b"})
    assert len(outcomes) == 2
    assert {o["citation_key"] for o in outcomes} == {"a", "b"}
    assert {o["ref_slug"] for o in outcomes} == {"slug-a", "slug-b"}


def test_verify_passport_joins_anchors_by_ref_slug():
    """verify_passport performs the prose-marker join: a {ref_slug: anchor} map
    is threaded so each entry's anchor_present reflects ITS ref_slug's anchor.
    Entry 'a' has a page anchor; entry 'b' has none → False."""
    from verification_gate import verify_passport
    passport = {
        "literature_corpus": [
            _entry(citation_key="a"),
            _entry(citation_key="b"),
        ]
    }
    ref_slug_by_key = {"a": "slug-a", "b": "slug-b"}
    anchors = {"slug-a": _PAGE_ANCHOR}  # slug-b absent → anchor_present False
    outcomes = verify_passport(
        passport, clients=_clients(),
        ref_slug_by_key=ref_slug_by_key, anchors=anchors)
    by_key = {o["citation_key"]: o for o in outcomes}
    assert by_key["a"]["anchor_present"] is True
    assert by_key["b"]["anchor_present"] is False


def test_verify_passport_empty_corpus():
    from verification_gate import verify_passport
    assert verify_passport(
        {"literature_corpus": []}, clients=_clients(), ref_slug_by_key={}) == []
    assert verify_passport({}, clients=_clients(), ref_slug_by_key={}) == []


def test_verify_passport_raises_on_missing_join():
    """An entry whose citation_key has no joined ref_slug is a caller error: the
    summary contract requires a non-null string ref_slug, so verify_passport
    raises rather than emitting a contract-invalid summary (#332). No silent
    default to citation_key or empty string."""
    from verification_gate import verify_passport
    passport = {"literature_corpus": [_entry(citation_key="orphan")]}
    with pytest.raises(ValueError, match="orphan"):
        verify_passport(passport, clients=_clients(), ref_slug_by_key={})


def test_verify_passport_outputs_are_schema_valid():
    """End-to-end: a schema-valid passport + a proper join map produces summaries
    that ALL validate against citation_verification_summary.schema (the #332 P1
    was that the normal passport path produced schema-invalid ref_slug: None)."""
    import json
    from jsonschema import Draft202012Validator
    from verification_gate import verify_passport
    schema = json.loads((
        REPO_ROOT / "shared" / "contracts" / "passport"
        / "citation_verification_summary.schema.json"
    ).read_text(encoding="utf-8"))
    passport = {"literature_corpus": [
        _entry(citation_key="a"), _entry(citation_key="b", doi=None)]}
    outcomes = verify_passport(
        passport, clients=_clients(),
        ref_slug_by_key={"a": "slug-a", "b": "slug-b"})
    validator = Draft202012Validator(schema)
    for o in outcomes:
        errors = list(validator.iter_errors(o))
        assert errors == [], f"summary must validate: {errors}"


def test_cache_argument_is_honest_not_silent_noop():
    """cache wiring at this layer is a forward-decl; passing a non-None cache
    must raise (not silently drop it), so a caller is never misled into
    thinking caching took effect."""
    from verification_gate import verify_citation
    with pytest.raises(NotImplementedError):
        verify_citation(_entry(), _clients(), ref_slug=_DEFAULT_REF_SLUG, cache=object())


@pytest.mark.parametrize("bad", [None, "", 0, 123, ["slug"], {"slug": 1}])
def test_verify_citation_rejects_non_string_or_empty_ref_slug(bad):
    """#332 hardening: ref_slug is the prose-join key that the summary schema
    requires as a non-empty string. verify_citation is the single emission point
    (verify_passport routes through it), so the contract is enforced here once:
    a non-string or empty ref_slug would stamp a summary that the caller cannot
    join to any <!--ref:slug--> marker (empty) or that fails the schema's
    type:string (non-string). Both are caller errors — raise rather than emit a
    join-broken / contract-invalid summary. Guarding at the entry also closes the
    verify_passport `is None`-only gap (it now rejects "" and non-str too)."""
    from verification_gate import verify_citation
    with pytest.raises((ValueError, TypeError)):
        verify_citation(_entry(), _clients(), ref_slug=bad)
