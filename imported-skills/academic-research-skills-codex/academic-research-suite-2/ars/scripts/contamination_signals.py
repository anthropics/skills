#!/usr/bin/env python3
"""#105 v3.7.3 contamination_signals resolvers.

Pure functions implementing v3.7.3 spec §3.2 Vector 1 + Vector 2 for use
by the migration tool. bibliography_agent computes these at ingest time;
this module gives the migration tool the equivalent computation for
post-hoc backfill on pre-v3.7.3 entries.

Design: docs/design/2026-05-15-issue-105-contamination-signals-backfill-design.md
Spec: docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md §3.2
"""
from __future__ import annotations

from typing import Any, Mapping, Protocol

# Re-export ArxivUnavailable so callers (and tests) can reference it from the
# signals module alongside the other resolver exceptions. Dual-path import
# mirrors the client modules' own import guard.
try:
    from arxiv_client import ArxivUnavailable
except ImportError:
    from scripts.arxiv_client import ArxivUnavailable


# #431 §0.12.3b — the resolver-decision logic version, stored under the
# "decision_version" key in each cached verdict value (spec-preferred form: no
# cache-key / schema migration; pre-v5 rows simply re-resolve once under v5).
# Bump it whenever the accept/reject logic changes so a verdict produced by a
# DIFFERENT logic is not silently reused. v5 is the exact-title-or-bust pivot: a
# pre-v5 row (written under the v3/v4 author-agree tiers, e.g. a `Study 1` /
# `Study 2` same-author pair stored as `matched_by=title`) would otherwise be
# returned as `matched` with `client.title_search` never called, bypassing the
# v5 loop entirely — a dangerous false-positive surviving the pivot for up to the
# 90-day TTL. A row whose stored version is absent or != this constant is a MISS.
RESOLVER_DECISION_VERSION = "431-v5"


# 10-venue closed list per v3.7.3 spec §3.2 + schema description.
# This list is intentionally redundant with the bibliography_agent's
# in-prose list — adapters and migration tools both need the literal set.
PREPRINT_VENUES = frozenset({
    "arXiv",
    "bioRxiv",
    "medRxiv",
    "SSRN",
    "Research Square",
    "Preprints.org",
    "ChemRxiv",
    "EarthArXiv",
    "OSF Preprints",
    "TechRxiv",
})


# source_pointer → venue inference table. Per v3.7.3 spec §3.2 + schema
# rule, when `venue` is absent the resolver must check `source_pointer`
# for a preprint-server URL/identifier. Substring match against
# lower-cased pointer; keys must be lower-cased and unambiguous.
_POINTER_VENUE_HINTS: tuple[tuple[str, str], ...] = (
    ("arxiv.org", "arXiv"),
    ("biorxiv.org", "bioRxiv"),
    ("medrxiv.org", "medRxiv"),
    ("ssrn.com", "SSRN"),
    ("papers.ssrn.com", "SSRN"),
    ("researchsquare.com", "Research Square"),
    ("preprints.org", "Preprints.org"),
    ("chemrxiv.org", "ChemRxiv"),
    ("eartharxiv.org", "EarthArXiv"),
    ("osf.io/preprints", "OSF Preprints"),
    ("techrxiv.org", "TechRxiv"),
)


def _infer_venue_from_pointer(source_pointer: str) -> str | None:
    """Return the preprint venue inferred from the source_pointer URL,
    or None if no preprint-server hint is present. Per v3.7.3 spec §3.2
    Vector 1: 'venue field (or, when venue is absent, inference from
    source_pointer)'."""
    pointer = source_pointer.lower()
    for hint, venue in _POINTER_VENUE_HINTS:
        if hint in pointer:
            return venue
    return None


class SemanticScholarUnavailable(Exception):
    """SS API degraded (network failure / rate limit exhausted / 5xx).

    Per spec §3.2 emission rules, this triggers OMIT of the
    `semantic_scholar_unmatched` field rather than setting it to False.
    Absence ≠ negative confirmation."""


class SemanticScholarClient(Protocol):
    """Minimal contract for the SS API client passed into Signal 2.

    Production callers pass a real client implementing the protocol at
    `deep-research/references/semantic_scholar_api_protocol.md`
    (429 → 2s backoff × 3, DOI-first then title-similarity fallback).
    Tests pass a MagicMock returning whatever shape the test specifies."""

    def lookup(self, entry: Mapping[str, Any]) -> Mapping[str, Any]:
        """Return {"matched": bool, ...}. Raise SemanticScholarUnavailable
        on transient API failures (after the protocol's retry budget is
        exhausted)."""
        ...


def reset_client_outage_latch(client: SemanticScholarClient) -> None:
    """Best-effort latch reset (#115 R5-3): production clients implementing
    the outage-latch pattern expose `reset_outage_latch()`; minimal mocks
    in tests may not. This helper invokes it when present, no-ops when
    absent. Long-running tools call this between passport batches."""
    reset = getattr(client, "reset_outage_latch", None)
    if callable(reset):
        reset()


def compute_preprint_signal(entry: Mapping[str, Any]) -> bool:
    """Signal 1 per v3.7.3 spec §3.2 Vector 1.

    True iff `year >= 2024 AND venue resolves to a preprint server`.
    Venue resolution per spec: prefer the explicit `venue` field; when
    absent, infer from `source_pointer` (e.g., 'https://arxiv.org/abs/...'
    → arXiv). Missing year, or venue that resolves to neither a preprint
    server nor an inferable pointer, returns False.

    Source-pointer inference: legacy entries that schema-validly omit
    `venue` but carry a preprint URL in `source_pointer` must still surface
    the CONTAMINATED-PREPRINT signal (per v3.7.3 §3.2 Vector 1 — `venue`
    absence is not a negative).
    """
    year = entry.get("year")
    if not isinstance(year, int) or year < 2024:
        return False
    venue = entry.get("venue")
    if venue in PREPRINT_VENUES:
        return True
    if not isinstance(venue, str):
        pointer = entry.get("source_pointer")
        if isinstance(pointer, str):
            return _infer_venue_from_pointer(pointer) in PREPRINT_VENUES
    return False


def compute_ss_unmatched_signal(
    entry: Mapping[str, Any],
    client: SemanticScholarClient,
    *,
    cache=None,
) -> bool | None:
    """Signal 2 per v3.7.3 spec §3.2 Vector 2.

    Returns:
      - None if `obtained_via='manual'` (spec exemption) OR API degradation
      - True if SS lookup returns no match
      - False if SS lookup returns a match

    Per spec emission rules, None means OMIT the field from the
    contamination_signals object (NOT set to False — that would imply
    "checked and found", which is not what happened).

    cache: optional VerificationCache (spec §2 Delta 2). The S2 wrapper is the
    resolver layer for S2 (its `lookup` is the lone entry-keyed client method),
    so it shares the same `_cached_verdict` path as the other three resolvers.
    A degradation returns None and is NEVER cached (absent != false): the
    SemanticScholarUnavailable raised by `lookup` propagates out of `compute`
    (uncached, since the put runs only on success) and is caught here to yield
    None. cache=None is byte-equivalent to no caching.
    """
    if entry.get("obtained_via") == "manual":
        return None
    try:
        return _cached_verdict(
            cache=cache,
            citation_key=entry.get("citation_key"),
            resolver_name="semantic_scholar",
            query_form=_query_form(
                id_label="doi",
                id_value=entry.get("doi"),
                title=entry.get("title", ""),
            ),
            # S2's lookup() does DOI-first then title internally, so queried_by
            # follows the same has-an-id rule as the other resolvers (C-V6(a)).
            compute=lambda: (
                not bool(client.lookup(entry).get("matched", False)),
                None,
                queried_by_for(entry, id_field="doi"),
            ),
        )
    except SemanticScholarUnavailable:
        return None  # degradation → omit field, never cached


def queried_by_for(entry: Mapping[str, Any], *, id_field: str) -> str:
    """The C-V6(a) queried_by value for an entry: 'id' when the entry carries the
    resolver's exact identifier (so an ID-keyed lookup is attempted), else
    'title'. The SINGLE definition of this rule — all resolver paths (DOI-keyed,
    arXiv-keyed, and S2's entry-keyed lookup) derive queried_by through here so
    the narrowed-false signal can never drift across layers."""
    return "id" if entry.get(id_field) else "title"


def _query_form(*, id_label: str, id_value: str | None, title: str) -> str:
    """Canonical cache query_form keying the WHOLE resolver attempt.

    A resolver may try the exact ID, miss, then fall through to title search;
    keying only on the ID would cache a title-hit verdict under the ID and
    falsely imply the ID resolved. So the query_form captures both inputs of
    the attempt: e.g. "doi:10.5/x|title:Attention...".
    The cache key already namespaces by citation_key + resolver_name, so this
    string never needs to disambiguate across citations or resolvers."""
    return f"{id_label}:{id_value or ''}|title:{title}"


def _cached_verdict(
    *,
    cache,
    citation_key,
    resolver_name: str,
    query_form: str,
    compute,
) -> bool | None:
    """Wrap a verdict computation with the persistent cache (spec §2 Delta 2).

    `compute()` returns `(unmatched: bool, matched_by: str | None,
    queried_by: str)`. On a cache hit the network call is skipped and the stored
    verdict is returned. On a miss the live `compute()` runs and the verdict is
    persisted (negatives included, so repeat runs don't re-hammer the API).
    `cache=None` is byte-equivalent to no caching. Degradation exceptions
    propagate from `compute()` and are NEVER cached (the caller omits the field).

    The stored payload carries `matched_by` + `queried_by` so a cached negative
    keeps the C-V6(a) ID-keyed signal the narrowed-false reducer needs.
    """
    if cache is None:
        unmatched, _, _ = compute()
        return unmatched
    cached = cache.get(citation_key, resolver_name, query_form)
    # #431 §0.12.3b: a hit is reusable ONLY when its stored decision version
    # matches the current logic. A row missing `matched` (written by an
    # older/other tool) OR carrying a stale/absent decision version (e.g. any
    # pre-v5 `matched_by=title` row written under the author-agree tiers) is
    # treated as a MISS — forcing a live recompute under the current logic
    # rather than reusing a verdict a different decision path produced. Without
    # this the #431 pivot is a no-op for every citation already cached.
    if (
        cached is not None
        and "matched" in cached
        and cached.get("decision_version") == RESOLVER_DECISION_VERSION
    ):
        return not cached["matched"]
    unmatched, matched_by, queried_by = compute()
    # query_form is the cache key, not part of the value — no need to echo it
    # into the stored payload (nothing reads it back). The decision version is
    # stamped into the value so a future run under a newer logic re-resolves.
    cache.put(
        citation_key,
        resolver_name,
        query_form,
        {"matched": not unmatched, "matched_by": matched_by,
         "queried_by": queried_by,
         "decision_version": RESOLVER_DECISION_VERSION},
    )
    return unmatched


def _resolve_doi_then_title(
    entry: Mapping[str, Any], client,
) -> tuple[bool, str | None, str]:
    """Run the DOI-then-title resolver flow, returning
    (unmatched, matched_by, queried_by).

    matched_by ∈ {'doi', 'title', None}: which channel produced a match.
    queried_by ∈ {'id', 'title'}: what the resolver ACTUALLY queried by —
      'id' when a DOI was present (so an exact-key lookup was attempted, even
      if it then fell through to title), 'title' when no DOI was available to
      key on. This is the C-V6(a) signal: an `unmatched` with queried_by='id'
      is fabrication evidence (a provably-bogus identifier); queried_by='title'
      is a coverage gap (reduce to unresolvable, not false). It reflects
      execution, not entry shape — see #182 Delta 4 / C-V6(a).

    Exception-type differentiation stays at the wrapper — this helper never
    catches."""
    title = entry.get("title", "")
    doi = entry.get("doi")
    queried_by = queried_by_for(entry, id_field="doi")
    if doi:
        hit = client.doi_lookup_with_title_check(doi, title)
        if hit is not None:
            return False, "doi", queried_by
        # DOI miss or MISMATCH — fall through to title search.
    hit = client.title_search(title)
    if hit is not None:
        return False, "title", queried_by
    return True, None, queried_by


def _resolve_by_doi_then_title(
    entry: Mapping[str, Any], client, *, resolver_name: str, cache=None,
) -> bool | None:
    """Shared body for resolve_openalex_unmatched / resolve_crossref_unmatched.
    See those wrappers for the spec contract."""
    if entry.get("obtained_via") == "manual":
        return None
    title = entry.get("title", "")
    return _cached_verdict(
        cache=cache,
        citation_key=entry.get("citation_key"),
        resolver_name=resolver_name,
        query_form=_query_form(
            id_label="doi", id_value=entry.get("doi"), title=title
        ),
        compute=lambda: _resolve_doi_then_title(entry, client),
    )


def resolve_openalex_unmatched(
    entry: Mapping[str, Any], client, *, cache=None,
) -> bool | None:
    """Compute openalex_unmatched per spec v3.9.0 §3.4.

    Mirrors resolve_semantic_scholar_unmatched semantics:
    - Manual entry → return None (caller MUST omit field).
    - API down → re-raise OpenAlexUnavailable (caller MUST omit field).
    - DOI present + DOI hit (passes title cross-check) → return False.
    - DOI present + DOI miss/MISMATCH → fall through to title search.
    - DOI absent → title search only.
    - No hit anywhere → return True (unmatched).

    Returns:
        True: OpenAlex returned no match by DOI (with title cross-check) or title.
        False: OpenAlex found a match.
        None: obtained_via='manual' → exempt, caller must omit field.

    Raises:
        OpenAlexUnavailable: API degraded, caller must omit field per R-L3-2-C.

    cache: optional VerificationCache (spec §2 Delta 2). cache=None is
        byte-equivalent to no caching.
    """
    return _resolve_by_doi_then_title(
        entry, client, resolver_name="openalex", cache=cache
    )


def resolve_crossref_unmatched(
    entry: Mapping[str, Any], client, *, cache=None,
) -> bool | None:
    """Compute crossref_unmatched per spec v3.9.0 §3.5.

    Mirrors resolve_openalex_unmatched / resolve_semantic_scholar_unmatched
    semantics. See those functions for return / raise contract.

    Returns:
        True / False / None per the same contract as resolve_openalex_unmatched.

    Raises:
        CrossrefUnavailable: API degraded, caller must omit field per R-L3-2-C.

    cache: optional VerificationCache (spec §2 Delta 2). cache=None is
        byte-equivalent to no caching.
    """
    return _resolve_by_doi_then_title(
        entry, client, resolver_name="crossref", cache=cache
    )


def _resolve_arxiv_id_then_title(
    entry: Mapping[str, Any], client,
) -> tuple[bool, str | None, str]:
    """arXiv-specific resolver flow (ID-keyed, not DOI-keyed), returning
    (unmatched, matched_by, queried_by). matched_by ∈ {'arxiv', 'title', None};
    queried_by ∈ {'id', 'title'} per the C-V6(a) signal (see
    _resolve_doi_then_title). 'id' when an arXiv ID was present. Never catches —
    exception differentiation stays at the wrapper.

    Precondition: only called for entries carrying an arxiv_id — both callers
    (`resolve_arxiv_unmatched` and verification_gate `_run_arxiv`) skip the
    resolver when arxiv_id is absent (#331), so the ID lookup always runs and a
    title search is only the ID-miss fallback."""
    title = entry.get("title", "")
    queried_by = queried_by_for(entry, id_field="arxiv_id")
    hit = client.arxiv_id_lookup(entry.get("arxiv_id"), title)
    if hit is not None:
        return False, "arxiv", queried_by
    # ID miss or MISMATCH — fall through to title search.
    hit = client.title_search(title)
    if hit is not None:
        return False, "title", queried_by
    return True, None, queried_by


def resolve_arxiv_unmatched(
    entry: Mapping[str, Any], client, *, cache=None,
) -> bool | None:
    """Compute arxiv_unmatched per spec v3.11 #182 Delta 1.

    Differs from resolve_crossref_unmatched / resolve_openalex_unmatched in
    its exact-key channel: arXiv is keyed by `entry['arxiv_id']` (not 'doi'),
    and the client's exact-key method is `arxiv_id_lookup` (not
    `doi_lookup_with_title_check`). The title fallback is identical.

    - Manual entry → return None (caller MUST omit field).
    - arXiv ID absent → SKIP the resolver, return None (caller MUST omit field).
      A non-arXiv citation is not title-searched against arXiv: a title miss
      there is a coverage gap, not non-existence evidence (#331). The spec keys
      the arXiv index on arxiv_id and states arxiv_unmatched is absent on
      citations with no arXiv ID ('arXiv resolver skipped on a non-arXiv
      citation per Delta 1', spec §4; orchestrator k_max rule).
    - arXiv ID present + ID hit (passes title cross-check) → return False.
    - arXiv ID present + ID miss/MISMATCH → fall through to title search.
    - No hit anywhere → return True (unmatched).

    Returns:
        True: arXiv returned no match by ID (with title cross-check) or title.
        False: arXiv found a match.
        None: obtained_via='manual' OR no arxiv_id → skipped, caller omits field.

    Raises:
        ArxivUnavailable: API degraded, caller must omit field per R-L3-2-C.

    cache: optional VerificationCache (spec §2 Delta 2). cache=None is
        byte-equivalent to no caching.
    """
    if entry.get("obtained_via") == "manual":
        return None
    # #331: no arXiv ID → resolver is skipped (no network, not cached — a skip
    # is resolver applicability, not an adjudication, so it never persists).
    if not entry.get("arxiv_id"):
        return None
    return _cached_verdict(
        cache=cache,
        citation_key=entry.get("citation_key"),
        resolver_name="arxiv",
        query_form=_query_form(
            id_label="arxiv",
            id_value=entry.get("arxiv_id"),
            title=entry.get("title", ""),
        ),
        compute=lambda: _resolve_arxiv_id_then_title(entry, client),
    )


def build_signals_object(
    entry: Mapping[str, Any],
    client: SemanticScholarClient,
    arxiv_client=None,
    *,
    cache=None,
) -> dict[str, bool]:
    """Construct the `contamination_signals` object for `entry`.

    Per v3.7.3 spec §3.2 emission rules:
      - Both signals computed → emit both fields (even when both False:
        "computed and found clean" is distinct from "not computed")
      - Manual entry → omit `semantic_scholar_unmatched` field
      - API degradation → omit `semantic_scholar_unmatched` field

    cache: optional VerificationCache (spec §2 Delta 2), threaded into both the
    S2 and arXiv resolvers. cache=None is byte-equivalent to no caching.
    """
    obj: dict[str, bool] = {
        "preprint_post_llm_inflection": compute_preprint_signal(entry),
    }
    ss = compute_ss_unmatched_signal(entry, client, cache=cache)
    if ss is not None:
        obj["semantic_scholar_unmatched"] = ss
    # v3.11 #182 Delta 1: arxiv signal is opt-in via an explicit client so the
    # v3.7.3 caller (migrate_literature_corpus_to_v3_7_3) stays byte-equivalent
    # (no client → no field). Manual exemption + API degradation both omit the
    # field (resolve returns None / raises), matching the ss field's rules.
    if arxiv_client is not None:
        try:
            ax = resolve_arxiv_unmatched(entry, arxiv_client, cache=cache)
        except ArxivUnavailable:
            ax = None
        if ax is not None:
            obj["arxiv_unmatched"] = ax
    return obj
