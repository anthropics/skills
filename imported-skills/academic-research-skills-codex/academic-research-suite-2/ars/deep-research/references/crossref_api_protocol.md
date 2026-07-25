# Crossref API Verification Protocol

**Status**: v3.9.0
**Used by**: `bibliography_agent`, `migrate_literature_corpus_to_v3_9_0.py`
**API base**: `https://api.crossref.org`
**Rate limit**: 10 req/s (polite pool, with `mailto:` in User-Agent), ~5 req/s (anonymous, varies). Confirmed via live `x-rate-limit-limit` / `x-rate-limit-interval` response headers (2026-05).
**Polite email env var**: `CROSSREF_POLITE_EMAIL` (optional)

---

## Purpose

Provides a third bibliographic-index lookup for v3.9.0 cross-index triangulation per spec v3.9.0 §3.5. Crossref is the DOI registry of record — strongest coverage for journal articles with DOIs. Monograph / chapter coverage is partial (publisher participation dependent). v3.9.0 surfaces `crossref_unmatched` as one of three signals, handled per R-L3-2-A (advisory by default; a user-enabled `contamination_triangulation` strict policy may promote the k=3 triangulation signal to a terminal block — see `shared/references/firm_rules.md`).

Mirrors the structure of `semantic_scholar_api_protocol.md` and `openalex_api_protocol.md`.

## Query Patterns

### Pattern 1: DOI Lookup with Title Cross-Check (primary when DOI is available)

```
GET /works/{doi}
```

Note: raw DOI in path, NO `doi:` prefix (Crossref convention; OpenAlex uses `/works/doi:{doi}`).

**Matching rule (mirrors S2 `DOI_MISMATCH` pattern):** DOI lookup hits are gated by a Levenshtein 0.70 title cross-check. Crossref returns `title` as a list of language variants; the first entry is compared. If similarity below threshold -> DOI_MISMATCH, return None, fall through to title search.

### Pattern 2: Title Search (fallback when DOI absent or DOI_MISMATCH)

```
GET /works?query.title={url_encoded_title}&rows=5
```

**Matching rule:** Levenshtein similarity >= 0.70 (matching S2 / OpenAlex / PaperOrchestra threshold). When multiple candidates pass, prefer matching-year tiebreaker via +0.05 score bonus. Crossref year lives in `issued.date-parts[0][0]` (canonical); fall through to `published-print` / `published-online` if `issued` absent.

## `crossref_unmatched` derivation

`true` if and only if:
- DOI present: DOI lookup either returns 404, misses title cross-check, AND title search returns no match meeting threshold; OR
- DOI absent: title search alone returns no match meeting threshold.

The check fires only when `obtained_via != 'manual'`.

## Degradation handling

| Condition | Action |
|---|---|
| HTTP 404 on DOI | Treat as miss -- return `{}` from `_get`; caller falls through to title search. NOT a degradation. |
| HTTP 429 (rate limit) | Back off 2 seconds, retry up to 3 times. After exhaustion, raise `CrossrefUnavailable`. Throttle anchor refreshed after each backoff. |
| HTTP 5xx | Raise `CrossrefUnavailable` immediately (no retry). |
| Network timeout (30s default) | Raise `CrossrefUnavailable`. |
| `CrossrefUnavailable` raised | Caller MUST omit `crossref_unmatched` from the entry (per spec v3.9.0 R-L3-2-C: absent != false). Other indexes proceed independently. |

## v3.9.0 R-L3-2-D constraint

Crossref returns `type` (e.g., `journal-article`, `book-chapter`). **v3.9.0 ignores this field.** Not stored on entries, not surfaced to finalizer, not used in any derivation. v3.10 will introduce adapter-declared `venue_type` with explicit provenance.

## Crossref-specific notes

- **Coverage caveat:** strongest for journal articles with DOIs. Monograph / chapter coverage depends on publisher DOI registration. Conference proceedings vary. This asymmetry is by design -- combined with S2 and OpenAlex, the three-index signal captures different genre profiles.
- **Polite pool etiquette:** the `mailto:` in User-Agent header (not query param) follows Crossref's documented convention for higher rate limits.

## Client implementation

See `scripts/crossref_client.py`. Class `CrossrefClient` exposes `doi_lookup_with_title_check(doi, expected_title)` and `title_search(title, year=None)`. Both return `dict | None` (the dict being either the `message` for DOI, or one item from `message.items` for title search). Both raise `CrossrefUnavailable` on degradation per the table above.

## Cross-references

- Spec: `docs/design/2026-05-17-ars-v3.9.0-cross-index-triangulation-measurement-spec.md` §3.5
- Mirror template: `deep-research/references/semantic_scholar_api_protocol.md`
- Sibling protocol: `deep-research/references/openalex_api_protocol.md`
