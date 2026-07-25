---
description: ARS /ars-cache-invalidate — drop cached verification entries for a citation key
model: sonnet
---

Invalidate the persistent verification cache for one citation key, so the next pipeline run re-verifies it live against Crossref / OpenAlex / Semantic Scholar / arXiv instead of returning a stale cached verdict. Use this when a citation's metadata changed (e.g. a preprint gained a published DOI) or when a prior verification looks wrong.

The cache (spec v3.11 #182 Delta 2) is a local SQLite store at `~/.cache/ars/verification.db` (override via `ARS_VERIFICATION_CACHE_PATH`), keyed by `(citation_key, resolver_name, query_form)` with a 90-day TTL. This command removes **every** cached entry for the named citation key (all four resolvers, all query forms); other citations are untouched. It is idempotent — invalidating a key with no cached rows succeeds as a no-op.

To invalidate the **entire** cache at once (e.g. after a systemic resolver bug cached many false negatives), delete the database file directly: `rm ~/.cache/ars/verification.db`. It is recreated empty on the next run.

Implementation:
```bash
python3 scripts/ars_cache_invalidate.py $ARGUMENTS
```

Mode reference: `docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md` §2 Delta 2.
