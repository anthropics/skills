#!/usr/bin/env python3
"""Minimal Semantic Scholar API client wrapper.

Implements the lookup contract documented at
`deep-research/references/semantic_scholar_api_protocol.md` for the
v3.7.3 contamination-signals migration tool (#105). DOI-first, title-
similarity fallback, 429 backoff per the protocol's retry budget.

Not a general-purpose S2 client — this is the migration tool's narrow
need (single-paper existence check). When ARS later adds a broader S2
helper, this module's `SemanticScholarClient` class should satisfy the
contamination_signals.SemanticScholarClient Protocol so the migration
tool can switch over without code changes.
"""
from __future__ import annotations

import os
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any, Mapping

# Dual-path import: try sibling-style first (scripts/-on-sys.path, used by
# tests and direct CLI invocation) so module identity matches when callers
# import via the sibling path. Fall back to `scripts.<module>` (namespace
# package style, repo-root PYTHONPATH). Same pattern as scripts/slr_lineage.py.
try:
    from _text_similarity import (
        _BACKOFF_SECONDS,
        _MAX_RETRIES,
        _TITLE_SIMILARITY_THRESHOLD,
        _normalize_title,
        _similarity,
        exact_normalized_title,
        generic_title,
    )
    from contamination_signals import SemanticScholarUnavailable
except ImportError:
    from scripts._text_similarity import (
        _BACKOFF_SECONDS,
        _MAX_RETRIES,
        _TITLE_SIMILARITY_THRESHOLD,
        _normalize_title,
        _similarity,
        exact_normalized_title,
        generic_title,
    )
    from scripts.contamination_signals import SemanticScholarUnavailable


# Per protocol: api.semanticscholar.org/graph/v1, 1 req/s unauthenticated.
_API_BASE = "https://api.semanticscholar.org/graph/v1"
_API_HOST = "api.semanticscholar.org"
_API_KEY_ENV = "S2_API_KEY"
_FIELDS = "title,authors,year,externalIds,venue,publicationDate"

# Per protocol line 6: unauthenticated tier is ~1 req/s, authenticated
# (S2_API_KEY) tier is 10 req/s. Default throttle interval defends
# against proactive rate limiting before a 429 fires (#115 R5-2).
_UNAUTHENTICATED_MIN_INTERVAL = 1.0
_AUTHENTICATED_MIN_INTERVAL = 0.1


def _require_api_url(url: str) -> None:
    parsed = urllib.parse.urlsplit(url)
    if parsed.scheme != "https" or parsed.netloc != _API_HOST:
        raise SemanticScholarUnavailable(f"Refusing non-S2 URL: {url}")


class SemanticScholarClient:
    """Production lookup-by-(doi-then-title) client for v3.7.3 backfill.

    Satisfies `contamination_signals.SemanticScholarClient` Protocol.
    Tests inject MagicMocks; production callers use this concrete class.

    Concurrency note: rate-limit pacing is per-instance. A migration tool
    that spawns N concurrent clients will issue N × (1 req/s) outbound
    even though each instance respects the throttle, blowing past the
    protocol's 1 req/s unauthenticated limit and triggering 429s. Share
    a single instance across a migration run.
    """

    def __init__(
        self,
        api_key: str | None = None,
        sleep: Any = time.sleep,
        clock: Any = time.monotonic,
        min_interval_seconds: float | None = None,
    ) -> None:
        self._api_key = api_key or os.environ.get(_API_KEY_ENV)
        self._sleep = sleep
        self._clock = clock
        if min_interval_seconds is None:
            # Auto-pick tier from API key presence (#115 R5-2).
            self._min_interval = (
                _AUTHENTICATED_MIN_INTERVAL if self._api_key
                else _UNAUTHENTICATED_MIN_INTERVAL
            )
        else:
            self._min_interval = min_interval_seconds
        # Pacing state: timestamp of last request. None = no prior call.
        self._last_request_at: float | None = None
        # Outage latch (#115 R5-3): once URLError fires, short-circuit
        # subsequent calls until reset_outage_latch() is invoked.
        self._latched_unavailable: bool = False

    def reset_outage_latch(self) -> None:
        """Clear the outage latch so the next lookup retries the network.

        Long-running tools (e.g., per-passport-batch migration runs) can
        call this between batches to attempt recovery. Per protocol
        §"On API failure": network errors skip the remaining batch;
        this method is the explicit "next batch starts fresh" signal.
        """
        self._latched_unavailable = False

    def lookup(self, entry: Mapping[str, Any]) -> Mapping[str, Any]:
        """Return {"matched": bool, "paperId": str | None}.

        Failure semantics:
        - HTTP 5xx → SemanticScholarUnavailable for THIS reference only
          (server-side error; subsequent lookups retry normally).
        - URLError (network-level) → SemanticScholarUnavailable AND
          latches the client unavailable. Subsequent lookups short-
          circuit without invoking urlopen until reset_outage_latch().
          Per protocol §"On API failure": skip S2 for remaining batch.

        Per protocol §"Query Patterns" + §"Response Handling":
        `semantic_scholar_unmatched` is True only when NEITHER DOI nor
        title lookup yields a hit. So:

        1. If `doi` present → GET /paper/DOI:{doi}; on hit, cross-check
           returned title (Levenshtein ≥ 0.70). DOI_MISMATCH (title
           differs despite DOI hit) AND DOI-404 BOTH fall through to (2)
           rather than returning no-match immediately — the v3.7.3
           Vector 2 contract requires both DOI AND title to miss before
           setting the signal. Codex R2-2 closure.
        2. Title search: GET /paper/search?query={url-encoded-title};
           pick the top result with title similarity ≥ 0.70, prefer
           matching year.

        Raises SemanticScholarUnavailable on:
        - HTTP 429 after exhausting `_MAX_RETRIES` retries
        - HTTP 5xx
        - Network error (URLError)
        """
        doi = entry.get("doi")
        title = entry.get("title") or ""
        if doi:
            doi_result = self._lookup_by_doi(doi, title)
            if doi_result["matched"]:
                return doi_result
            # DOI miss or DOI_MISMATCH: fall through to title search
            # per protocol §Vector 2 "neither DOI nor title" rule.
        if title:
            return self._lookup_by_title(title, entry.get("year"))
        return {"matched": False, "paperId": None}

    def _request(self, path: str) -> dict[str, Any]:
        # Latch short-circuit (#115 R5-3): if a prior URLError marked
        # the network dead, fail fast without trying again.
        if self._latched_unavailable:
            raise SemanticScholarUnavailable(
                "S2 API latched unavailable after prior network failure; "
                "call reset_outage_latch() to retry."
            )

        # Throttle (#115 R5-2): pace requests at the protocol's rate
        # limit. First call passes through (no prior timestamp). Update
        # `_last_request_at` to "now" before issuing the request so all
        # exit paths (success, 404, 5xx, HTTPError, 429-retry) leave a
        # fresh anchor for the next outer call. 429 retries below
        # re-update after their backoff sleep so the anchor reflects
        # actual wall time even when retries land in a slow second.
        if self._last_request_at is not None and self._min_interval > 0:
            elapsed = self._clock() - self._last_request_at
            remaining = self._min_interval - elapsed
            if remaining > 0:
                self._sleep(remaining)
        self._last_request_at = self._clock()

        url = f"{_API_BASE}{path}"
        _require_api_url(url)
        headers = {"User-Agent": "ARS-migration/1.0"}
        if self._api_key:
            headers["x-api-key"] = self._api_key
        req = urllib.request.Request(url, headers=headers)

        for attempt in range(_MAX_RETRIES + 1):
            try:
                # URL is fixed-host HTTPS after _require_api_url().
                with urllib.request.urlopen(req, timeout=30) as resp:  # nosec B310
                    import json
                    return json.loads(resp.read().decode("utf-8"))
            except urllib.error.HTTPError as e:
                if e.code == 404:
                    return {}
                if e.code == 429 and attempt < _MAX_RETRIES:
                    self._sleep(_BACKOFF_SECONDS)
                    # F5 closure (simplify efficiency): refresh anchor
                    # after each 429 backoff so the next outer _request
                    # paces against actual wake time, not entry time.
                    # Without this the next outer call may under-sleep
                    # (because elapsed counts the 2s × N backoff time)
                    # and re-trigger 429.
                    self._last_request_at = self._clock()
                    continue
                if 500 <= e.code < 600:
                    raise SemanticScholarUnavailable(
                        f"S2 API HTTP {e.code}"
                    ) from e
                raise SemanticScholarUnavailable(
                    f"S2 API HTTP {e.code} after {_MAX_RETRIES} retries"
                ) from e
            except urllib.error.URLError as e:
                # Network-level failure: latch the client so subsequent
                # lookups in the same batch fail fast (#115 R5-3).
                # Per protocol §"On API failure": skip S2 for remaining
                # batch on network error.
                self._latched_unavailable = True
                raise SemanticScholarUnavailable(f"S2 API network error: {e}") from e
            except (OSError, TimeoutError) as e:
                # Response-body read timeouts (socket.timeout subclasses
                # OSError; TimeoutError is the 3.10+ alias) and other
                # transient I/O failures during resp.read() must be
                # treated as API degradation per spec — never let them
                # abort the migration. Codex R4-2 closure.
                #
                # Also latch the client (codex #115 R2 closure): the
                # protocol §"On API failure" rule "skip S2 for remaining
                # batch on network error" covers transport-level
                # failures, which include connection resets / socket
                # read timeouts that surface during resp.read(), not
                # only URLError at urlopen() time. Without this latch,
                # a real network outage produces 30s read-timeout per
                # entry × N entries.
                self._latched_unavailable = True
                raise SemanticScholarUnavailable(
                    f"S2 API I/O failure during response read: {e}"
                ) from e
        raise SemanticScholarUnavailable(f"S2 API exhausted {_MAX_RETRIES} retries")

    def _lookup_by_doi(self, doi: str, expected_title: str) -> dict[str, Any]:
        data = self._request(
            f"/paper/DOI:{urllib.parse.quote(doi, safe='')}?fields={_FIELDS}"
        )
        if not data or not data.get("paperId"):
            return {"matched": False, "paperId": None}
        # Per protocol: cross-check title; DOI_MISMATCH counts as no-match
        # for this binary signal.
        returned_title = data.get("title") or ""
        if _similarity(expected_title, returned_title) < _TITLE_SIMILARITY_THRESHOLD:
            return {"matched": False, "paperId": None}
        return {"matched": True, "paperId": data["paperId"]}

    def _lookup_by_title(self, title: str, year: int | None) -> dict[str, Any]:
        """Title search under the #431 exact-title-or-bust gate.

        A candidate matches iff it clears the 0.70 ratio AND is an exact
        normalized title match (§0.12.1); the candidate dict must be inspected
        for its title here (the pre-#431 version discarded it, keeping only
        paperId, so it could not apply the exact gate). A non-exact high-ratio
        title is never promoted on year alone. On the title-fallback path no ID
        corroborates, so an exact-but-generic title (§0.12.2) is not promoted.
        A no-exact loop returns no match → the resolver reduces the title-keyed
        miss to `unresolvable` (never a false `matched`)."""
        if generic_title(title):
            return {"matched": False, "paperId": None}
        path = (
            f"/paper/search?query={urllib.parse.quote(title)}"
            f"&limit=5&fields={_FIELDS}"
        )
        data = self._request(path)
        candidates = data.get("data") or []
        best: tuple[float, dict[str, Any]] | None = None
        for cand in candidates:
            cand_title = cand.get("title") or ""
            sim = _similarity(title, cand_title)
            if sim < _TITLE_SIMILARITY_THRESHOLD:
                continue
            if not exact_normalized_title(title, cand_title):
                continue
            # Per protocol: prefer matching year when multiple ≥0.70 results.
            year_match = year is not None and cand.get("year") == year
            score = sim + (0.05 if year_match else 0.0)
            if best is None or score > best[0]:
                best = (score, cand)
        if best is None:
            return {"matched": False, "paperId": None}
        return {"matched": True, "paperId": best[1].get("paperId")}
