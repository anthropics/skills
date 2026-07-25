#!/usr/bin/env python3
"""Minimal OpenAlex API client wrapper.

Implements the lookup contract documented at
`deep-research/references/openalex_api_protocol.md`. DOI-first with
title cross-check (DOI_MISMATCH pattern), title-similarity fallback,
429 → budget-exhausted fail-fast or exponential backoff × 3 retries,
5xx → skip. Mirrors `semantic_scholar_client.py` structure for code
locality.
"""
from __future__ import annotations

import http.client
import json
import os
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any, Mapping

# Dual-path import: sibling-first (so module identity matches when callers
# import via the sibling path, e.g. tests), namespace-package fallback (for
# repo-root `import scripts.openalex_client`). See semantic_scholar_client.py
# for the identity-matching rationale.
try:
    from _text_similarity import (
        _BACKOFF_SECONDS,
        _MAX_RETRIES,
        _TITLE_SIMILARITY_THRESHOLD,
        _similarity,
        exact_normalized_title,
        generic_title,
    )
except ImportError:
    from scripts._text_similarity import (
        _BACKOFF_SECONDS,
        _MAX_RETRIES,
        _TITLE_SIMILARITY_THRESHOLD,
        _similarity,
        exact_normalized_title,
        generic_title,
    )


_API_BASE = "https://api.openalex.org"
_API_HOST = "api.openalex.org"
_API_KEY_ENV = "OPENALEX_API_KEY"
_POLITE_EMAIL_ENV = "OPENALEX_POLITE_EMAIL"
_FIELDS = "id,title,authorships,publication_year,doi,primary_location"

_AUTHENTICATED_MIN_INTERVAL = 0.1
_ANONYMOUS_MIN_INTERVAL = 1.0


def _require_api_url(url: str) -> None:
    parsed = urllib.parse.urlsplit(url)
    if parsed.scheme != "https" or parsed.netloc != _API_HOST:
        # Strip the query from the message: it can carry api_key, which
        # must never land in logs / raised-exception text.
        redacted = urllib.parse.urlunsplit(
            (parsed.scheme, parsed.netloc, parsed.path, "", "")
        )
        raise OpenAlexUnavailable(f"Refusing non-OpenAlex URL: {redacted}")


def _daily_budget_exhausted(headers: Any) -> bool:
    """True iff a 429 carries `X-RateLimit-Remaining: 0` — OpenAlex's
    daily-budget exhaustion signal (budget refills at midnight UTC), where
    an in-process retry seconds later cannot succeed. A 429 without the
    header, or with budget remaining, is transient burst limiting
    (>100 req/s) and stays on the retry path."""
    if headers is None:
        return False
    value = headers.get("X-RateLimit-Remaining")
    if value is None:
        return False
    try:
        return int(value) == 0
    except (ValueError, TypeError):
        return False


class OpenAlexUnavailable(Exception):
    """OpenAlex API degraded — caller MUST omit `openalex_unmatched`."""


class OpenAlexClient:
    """Production lookup-by-(doi-with-cross-check-then-title) client.

    Concurrency note: rate-limit pacing is per-instance. Share a single
    instance across a migration run.
    """

    def __init__(
        self, polite_email: str | None = None, api_key: str | None = None,
    ):
        # api_key is the OpenAlex-documented auth mechanism (free key, 10×
        # the keyless daily budget). polite_email predates it: the polite
        # pool is no longer in OpenAlex's docs but `mailto` is still sent
        # for backward compatibility when configured. Either credential
        # selects the authenticated pacing tier.
        self._api_key = api_key or os.environ.get(_API_KEY_ENV)
        self._polite_email = polite_email or os.environ.get(_POLITE_EMAIL_ENV)
        self._min_interval = (
            _AUTHENTICATED_MIN_INTERVAL
            if (self._api_key or self._polite_email)
            else _ANONYMOUS_MIN_INTERVAL
        )
        self._last_request_at: float | None = None

    def _throttle(self) -> None:
        if self._last_request_at is None:
            return
        # time.monotonic for elapsed measurement: NTP / manual clock
        # adjustments can make time.time go backward, producing negative
        # elapsed and either huge sleep or zero sleep (#128 §6). Aligns
        # with semantic_scholar_client.py.
        elapsed = time.monotonic() - self._last_request_at
        if elapsed < self._min_interval:
            time.sleep(self._min_interval - elapsed)

    def _get(self, path: str, query: Mapping[str, str]) -> dict[str, Any]:
        params = dict(query)
        if self._api_key:
            params["api_key"] = self._api_key
        if self._polite_email:
            params["mailto"] = self._polite_email
        url = f"{_API_BASE}{path}?{urllib.parse.urlencode(params)}"
        _require_api_url(url)
        req = urllib.request.Request(url, headers={"User-Agent": "ARS-v3.9.0"})

        self._throttle()
        self._last_request_at = time.monotonic()

        for attempt in range(_MAX_RETRIES + 1):
            try:
                # URL is fixed-host HTTPS after _require_api_url().
                with urllib.request.urlopen(req, timeout=30) as resp:  # nosec B310
                    # Wrap response body read + decode + parse in a narrow
                    # except so transient socket drops mid-stream, garbled
                    # bodies, or HTML error pages slipped through with 200
                    # status surface as OpenAlexUnavailable — honoring the
                    # v3.9.0 spec §3.7 per-API degradation contract (one
                    # transient failure must drop only openalex_unmatched,
                    # not abort the whole backfill).
                    try:
                        body = resp.read()
                        return json.loads(body.decode("utf-8"))
                    except (
                        OSError,
                        http.client.HTTPException,
                        UnicodeDecodeError,
                        json.JSONDecodeError,
                    ) as e:
                        # http.client.HTTPException covers IncompleteRead
                        # (truncated body — canonical mid-stream socket drop)
                        # which inherits HTTPException, not OSError. Codex
                        # review v3.9.1 R1 P2.
                        raise OpenAlexUnavailable(
                            f"OpenAlex response read/parse failed: {e}"
                        ) from e
            except urllib.error.HTTPError as e:
                if e.code == 404:
                    return {}
                if e.code == 429:
                    if _daily_budget_exhausted(e.headers):
                        raise OpenAlexUnavailable(
                            "OpenAlex daily budget exhausted "
                            "(X-RateLimit-Remaining: 0, refills midnight UTC)"
                        ) from e
                    if attempt < _MAX_RETRIES:
                        # Exponential backoff (2s → 4s → 8s) per OpenAlex's
                        # documented guidance for transient burst 429s.
                        time.sleep(_BACKOFF_SECONDS * (2 ** attempt))
                        # Refresh anchor after backoff so the next _throttle()
                        # paces against actual wake time, not entry time.
                        # Without this the next call may under-sleep (elapsed
                        # already counts the backoff) and re-trigger 429.
                        self._last_request_at = time.monotonic()
                        continue
                raise OpenAlexUnavailable(f"OpenAlex HTTP {e.code}: {e.reason}") from e
            except (urllib.error.URLError, TimeoutError) as e:
                raise OpenAlexUnavailable(f"OpenAlex network error: {e}") from e

        raise OpenAlexUnavailable("OpenAlex rate limit exhausted after retries")

    def doi_lookup_with_title_check(
        self, doi: str, expected_title: str,
    ) -> dict[str, Any] | None:
        """DOI lookup with mandatory Levenshtein 0.70 title cross-check."""
        quoted_doi = urllib.parse.quote(doi, safe="")
        data = self._get(f"/works/doi:{quoted_doi}", {"select": _FIELDS})
        title = data.get("title") or ""
        if _similarity(title, expected_title) >= _TITLE_SIMILARITY_THRESHOLD:
            return data
        return None  # DOI_MISMATCH

    def title_search(self, title: str, year: int | None = None) -> dict[str, Any] | None:
        """Title search under the #431 exact-title-or-bust gate.

        A candidate matches iff it clears the 0.70 ratio AND is an exact
        normalized title match (§0.12.1); a non-exact high-ratio title is never
        promoted on year/author alone. On the title-fallback path no ID can
        corroborate, so an exact-but-generic title (§0.12.2) is not promoted.
        Returns the best exact candidate, or None → resolver reduces the
        title-keyed miss to `unresolvable`. See crossref_client.title_search."""
        if generic_title(title):
            return None
        data = self._get("/works", {
            "search": title,
            "per-page": "5",
            "select": _FIELDS,
        })
        candidates = data.get("results", [])
        scored = []
        for cand in candidates:
            cand_title = cand.get("title") or ""
            sim = _similarity(cand_title, title)
            if sim < _TITLE_SIMILARITY_THRESHOLD:
                continue
            if not exact_normalized_title(title, cand_title):
                continue
            year_match = year is not None and cand.get("publication_year") == year
            score = sim + (0.05 if year_match else 0.0)
            scored.append((cand, score))
        if not scored:
            return None
        scored.sort(key=lambda cand_score: (-cand_score[1],))
        return scored[0][0]
