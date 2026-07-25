#!/usr/bin/env python3
"""Tests for OpenAlex client per deep-research/references/openalex_api_protocol.md."""
from __future__ import annotations

import json
import urllib.error
from unittest.mock import MagicMock, patch

import pytest


def test_title_search_match_at_threshold(monkeypatch):
    """0.70 similarity threshold matches like S2 (PaperOrchestra precedent)."""
    from openalex_client import OpenAlexClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "results": [{
            "title": "Attention Is All You Need",
            "publication_year": 2017,
            "doi": "https://doi.org/10.5555/3295222.3295349",
        }]
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        result = client.title_search("Attention Is All You Need")

    assert result is not None
    assert result["title"] == "Attention Is All You Need"


def test_title_search_no_match_below_threshold(monkeypatch):
    """No match returned if best candidate similarity < 0.70."""
    from openalex_client import OpenAlexClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "results": [{
            "title": "Completely Unrelated Paper Title",
            "publication_year": 2017,
        }]
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        result = client.title_search("Attention Is All You Need")

    assert result is None


def test_doi_lookup_with_title_cross_check(monkeypatch):
    """DOI hit MUST pass Levenshtein 0.70 title cross-check (DOI_MISMATCH pattern)."""
    from openalex_client import OpenAlexClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "title": "Some Other Paper",
        "doi": "https://doi.org/10.5555/3295222.3295349",
        "publication_year": 2020,
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        result = client.doi_lookup_with_title_check(
            doi="10.5555/3295222.3295349",
            expected_title="Attention Is All You Need",
        )

    assert result is None  # DOI_MISMATCH


def test_doi_lookup_with_matching_title(monkeypatch):
    """DOI hit + matching title → success."""
    from openalex_client import OpenAlexClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "title": "Attention Is All You Need",
        "doi": "https://doi.org/10.5555/3295222.3295349",
        "publication_year": 2017,
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        result = client.doi_lookup_with_title_check(
            doi="10.5555/3295222.3295349",
            expected_title="Attention Is All You Need",
        )

    assert result is not None
    assert result["title"] == "Attention Is All You Need"


def test_429_transient_backs_off_exponentially(monkeypatch):
    """Per protocol (#495): transient 429 (no budget header) → exponential
    backoff 2s → 4s → 8s over 3 retries → raise OpenAlexUnavailable."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="https://api.openalex.org/works",
            code=429,
            msg="Too Many Requests",
            hdrs={},
            fp=None,
        )

    sleeps = []
    monkeypatch.setattr("openalex_client.time.sleep", lambda s: sleeps.append(s))

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("anything")

    assert call_count[0] == 4  # initial + 3 retries
    assert sleeps == [2.0, 4.0, 8.0]


def test_429_daily_budget_exhausted_fails_fast(monkeypatch):
    """Per protocol (#495): 429 with X-RateLimit-Remaining: 0 is daily-budget
    exhaustion (refills midnight UTC) — an in-process retry cannot succeed, so
    raise OpenAlexUnavailable immediately: no sleep, no retry."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="https://api.openalex.org/works",
            code=429,
            msg="Too Many Requests",
            hdrs={"X-RateLimit-Remaining": "0"},
            fp=None,
        )

    sleeps = []
    monkeypatch.setattr("openalex_client.time.sleep", lambda s: sleeps.append(s))

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable, match="daily budget exhausted"):
            client.title_search("anything")

    assert call_count[0] == 1  # fail-fast: no retry
    assert sleeps == []


def test_429_with_remaining_budget_stays_on_retry_path(monkeypatch):
    """A 429 whose X-RateLimit-Remaining is nonzero is burst limiting, not
    budget exhaustion — it must keep the retry behavior."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="https://api.openalex.org/works",
            code=429,
            msg="Too Many Requests",
            hdrs={"X-RateLimit-Remaining": "42"},
            fp=None,
        )

    monkeypatch.setattr("openalex_client.time.sleep", lambda s: None)

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("anything")

    assert call_count[0] == 4  # initial + 3 retries


def test_5xx_skips_immediately(monkeypatch):
    """Per protocol: 5xx → no retry (call count == 1), raise OpenAlexUnavailable."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="https://api.openalex.org/works",
            code=503,
            msg="Service Unavailable",
            hdrs={},
            fp=None,
        )

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("anything")

    assert call_count[0] == 1  # no retry on 5xx


def test_polite_pool_email_param(monkeypatch):
    """OPENALEX_POLITE_EMAIL env var adds mailto= query param."""
    from openalex_client import OpenAlexClient

    captured_url = []

    def mock_urlopen(req, *args, **kwargs):
        captured_url.append(req.full_url if hasattr(req, "full_url") else req)
        mock_response = MagicMock()
        mock_response.read.return_value = json.dumps({"results": []}).encode("utf-8")
        mock_response.__enter__ = MagicMock(return_value=mock_response)
        mock_response.__exit__ = MagicMock(return_value=None)
        return mock_response

    monkeypatch.setenv("OPENALEX_POLITE_EMAIL", "test@example.com")

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        client.title_search("any title")

    assert any("mailto=test%40example.com" in url for url in captured_url)


# ---------- #495: OPENALEX_API_KEY auth ----------


def test_api_key_env_adds_api_key_param(monkeypatch):
    """OPENALEX_API_KEY env var adds api_key= query param (#495)."""
    from openalex_client import OpenAlexClient

    captured_url = []

    def mock_urlopen(req, *args, **kwargs):
        captured_url.append(req.full_url if hasattr(req, "full_url") else req)
        mock_response = MagicMock()
        mock_response.read.return_value = json.dumps({"results": []}).encode("utf-8")
        mock_response.__enter__ = MagicMock(return_value=mock_response)
        mock_response.__exit__ = MagicMock(return_value=None)
        return mock_response

    monkeypatch.setenv("OPENALEX_API_KEY", "test-key-123")

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        client.title_search("any title")

    assert any("api_key=test-key-123" in url for url in captured_url)


def test_api_key_selects_authenticated_interval(monkeypatch):
    """api_key (like polite_email) selects the 0.1s authenticated pacing
    tier; with neither credential the anonymous 1.0s tier applies (#495)."""
    from openalex_client import OpenAlexClient

    monkeypatch.delenv("OPENALEX_API_KEY", raising=False)
    monkeypatch.delenv("OPENALEX_POLITE_EMAIL", raising=False)

    assert OpenAlexClient()._min_interval == 1.0
    assert OpenAlexClient(api_key="k")._min_interval == 0.1
    assert OpenAlexClient(polite_email="a@b.c")._min_interval == 0.1


def test_refusal_message_never_carries_api_key(monkeypatch):
    """The non-OpenAlex-URL refusal strips the query string so api_key
    never lands in raised-exception text / logs (#495)."""
    import openalex_client
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    monkeypatch.setattr(openalex_client, "_API_BASE", "http://evil.example")
    with patch("urllib.request.urlopen", MagicMock()):
        client = OpenAlexClient(api_key="sk-secret-key")
        with pytest.raises(OpenAlexUnavailable) as excinfo:
            client.title_search("anything")

    assert "sk-secret-key" not in str(excinfo.value)


def test_doi_404_treated_as_miss_not_unavailable(monkeypatch):
    """DOI not indexed in OpenAlex (404) → return None (miss), not raise OpenAlexUnavailable."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    def mock_urlopen(*args, **kwargs):
        raise urllib.error.HTTPError(
            url="https://api.openalex.org/works/doi:10.5555/nonexistent",
            code=404,
            msg="Not Found",
            hdrs={},
            fp=None,
        )

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        result = client.doi_lookup_with_title_check(
            doi="10.5555/nonexistent",
            expected_title="Anything",
        )

    assert result is None  # 404 = miss, falls through to title search at caller level


def test_title_search_prefers_matching_year(monkeypatch):
    """When two candidates have similar titles, prefer the one with matching year."""
    from openalex_client import OpenAlexClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "results": [
            {"title": "Attention Is All You Need", "publication_year": 1999},  # wrong year
            {"title": "Attention Is All You Need", "publication_year": 2017},  # matching year
        ]
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        result = client.title_search("Attention Is All You Need", year=2017)

    assert result is not None
    assert result["publication_year"] == 2017


# ---------- v3.9.1: #129 response-read failure wrapping ----------


def test_oserror_during_read_raises_unavailable(monkeypatch):
    """urlopen succeeds, but resp.read() raises OSError (socket drop / timeout
    mid-stream). Per v3.9.0 spec §3.7 degradation contract, this MUST be
    translated to OpenAlexUnavailable so migrate_literature_corpus_to_v3_9_0
    omits openalex_unmatched instead of aborting the whole backfill."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    mock_response = MagicMock()
    mock_response.read.side_effect = OSError("socket dropped mid-read")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("any title")


def test_invalid_utf8_body_raises_unavailable(monkeypatch):
    """resp.read() returns bytes that aren't valid UTF-8 (garbled CDN response).
    Per v3.9.0 spec §3.7, translate to OpenAlexUnavailable not bubble out as
    UnicodeDecodeError."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    mock_response = MagicMock()
    mock_response.read.return_value = b"\xff\xfe\xff garbage"
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("any title")


def test_invalid_json_body_raises_unavailable(monkeypatch):
    """resp.read() returns valid utf-8 but not valid JSON (e.g. truncated body,
    HTML error page slipped through). Per v3.9.0 spec §3.7, translate to
    OpenAlexUnavailable not bubble JSONDecodeError."""
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    mock_response = MagicMock()
    mock_response.read.return_value = b"<html>503 backend unavailable</html>"
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("any title")


def test_truncated_read_raises_unavailable(monkeypatch):
    """http.client.IncompleteRead is the canonical mid-stream socket-drop
    exception (200 status with truncated body). Inherits HTTPException, NOT
    OSError — so an OSError-only handler still lets it escape. v3.9.1 codex
    R1 P2: catch this explicitly to honor the v3.9.0 §3.7 per-API
    degradation contract."""
    import http.client

    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    mock_response = MagicMock()
    mock_response.read.side_effect = http.client.IncompleteRead(
        partial=b'{"results":', expected=200
    )
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("any title")


def test_throttle_uses_monotonic_clock(monkeypatch):
    """time.monotonic for elapsed measurement (NTP-safe). time.time can
    go backward on NTP adjustments, breaking elapsed calculation.
    Aligns OA/CR with semantic_scholar_client.py (#128 §6)."""
    from openalex_client import OpenAlexClient

    monotonic_calls = []
    time_calls = []

    def fake_monotonic():
        monotonic_calls.append(1)
        return 100.0

    def fake_time():
        time_calls.append(1)
        return 100.0

    monkeypatch.setattr("openalex_client.time.monotonic", fake_monotonic)
    monkeypatch.setattr("openalex_client.time.time", fake_time)

    client = OpenAlexClient()
    # Initial state: no prior request — _throttle short-circuits.
    client._throttle()
    # Set anchor, then check throttle uses monotonic, not time.time.
    client._last_request_at = 90.0
    client._throttle()

    assert len(monotonic_calls) >= 1, "throttle must read time.monotonic"
    assert len(time_calls) == 0, "throttle must NOT read time.time (NTP-unsafe)"


def test_doi_lookup_quotes_doi_path_segment(monkeypatch):
    """DOI lookup must encode path separators/query markers before urlopen."""
    from openalex_client import OpenAlexClient

    # Exact-URL assertion below — a developer-machine OPENALEX_API_KEY /
    # OPENALEX_POLITE_EMAIL would append extra params and break it.
    monkeypatch.delenv("OPENALEX_API_KEY", raising=False)
    monkeypatch.delenv("OPENALEX_POLITE_EMAIL", raising=False)

    captured_urls = []

    def mock_urlopen(req, *args, **kwargs):
        captured_urls.append(req.full_url)
        mock_response = MagicMock()
        mock_response.read.return_value = json.dumps({
            "title": "Attention Is All You Need",
            "doi": "https://doi.org/10.1000/foo?bar=baz",
        }).encode("utf-8")
        mock_response.__enter__ = MagicMock(return_value=mock_response)
        mock_response.__exit__ = MagicMock(return_value=None)
        return mock_response

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = OpenAlexClient()
        result = client.doi_lookup_with_title_check(
            doi="10.1000/foo?bar=baz",
            expected_title="Attention Is All You Need",
        )

    assert result is not None
    assert captured_urls == [
        "https://api.openalex.org/works/doi:10.1000%2Ffoo%3Fbar%3Dbaz?select=id%2Ctitle%2Cauthorships%2Cpublication_year%2Cdoi%2Cprimary_location"
    ]


def test_rejects_non_openalex_api_url_before_urlopen(monkeypatch):
    import openalex_client
    from openalex_client import OpenAlexClient, OpenAlexUnavailable

    monkeypatch.setattr(openalex_client, "_API_BASE", "http://evil.example")
    urlopen = MagicMock()
    with patch("urllib.request.urlopen", urlopen):
        client = OpenAlexClient()
        with pytest.raises(OpenAlexUnavailable):
            client.title_search("anything")

    assert urlopen.call_count == 0
