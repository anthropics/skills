#!/usr/bin/env python3
"""Tests for Crossref client per deep-research/references/crossref_api_protocol.md."""
from __future__ import annotations

import json
import urllib.error
from unittest.mock import MagicMock, patch

import pytest


def test_title_search_match_at_threshold(monkeypatch):
    """0.70 similarity threshold matches like S2/OpenAlex."""
    from crossref_client import CrossrefClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "message": {
            "items": [{
                "title": ["Attention Is All You Need"],
                "DOI": "10.5555/3295222.3295349",
            }]
        }
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        result = client.title_search("Attention Is All You Need")

    assert result is not None
    # Result should be the candidate dict from items list.
    assert result["title"] == ["Attention Is All You Need"]


def test_title_search_no_match_below_threshold(monkeypatch):
    """No match if best candidate similarity < 0.70."""
    from crossref_client import CrossrefClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "message": {
            "items": [{"title": ["Completely Unrelated Paper Title"]}]
        }
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        result = client.title_search("Attention Is All You Need")

    assert result is None


def test_doi_lookup_with_title_cross_check(monkeypatch):
    """DOI hit MUST pass Levenshtein 0.70 title cross-check (DOI_MISMATCH)."""
    from crossref_client import CrossrefClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "message": {
            "title": ["Some Other Paper"],
            "DOI": "10.5555/3295222.3295349",
        }
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        result = client.doi_lookup_with_title_check(
            doi="10.5555/3295222.3295349",
            expected_title="Attention Is All You Need",
        )

    assert result is None  # DOI_MISMATCH


def test_doi_lookup_with_matching_title(monkeypatch):
    """DOI hit + matching title -> success."""
    from crossref_client import CrossrefClient

    mock_response = MagicMock()
    mock_response.read.return_value = json.dumps({
        "message": {
            "title": ["Attention Is All You Need"],
            "DOI": "10.5555/3295222.3295349",
        }
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        result = client.doi_lookup_with_title_check(
            doi="10.5555/3295222.3295349",
            expected_title="Attention Is All You Need",
        )

    assert result is not None
    assert result["title"] == ["Attention Is All You Need"]


def test_429_triggers_2s_backoff_3_retries(monkeypatch):
    """Per protocol: 429 -> 2s backoff x 3 retries -> raise CrossrefUnavailable."""
    from crossref_client import CrossrefClient, CrossrefUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="https://api.crossref.org/works",
            code=429, msg="Too Many Requests", hdrs={}, fp=None,
        )

    sleeps = []
    monkeypatch.setattr("crossref_client.time.sleep", lambda s: sleeps.append(s))

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("anything")

    assert call_count[0] == 4
    assert sleeps == [2.0, 2.0, 2.0]


def test_5xx_skips_immediately(monkeypatch):
    """Per protocol: 5xx -> no retry, raise CrossrefUnavailable. Assert call_count == 1."""
    from crossref_client import CrossrefClient, CrossrefUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="https://api.crossref.org/works", code=503, msg="SU", hdrs={}, fp=None,
        )

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("anything")

    assert call_count[0] == 1


def test_doi_404_treated_as_miss_not_unavailable(monkeypatch):
    """DOI not indexed in Crossref (404) -> return None (miss), not raise CrossrefUnavailable."""
    from crossref_client import CrossrefClient, CrossrefUnavailable

    def mock_urlopen(*args, **kwargs):
        raise urllib.error.HTTPError(
            url="https://api.crossref.org/works/10.5555/nope",
            code=404, msg="Not Found", hdrs={}, fp=None,
        )

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = CrossrefClient()
        result = client.doi_lookup_with_title_check(
            doi="10.5555/nope",
            expected_title="Anything",
        )

    assert result is None


def test_title_search_prefers_matching_year(monkeypatch):
    """Two candidates same title - year-match wins via 0.05 score bonus."""
    from crossref_client import CrossrefClient

    mock_response = MagicMock()
    # Crossref year is nested: typically under `published-print` or `issued`.
    # Use `issued.date-parts[0][0]` for the year value (standard Crossref shape).
    mock_response.read.return_value = json.dumps({
        "message": {
            "items": [
                {
                    "title": ["Attention Is All You Need"],
                    "issued": {"date-parts": [[1999]]},
                },
                {
                    "title": ["Attention Is All You Need"],
                    "issued": {"date-parts": [[2017]]},
                },
            ]
        }
    }).encode("utf-8")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        result = client.title_search("Attention Is All You Need", year=2017)

    assert result is not None
    assert result["issued"]["date-parts"][0][0] == 2017


def test_polite_pool_email_in_user_agent(monkeypatch):
    """CROSSREF_POLITE_EMAIL adds 'mailto:...' to User-Agent header (NOT query param)."""
    from crossref_client import CrossrefClient

    captured_headers = []

    def mock_urlopen(req, *args, **kwargs):
        # urllib.request.Request stores headers; access via get_header (case-insensitive)
        ua = req.get_header("User-agent") or ""
        captured_headers.append(ua)
        mock_response = MagicMock()
        mock_response.read.return_value = json.dumps({"message": {"items": []}}).encode("utf-8")
        mock_response.__enter__ = MagicMock(return_value=mock_response)
        mock_response.__exit__ = MagicMock(return_value=None)
        return mock_response

    monkeypatch.setenv("CROSSREF_POLITE_EMAIL", "test@example.com")

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = CrossrefClient()
        client.title_search("any title")

    assert any("mailto:test@example.com" in ua for ua in captured_headers)


# ---------- v3.9.1: #129 response-read failure wrapping (Crossref) ----------


def test_oserror_during_read_raises_unavailable(monkeypatch):
    """urlopen succeeds, but resp.read() raises OSError (socket drop / timeout
    mid-stream). Per v3.9.0 spec §3.7 degradation contract, this MUST be
    translated to CrossrefUnavailable so migrate_literature_corpus_to_v3_9_0
    omits crossref_unmatched instead of aborting the whole backfill."""
    from crossref_client import CrossrefClient, CrossrefUnavailable

    mock_response = MagicMock()
    mock_response.read.side_effect = OSError("socket dropped mid-read")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("any title")


def test_invalid_utf8_body_raises_unavailable(monkeypatch):
    """resp.read() returns bytes that aren't valid UTF-8. Per v3.9.0 spec §3.7,
    translate to CrossrefUnavailable not bubble UnicodeDecodeError."""
    from crossref_client import CrossrefClient, CrossrefUnavailable

    mock_response = MagicMock()
    mock_response.read.return_value = b"\xff\xfe\xff garbage"
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("any title")


def test_invalid_json_body_raises_unavailable(monkeypatch):
    """resp.read() returns valid utf-8 but not valid JSON (truncated body /
    HTML error page). Per v3.9.0 spec §3.7, translate to CrossrefUnavailable
    not bubble JSONDecodeError."""
    from crossref_client import CrossrefClient, CrossrefUnavailable

    mock_response = MagicMock()
    mock_response.read.return_value = b"<html>503 backend unavailable</html>"
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("any title")


def test_truncated_read_raises_unavailable(monkeypatch):
    """http.client.IncompleteRead = mid-stream socket drop (200 + truncated
    body). Inherits HTTPException not OSError. v3.9.1 codex R1 P2 — symmetric
    to OpenAlex client."""
    import http.client

    from crossref_client import CrossrefClient, CrossrefUnavailable

    mock_response = MagicMock()
    mock_response.read.side_effect = http.client.IncompleteRead(
        partial=b'{"message":', expected=200
    )
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("any title")


def test_throttle_uses_monotonic_clock(monkeypatch):
    """time.monotonic for elapsed measurement (NTP-safe). time.time can
    go backward on NTP adjustments, breaking elapsed calculation.
    Aligns OA/CR with semantic_scholar_client.py (#128 §6)."""
    from crossref_client import CrossrefClient

    monotonic_calls = []
    time_calls = []

    def fake_monotonic():
        monotonic_calls.append(1)
        return 100.0

    def fake_time():
        time_calls.append(1)
        return 100.0

    monkeypatch.setattr("crossref_client.time.monotonic", fake_monotonic)
    monkeypatch.setattr("crossref_client.time.time", fake_time)

    client = CrossrefClient()
    # Initial state: no prior request — _throttle short-circuits.
    client._throttle()
    # Set anchor, then check throttle uses monotonic, not time.time.
    client._last_request_at = 90.0
    client._throttle()

    assert len(monotonic_calls) >= 1, "throttle must read time.monotonic"
    assert len(time_calls) == 0, "throttle must NOT read time.time (NTP-unsafe)"


def test_doi_lookup_quotes_doi_path_segment(monkeypatch):
    """DOI lookup must encode path separators/query markers before urlopen."""
    from crossref_client import CrossrefClient

    captured_urls = []

    def mock_urlopen(req, *args, **kwargs):
        captured_urls.append(req.full_url)
        mock_response = MagicMock()
        mock_response.read.return_value = json.dumps({
            "message": {
                "title": ["Attention Is All You Need"],
                "DOI": "10.1000/foo?bar=baz",
            }
        }).encode("utf-8")
        mock_response.__enter__ = MagicMock(return_value=mock_response)
        mock_response.__exit__ = MagicMock(return_value=None)
        return mock_response

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = CrossrefClient()
        result = client.doi_lookup_with_title_check(
            doi="10.1000/foo?bar=baz",
            expected_title="Attention Is All You Need",
        )

    assert result is not None
    assert captured_urls == [
        "https://api.crossref.org/works/10.1000%2Ffoo%3Fbar%3Dbaz"
    ]


def test_rejects_non_crossref_api_url_before_urlopen(monkeypatch):
    import crossref_client
    from crossref_client import CrossrefClient, CrossrefUnavailable

    monkeypatch.setattr(crossref_client, "_API_BASE", "http://evil.example")
    urlopen = MagicMock()
    with patch("urllib.request.urlopen", urlopen):
        client = CrossrefClient()
        with pytest.raises(CrossrefUnavailable):
            client.title_search("anything")

    assert urlopen.call_count == 0


def test_refusal_message_never_carries_mailto(monkeypatch):
    """The non-Crossref-URL refusal strips the query string so the polite-pool
    mailto (an email address) never lands in raised-exception text / logs
    (#495; mirrors openalex_client.py)."""
    import crossref_client
    from crossref_client import CrossrefClient, CrossrefUnavailable

    monkeypatch.setattr(crossref_client, "_API_BASE", "http://evil.example")
    with patch("urllib.request.urlopen", MagicMock()):
        client = CrossrefClient(polite_email="secret@example.com")
        with pytest.raises(CrossrefUnavailable) as excinfo:
            client.title_search("anything")

    assert "secret@example.com" not in str(excinfo.value)
