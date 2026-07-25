#!/usr/bin/env python3
"""Tests for arXiv client per deep-research/references/arxiv_api_protocol.md.

Mirrors test_crossref_client.py. arXiv API differs from Crossref in three
ways the tests exercise: (1) the response is Atom XML, not JSON; (2) the
exact-key lookup is by arXiv ID (`arxiv_id_lookup`), not DOI; (3) there is
no polite-pool email — pacing is a fixed min-interval.

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 1.
"""
from __future__ import annotations

import http.client
import urllib.error
from unittest.mock import MagicMock, patch

import pytest


def _atom(entries: list[str]) -> bytes:
    """Build an Atom feed body with the given <entry> blocks (raw XML strings)."""
    body = (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<feed xmlns="http://www.w3.org/2005/Atom">\n'
        + "\n".join(entries)
        + "\n</feed>"
    )
    return body.encode("utf-8")


def _entry(title: str, arxiv_url: str = "http://arxiv.org/abs/1706.03762v5",
           published: str = "2017-06-12T00:00:00Z") -> str:
    return (
        "<entry>"
        f"<id>{arxiv_url}</id>"
        f"<title>{title}</title>"
        f"<published>{published}</published>"
        "</entry>"
    )


def _mock_resp(body: bytes) -> MagicMock:
    mock_response = MagicMock()
    mock_response.read.return_value = body
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)
    return mock_response


def test_title_search_match_at_threshold():
    """0.70 similarity threshold matches like the other clients."""
    from arxiv_client import ArxivClient

    body = _atom([_entry("Attention Is All You Need")])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.title_search("Attention Is All You Need")

    assert result is not None
    assert result["title"] == "Attention Is All You Need"


def test_title_search_no_match_below_threshold():
    """No match if best candidate similarity < 0.70."""
    from arxiv_client import ArxivClient

    body = _atom([_entry("Completely Unrelated Paper Title")])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.title_search("Attention Is All You Need")

    assert result is None


def test_title_search_empty_feed_returns_none():
    """Zero <entry> elements (arXiv's empty-result shape) -> None."""
    from arxiv_client import ArxivClient

    body = _atom([])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.title_search("Attention Is All You Need")

    assert result is None


def test_arxiv_id_lookup_with_title_cross_check():
    """ID hit MUST pass 0.70 title cross-check (ID_MISMATCH -> None)."""
    from arxiv_client import ArxivClient

    body = _atom([_entry("Some Other Paper")])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.arxiv_id_lookup(
            arxiv_id="1706.03762",
            expected_title="Attention Is All You Need",
        )

    assert result is None  # ID_MISMATCH


def test_arxiv_id_lookup_with_matching_title():
    """ID hit + matching title -> success (returns the entry dict)."""
    from arxiv_client import ArxivClient

    body = _atom([_entry("Attention Is All You Need")])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.arxiv_id_lookup(
            arxiv_id="1706.03762",
            expected_title="Attention Is All You Need",
        )

    assert result is not None
    assert result["title"] == "Attention Is All You Need"


def test_arxiv_id_lookup_empty_feed_is_miss():
    """A non-existent arXiv ID returns an empty feed (no <entry>) -> None (miss)."""
    from arxiv_client import ArxivClient

    body = _atom([])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.arxiv_id_lookup(
            arxiv_id="9999.99999",
            expected_title="Anything",
        )

    assert result is None


def test_arxiv_id_with_version_suffix_resolves():
    """arXiv natively supports versioned IDs (1706.03762v5) in id_list — the
    client passes the id through verbatim and a matching feed resolves."""
    from arxiv_client import ArxivClient

    body = _atom([_entry("Attention Is All You Need")])
    captured = {}

    def mock_urlopen(req, *a, **k):
        captured["url"] = req.full_url
        return _mock_resp(body)

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = ArxivClient()
        result = client.arxiv_id_lookup(
            arxiv_id="1706.03762v5",
            expected_title="Attention Is All You Need",
        )

    assert result is not None
    assert "1706.03762v5" in captured["url"]  # passed through verbatim


def test_arxiv_id_as_full_url_falls_through_to_title():
    """If arxiv_id is a full URL (not a bare ID), id_list lookup won't match
    and the client falls through to title search. Documents current behavior:
    the client does NOT strip URLs — adapters are expected to emit bare IDs.
    The fall-through still finds the paper via title, so it is not a hard miss."""
    from arxiv_client import ArxivClient

    # id_list lookup of a URL -> arXiv returns empty feed; title search hits.
    id_feed = _atom([])
    title_feed = _atom([_entry("Attention Is All You Need")])
    responses = [_mock_resp(id_feed), _mock_resp(title_feed)]

    def mock_urlopen(*a, **k):
        return responses.pop(0)

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = ArxivClient()
        id_hit = client.arxiv_id_lookup(
            arxiv_id="https://arxiv.org/abs/1706.03762",
            expected_title="Attention Is All You Need",
        )
        assert id_hit is None  # URL did not resolve as an exact id_list key
        # The resolver wrapper would then fall through to title_search:
        title_hit = client.title_search("Attention Is All You Need")
        assert title_hit is not None


def test_title_search_empty_title_is_miss_not_crash():
    """An empty title produces a ti:"" query; the client must not crash and
    returns None (no candidate meets the 0.70 threshold against "")."""
    from arxiv_client import ArxivClient

    body = _atom([])  # arXiv returns no entries for an empty title query
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.title_search("")

    assert result is None


def test_title_search_prefers_matching_year():
    """Two same-title candidates - matching publication year wins via 0.05 bonus."""
    from arxiv_client import ArxivClient

    body = _atom([
        _entry("Attention Is All You Need", published="1999-01-01T00:00:00Z"),
        _entry("Attention Is All You Need", published="2017-06-12T00:00:00Z"),
    ])
    with patch("urllib.request.urlopen", return_value=_mock_resp(body)):
        client = ArxivClient()
        result = client.title_search("Attention Is All You Need", year=2017)

    assert result is not None
    assert result["year"] == 2017


def test_429_backs_off_at_tou_pacing_floor(monkeypatch):
    """Per protocol (#495): 429 -> 3s backoff x 3 retries -> raise
    ArxivUnavailable. The backoff is the ToU pacing floor (>= 3s between
    requests) — a sub-3s retry would itself violate arXiv's rate terms."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="http://export.arxiv.org/api/query",
            code=429, msg="Too Many Requests", hdrs={}, fp=None,
        )

    sleeps = []
    monkeypatch.setattr("arxiv_client.time.sleep", lambda s: sleeps.append(s))

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("anything")

    assert call_count[0] == 4
    assert sleeps == [3.0, 3.0, 3.0]


def test_5xx_skips_immediately():
    """Per protocol: 5xx -> no retry, raise ArxivUnavailable. call_count == 1."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    call_count = [0]

    def mock_urlopen(*args, **kwargs):
        call_count[0] += 1
        raise urllib.error.HTTPError(
            url="http://export.arxiv.org/api/query", code=503, msg="SU",
            hdrs={}, fp=None,
        )

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("anything")

    assert call_count[0] == 1


def test_network_error_raises_unavailable():
    """URLError / TimeoutError -> ArxivUnavailable (degradation contract)."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    def mock_urlopen(*args, **kwargs):
        raise urllib.error.URLError("connection refused")

    with patch("urllib.request.urlopen", side_effect=mock_urlopen):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("anything")


def test_malformed_xml_body_raises_unavailable():
    """resp.read() returns bytes that aren't well-formed XML (truncated body
    mid-stream: an unclosed tag). Per the §3.7 degradation contract, translate
    the ParseError to ArxivUnavailable. Mirrors crossref's
    test_invalid_json_body_raises_unavailable.

    Distinct from the non-Atom-200 case (#331): a *complete* HTML error page
    parses without ParseError but has a non-feed root tag, so it is rejected by
    the explicit root-tag check (test_non_atom_200_body_raises_unavailable), not
    here. This test covers genuinely malformed bytes (truncated/unclosed),
    which is what an interrupted transfer actually produces."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    with patch("urllib.request.urlopen", return_value=_mock_resp(
            b'<feed xmlns="http://www.w3.org/2005/Atom"><entry><title>trunc')):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("any title")


def test_non_atom_200_body_raises_unavailable():
    """#331: a complete, well-formed non-Atom body served with 200 (e.g. an HTML
    error page from a proxy/CDN) must NOT be treated as a real empty-result miss.
    arXiv's genuine empty result is an Atom <feed> with zero <entry> children;
    an HTML error page has a non-feed root tag. The non-feed root must raise
    ArxivUnavailable (omit-on-degradation) so it is never cached as a false
    arxiv_unmatched=true for the 90-day TTL."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    html_error_page = b"<html><body><h1>503 Service Unavailable</h1></body></html>"
    with patch("urllib.request.urlopen", return_value=_mock_resp(html_error_page)):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("any title")


def test_genuine_empty_atom_feed_is_miss_not_unavailable():
    """#331 guard against over-correction: a genuine empty Atom <feed> (zero
    <entry>, the real arXiv miss shape) must still resolve to a miss (None), NOT
    raise. The root-tag check accepts the feed root and findall returns []."""
    from arxiv_client import ArxivClient

    empty_feed = b'<feed xmlns="http://www.w3.org/2005/Atom"><title>arXiv Query</title></feed>'
    with patch("urllib.request.urlopen", return_value=_mock_resp(empty_feed)):
        client = ArxivClient()
        assert client.title_search("nonexistent paper") is None


def test_oserror_during_read_raises_unavailable():
    """urlopen succeeds, resp.read() raises OSError (socket drop mid-stream).
    Translate to ArxivUnavailable. Mirrors crossref."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    mock_response = MagicMock()
    mock_response.read.side_effect = OSError("socket dropped mid-read")
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("any title")


def test_truncated_read_raises_unavailable():
    """http.client.IncompleteRead = mid-stream socket drop (200 + truncated
    body). Inherits HTTPException not OSError. Mirrors the crossref client."""
    from arxiv_client import ArxivClient, ArxivUnavailable

    mock_response = MagicMock()
    mock_response.read.side_effect = http.client.IncompleteRead(
        partial=b"<feed>", expected=200
    )
    mock_response.__enter__ = MagicMock(return_value=mock_response)
    mock_response.__exit__ = MagicMock(return_value=None)

    with patch("urllib.request.urlopen", return_value=mock_response):
        client = ArxivClient()
        with pytest.raises(ArxivUnavailable):
            client.title_search("any title")


def test_throttle_uses_monotonic_clock(monkeypatch):
    """time.monotonic for elapsed measurement (NTP-safe), not time.time.
    Aligns with crossref/openalex/S2 (#128 §6)."""
    from arxiv_client import ArxivClient

    monotonic_calls = []
    time_calls = []

    monkeypatch.setattr("arxiv_client.time.monotonic",
                        lambda: (monotonic_calls.append(1), 100.0)[1])
    monkeypatch.setattr("arxiv_client.time.time",
                        lambda: (time_calls.append(1), 100.0)[1])

    client = ArxivClient()
    client._throttle()  # no prior request -> short-circuit
    client._last_request_at = 90.0
    client._throttle()

    assert len(monotonic_calls) >= 1, "throttle must read time.monotonic"
    assert len(time_calls) == 0, "throttle must NOT read time.time (NTP-unsafe)"
