#!/usr/bin/env python3
"""Tests for the minimal Semantic Scholar client backing #105 CLI.

Mocks urllib at the transport layer (no real network). Verifies the
client honors the protocol's DOI-first + title-similarity + 429-backoff
contract and surfaces SemanticScholarUnavailable on the documented
failure modes.
"""
from __future__ import annotations

import io
import json
import sys
import unittest
import urllib.error
from pathlib import Path
from unittest.mock import patch, MagicMock

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import semantic_scholar_client as ssc  # noqa: E402
from contamination_signals import SemanticScholarUnavailable  # noqa: E402


def _mock_response(payload: dict) -> MagicMock:
    """Build a urlopen-style response context manager returning `payload`."""
    body = json.dumps(payload).encode("utf-8")
    resp = MagicMock()
    resp.read.return_value = body
    resp.__enter__ = MagicMock(return_value=resp)
    resp.__exit__ = MagicMock(return_value=False)
    return resp


def _mock_urlopen_returning(payload: dict) -> MagicMock:
    """Build a urlopen mock that returns `payload` JSON as the response body."""
    return MagicMock(return_value=_mock_response(payload))


class DoiLookupTest(unittest.TestCase):
    def test_doi_match_with_matching_title(self) -> None:
        client = ssc.SemanticScholarClient()
        payload = {"paperId": "abc123", "title": "AI in education"}
        with patch(
            "urllib.request.urlopen", _mock_urlopen_returning(payload)
        ):
            result = client.lookup(
                {"title": "AI in education", "doi": "10.1234/xyz", "year": 2024}
            )
        self.assertEqual(result, {"matched": True, "paperId": "abc123"})

    def test_doi_lookup_quotes_doi_path_segment(self) -> None:
        client = ssc.SemanticScholarClient()
        captured_urls = []

        def mock_urlopen(req, *args, **kwargs):
            captured_urls.append(req.full_url)
            return _mock_response({
                "paperId": "abc123",
                "title": "AI in education",
            })

        with patch("urllib.request.urlopen", mock_urlopen):
            result = client.lookup({
                "title": "AI in education",
                "doi": "10.1000/foo?bar=baz",
                "year": 2024,
            })

        self.assertEqual(result, {"matched": True, "paperId": "abc123"})
        self.assertEqual(captured_urls, [
            "https://api.semanticscholar.org/graph/v1/paper/DOI:10.1000%2Ffoo%3Fbar%3Dbaz?fields=title,authors,year,externalIds,venue,publicationDate"
        ])

    def test_rejects_non_s2_api_url_before_urlopen(self) -> None:
        client = ssc.SemanticScholarClient()
        urlopen = MagicMock()
        with patch.object(ssc, "_API_BASE", "http://evil.example"):
            with patch("urllib.request.urlopen", urlopen):
                with self.assertRaises(SemanticScholarUnavailable):
                    client.lookup({"title": "T", "doi": "10.1/y"})

        self.assertEqual(urlopen.call_count, 0)

    def test_rejects_wrong_s2_host_before_urlopen(self) -> None:
        client = ssc.SemanticScholarClient()
        urlopen = MagicMock()
        with patch.object(ssc, "_API_BASE", "https://evil.example"):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "T", "doi": "10.1/y"})

        self.assertEqual(urlopen.call_count, 0)

    def test_doi_404_falls_back_to_title_search(self) -> None:
        """Codex R2-2 closure: v3.7.3 Vector 2 says unmatched=true only
        when NEITHER DOI nor title yields a hit. DOI 404 alone is not
        sufficient — must fall through to title search."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        # DOI lookup 404s; title search finds match
        title_payload = {
            "data": [
                {"paperId": "title-hit", "title": "AI in education", "year": 2024}
            ]
        }
        title_body = json.dumps(title_payload).encode("utf-8")
        title_resp = MagicMock()
        title_resp.read.return_value = title_body
        title_resp.__enter__ = MagicMock(return_value=title_resp)
        title_resp.__exit__ = MagicMock(return_value=False)
        urlopen = MagicMock(side_effect=[
            urllib.error.HTTPError("u", 404, "Not Found", {}, io.BytesIO(b"")),
            title_resp,
        ])
        with patch("urllib.request.urlopen", urlopen):
            result = client.lookup(
                {"title": "AI in education", "doi": "10.9999/bogus", "year": 2024}
            )
        self.assertEqual(result, {"matched": True, "paperId": "title-hit"})

    def test_doi_title_mismatch_falls_back_to_title_search(self) -> None:
        """Codex R2-2 closure: DOI returns wrong paper (title mismatch).
        Still must try title search before declaring unmatched."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        doi_payload = {"paperId": "wrong-paper", "title": "Totally unrelated"}
        title_payload = {
            "data": [
                {"paperId": "title-hit", "title": "AI in education", "year": 2024}
            ]
        }
        doi_body = json.dumps(doi_payload).encode("utf-8")
        title_body = json.dumps(title_payload).encode("utf-8")
        doi_resp = MagicMock()
        doi_resp.read.return_value = doi_body
        doi_resp.__enter__ = MagicMock(return_value=doi_resp)
        doi_resp.__exit__ = MagicMock(return_value=False)
        title_resp = MagicMock()
        title_resp.read.return_value = title_body
        title_resp.__enter__ = MagicMock(return_value=title_resp)
        title_resp.__exit__ = MagicMock(return_value=False)
        urlopen = MagicMock(side_effect=[doi_resp, title_resp])
        with patch("urllib.request.urlopen", urlopen):
            result = client.lookup(
                {"title": "AI in education", "doi": "10.1234/xyz", "year": 2024}
            )
        self.assertEqual(result, {"matched": True, "paperId": "title-hit"})

    def test_doi_404_and_title_404_returns_no_match(self) -> None:
        """Both endpoints miss: now legitimate unmatched."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        urlopen = MagicMock(side_effect=[
            urllib.error.HTTPError("u", 404, "Not Found", {}, io.BytesIO(b"")),
            urllib.error.HTTPError("u", 404, "Not Found", {}, io.BytesIO(b"")),
        ])
        with patch("urllib.request.urlopen", urlopen):
            result = client.lookup(
                {"title": "Truly nonexistent", "doi": "10.0000/bogus", "year": 2024}
            )
        self.assertEqual(result, {"matched": False, "paperId": None})


class TitleSearchTest(unittest.TestCase):
    def test_title_search_above_threshold_matches(self) -> None:
        client = ssc.SemanticScholarClient()
        payload = {
            "data": [
                {"paperId": "abc123", "title": "AI in education", "year": 2024}
            ]
        }
        with patch(
            "urllib.request.urlopen", _mock_urlopen_returning(payload)
        ):
            result = client.lookup({"title": "AI in education", "year": 2024})
        self.assertEqual(result, {"matched": True, "paperId": "abc123"})

    def test_title_search_below_threshold_no_match(self) -> None:
        client = ssc.SemanticScholarClient()
        payload = {
            "data": [
                {"paperId": "xyz", "title": "Totally different", "year": 2024}
            ]
        }
        with patch(
            "urllib.request.urlopen", _mock_urlopen_returning(payload)
        ):
            result = client.lookup({"title": "AI in education", "year": 2024})
        self.assertEqual(result, {"matched": False, "paperId": None})

    def test_empty_results_no_match(self) -> None:
        client = ssc.SemanticScholarClient()
        with patch(
            "urllib.request.urlopen", _mock_urlopen_returning({"data": []})
        ):
            result = client.lookup({"title": "Unknown paper"})
        self.assertEqual(result, {"matched": False, "paperId": None})


class FailureHandlingTest(unittest.TestCase):
    def _raise_http(self, code: int):
        return urllib.error.HTTPError("u", code, "msg", {}, io.BytesIO(b""))

    def test_429_backoff_then_recover(self) -> None:
        """Per protocol: HTTP 429 → 2s backoff × 3 retries before
        giving up. The retry is transparent — successful retry returns
        a normal result without raising."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        payload = {"paperId": "abc", "title": "AI in education"}
        body = json.dumps(payload).encode("utf-8")
        resp = MagicMock()
        resp.read.return_value = body
        resp.__enter__ = MagicMock(return_value=resp)
        resp.__exit__ = MagicMock(return_value=False)

        # First two calls 429, third succeeds
        urlopen = MagicMock(side_effect=[
            self._raise_http(429),
            self._raise_http(429),
            resp,
        ])
        with patch("urllib.request.urlopen", urlopen):
            result = client.lookup(
                {"title": "AI in education", "doi": "10.1234/xyz"}
            )
        self.assertEqual(result, {"matched": True, "paperId": "abc"})

    def test_429_after_max_retries_raises_unavailable(self) -> None:
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        # All 4 attempts (initial + 3 retries) raise 429
        urlopen = MagicMock(side_effect=[self._raise_http(429)] * 4)
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "X", "doi": "10.1/y"})

    def test_5xx_raises_unavailable(self) -> None:
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        urlopen = MagicMock(side_effect=self._raise_http(503))
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "X", "doi": "10.1/y"})

    def test_404_means_no_match_not_unavailable(self) -> None:
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        urlopen = MagicMock(side_effect=self._raise_http(404))
        with patch("urllib.request.urlopen", urlopen):
            result = client.lookup({"title": "X", "doi": "10.1/y"})
        self.assertEqual(result, {"matched": False, "paperId": None})

    def test_network_error_raises_unavailable(self) -> None:
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        urlopen = MagicMock(side_effect=urllib.error.URLError("connection refused"))
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "X", "doi": "10.1/y"})


class TitleNormalizationTest(unittest.TestCase):
    """Codex R4-1 closure: protocol §"Query Patterns" Pattern 1 says
    title matching is 'case-insensitive, stripped of punctuation'."""

    def test_acronym_punctuation_clears_threshold(self) -> None:
        """'R.A.G.' vs 'RAG' originally scored below 0.70 because raw
        SequenceMatcher penalized the punctuation. After normalize the
        score clears the 0.70 protocol threshold."""
        self.assertGreaterEqual(ssc._similarity("R.A.G.", "RAG"), 0.70)

    def test_punctuation_stripped_before_similarity(self) -> None:
        """Trailing colons / em-dashes / quotes should not penalize match."""
        self.assertGreater(
            ssc._similarity(
                "Attention Is All You Need: A Transformers Story",
                "attention is all you need a transformers story",
            ),
            0.95,
        )

    def test_title_normalize_collapses_whitespace(self) -> None:
        """Multiple punctuation chars become spaces; collapse them."""
        self.assertEqual(ssc._normalize_title("Foo,  Bar... Baz!"), "foo bar baz")


class ResponseReadTimeoutTest(unittest.TestCase):
    """Codex R4-2 closure: resp.read() can raise OSError/TimeoutError
    (e.g. socket.timeout on the body read) outside the URLError handler.
    Must be wrapped as SemanticScholarUnavailable so the migration
    degrades gracefully rather than aborting mid-run."""

    def test_response_read_oserror_raises_unavailable(self) -> None:
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        resp = MagicMock()
        resp.read.side_effect = OSError("socket read timeout")
        resp.__enter__ = MagicMock(return_value=resp)
        resp.__exit__ = MagicMock(return_value=False)
        with patch("urllib.request.urlopen", MagicMock(return_value=resp)):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "X", "doi": "10.1/y"})

    def test_response_read_timeout_error_raises_unavailable(self) -> None:
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        resp = MagicMock()
        resp.read.side_effect = TimeoutError("body read timed out")
        resp.__enter__ = MagicMock(return_value=resp)
        resp.__exit__ = MagicMock(return_value=False)
        with patch("urllib.request.urlopen", MagicMock(return_value=resp)):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "X", "doi": "10.1/y"})


class RateLimitThrottleTest(unittest.TestCase):
    """#115 R5-2: back-to-back successful lookups must respect the
    protocol's 1 req/s unauthenticated rate limit so the client doesn't
    proactively hit 429 and exhaust retries on healthy corpora."""

    def _good_resp(self, payload: dict) -> MagicMock:
        return _mock_response(payload)

    def test_first_request_does_not_sleep(self) -> None:
        """First request after construction has no prior call to pace
        against; the throttle should pass through immediately. Hermetic
        regardless of S2_API_KEY env (no comparison against tier)."""
        sleep = MagicMock()
        clock = MagicMock(return_value=1000.0)
        client = ssc.SemanticScholarClient(
            sleep=sleep, clock=clock, min_interval_seconds=1.0
        )
        with patch(
            "urllib.request.urlopen",
            MagicMock(return_value=self._good_resp({"paperId": "x", "title": "T"})),
        ):
            client.lookup({"title": "T", "doi": "10.1/y"})
        # Throttle sleep must NOT fire on first call (only on subsequent)
        self.assertEqual(sleep.call_count, 0)

    def test_back_to_back_calls_throttle_to_one_req_per_second(self) -> None:
        """Default unauthenticated tier: 1.0s min interval between calls.
        Second call within the interval should sleep the remainder.

        Explicit `min_interval_seconds=1.0` so the test is hermetic
        against `S2_API_KEY` set in the environment (codex R1 P2)."""
        sleep = MagicMock()
        # clock: first request at t=1000.0, second at t=1000.3 (0.3s later
        # — throttle should sleep 0.7s before issuing second request)
        clock = MagicMock(side_effect=[1000.0, 1000.3, 1000.3])
        client = ssc.SemanticScholarClient(
            sleep=sleep, clock=clock, min_interval_seconds=1.0
        )
        resp_factory = lambda: self._good_resp({"paperId": "x", "title": "T"})
        with patch(
            "urllib.request.urlopen",
            MagicMock(side_effect=[resp_factory(), resp_factory()]),
        ):
            client.lookup({"title": "T", "doi": "10.1/y"})
            client.lookup({"title": "T", "doi": "10.1/z"})
        # One sleep call between the two requests
        self.assertEqual(sleep.call_count, 1)
        slept = sleep.call_args[0][0]
        self.assertAlmostEqual(slept, 0.7, places=2)

    def test_back_to_back_calls_past_interval_do_not_sleep(self) -> None:
        """If enough time elapsed naturally between calls, no extra sleep
        is needed — the throttle is a floor, not a ceiling. Explicit
        min_interval_seconds for env-hermeticity (codex R1 P2)."""
        sleep = MagicMock()
        # Second call 2.5s after first; no throttle sleep needed
        clock = MagicMock(side_effect=[1000.0, 1002.5, 1002.5])
        client = ssc.SemanticScholarClient(
            sleep=sleep, clock=clock, min_interval_seconds=1.0
        )
        resp_factory = lambda: self._good_resp({"paperId": "x", "title": "T"})
        with patch(
            "urllib.request.urlopen",
            MagicMock(side_effect=[resp_factory(), resp_factory()]),
        ):
            client.lookup({"title": "T", "doi": "10.1/y"})
            client.lookup({"title": "T", "doi": "10.1/z"})
        # No throttle-sleep calls (429 retry sleeps would also count but
        # we don't hit any 429 here)
        self.assertEqual(sleep.call_count, 0)

    def test_api_key_lowers_interval_to_authenticated_tier(self) -> None:
        """Per protocol line 6: authenticated tier is 10 req/s = 0.1s
        interval. When S2_API_KEY is set, throttle drops accordingly."""
        sleep = MagicMock()
        clock = MagicMock(side_effect=[1000.0, 1000.03, 1000.03])
        client = ssc.SemanticScholarClient(
            api_key="test-key", sleep=sleep, clock=clock
        )
        resp_factory = lambda: self._good_resp({"paperId": "x", "title": "T"})
        with patch(
            "urllib.request.urlopen",
            MagicMock(side_effect=[resp_factory(), resp_factory()]),
        ):
            client.lookup({"title": "T", "doi": "10.1/y"})
            client.lookup({"title": "T", "doi": "10.1/z"})
        # 0.1 - 0.03 = 0.07s sleep on authenticated tier
        self.assertEqual(sleep.call_count, 1)
        slept = sleep.call_args[0][0]
        self.assertAlmostEqual(slept, 0.07, places=2)

    def test_429_retry_refreshes_throttle_anchor(self) -> None:
        """F5 closure (simplify efficiency): if `_last_request_at` is not
        refreshed after a 429 backoff, the next outer call paces against
        entry time + N × backoff already elapsed, then under-sleeps and
        re-triggers 429. After fix: anchor refreshes to actual wake time.
        Explicit min_interval_seconds for env-hermeticity (codex R1 P2)."""
        sleep = MagicMock()
        # Clock sequence:
        # call 1 entry elapsed check (none, first call) - not used
        # call 1 entry write t=1000.0
        # call 1 429-retry write t=1002.0 (after 2s backoff)
        # call 2 entry elapsed check t=1002.0 (no extra sleep, 0s elapsed
        #   from anchor with 1s interval = sleep 1.0s)
        # call 2 entry write t=1003.0
        clock = MagicMock(side_effect=[1000.0, 1002.0, 1002.0, 1003.0])
        client = ssc.SemanticScholarClient(
            sleep=sleep, clock=clock, min_interval_seconds=1.0
        )
        good = _mock_response({"paperId": "x", "title": "T"})

        def urlopen_side(*args, **kwargs):
            urlopen_side.count += 1
            if urlopen_side.count == 1:
                raise urllib.error.HTTPError(
                    "u", 429, "Too Many", {}, io.BytesIO(b"")
                )
            return good
        urlopen_side.count = 0

        with patch("urllib.request.urlopen", urlopen_side):
            client.lookup({"title": "T", "doi": "10.1/y"})
            client.lookup({"title": "T", "doi": "10.1/z"})
        # Sleeps: one 2s backoff for the 429, one 1s for the throttle on
        # the 2nd outer call (anchor is fresh at t=1002 so elapsed=0,
        # remaining=1.0)
        self.assertEqual(sleep.call_count, 2)
        self.assertAlmostEqual(sleep.call_args_list[0][0][0], 2.0, places=2)
        self.assertAlmostEqual(sleep.call_args_list[1][0][0], 1.0, places=2)

    def test_explicit_min_interval_override(self) -> None:
        """Caller can override the throttle interval (e.g., for tests or
        for a hypothetical higher tier)."""
        sleep = MagicMock()
        clock = MagicMock(side_effect=[1000.0, 1000.0, 1000.0])
        client = ssc.SemanticScholarClient(
            sleep=sleep, clock=clock, min_interval_seconds=0.0
        )
        resp_factory = lambda: self._good_resp({"paperId": "x", "title": "T"})
        with patch(
            "urllib.request.urlopen",
            MagicMock(side_effect=[resp_factory(), resp_factory()]),
        ):
            client.lookup({"title": "T", "doi": "10.1/y"})
            client.lookup({"title": "T", "doi": "10.1/z"})
        # min_interval=0 means never throttle
        self.assertEqual(sleep.call_count, 0)


class OutageLatchTest(unittest.TestCase):
    """#115 R5-3: when urlopen raises URLError (network down), the client
    must latch into unavailable mode so subsequent calls fail fast
    without waiting on a known-dead service. Reset method allows
    long-running tools to retry recovery between passports."""

    def test_url_error_latches_client_unavailable(self) -> None:
        """First call hits URLError → SemanticScholarUnavailable. Second
        call must raise immediately WITHOUT invoking urlopen — the
        latch short-circuits the network entirely."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        urlopen = MagicMock(
            side_effect=urllib.error.URLError("connection refused")
        )
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "T", "doi": "10.1/y"})
            # urlopen was called once for the first lookup
            self.assertEqual(urlopen.call_count, 1)
            # Second lookup must NOT call urlopen — latched short-circuit
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "Other", "doi": "10.1/z"})
            self.assertEqual(urlopen.call_count, 1, "latched call must skip network")

    def test_reset_outage_latch_restores_normal_behavior(self) -> None:
        """A long-running tool between passport batches can call
        reset_outage_latch() to retry the network."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        # First call latches
        urlopen = MagicMock(side_effect=urllib.error.URLError("down"))
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "T", "doi": "10.1/y"})

        # Reset latch
        client.reset_outage_latch()

        # Subsequent call should re-attempt urlopen (and succeed in this
        # mock scenario)
        urlopen_good = MagicMock(
            return_value=_mock_response({"paperId": "x", "title": "T"})
        )
        with patch("urllib.request.urlopen", urlopen_good):
            result = client.lookup({"title": "T", "doi": "10.1/y"})
        self.assertEqual(result, {"matched": True, "paperId": "x"})
        self.assertEqual(urlopen_good.call_count, 1)

    def test_response_read_oserror_also_latches(self) -> None:
        """Codex R2 closure: protocol §"On API failure" treats transport-
        level network failures uniformly, regardless of which urllib
        boundary surfaces them. A socket read timeout during resp.read()
        must latch the batch just like URLError at urlopen() time —
        otherwise a real outage retries 30s per entry × N."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        resp = MagicMock()
        resp.read.side_effect = OSError("socket read timeout")
        resp.__enter__ = MagicMock(return_value=resp)
        resp.__exit__ = MagicMock(return_value=False)
        urlopen = MagicMock(return_value=resp)
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "T", "doi": "10.1/y"})
            self.assertEqual(urlopen.call_count, 1)
            # Second call should short-circuit — no second urlopen
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "Other", "doi": "10.1/z"})
            self.assertEqual(urlopen.call_count, 1, "latched after read-timeout")

    def test_http_error_does_not_latch(self) -> None:
        """HTTP 5xx is a server-side error, not a transport-level outage.
        The protocol §"On API failure" says network errors skip the
        remaining batch; HTTP failures don't. Make sure 5xx doesn't
        falsely latch the client."""
        client = ssc.SemanticScholarClient(sleep=MagicMock())
        urlopen = MagicMock(side_effect=[
            urllib.error.HTTPError("u", 503, "Service Unavailable", {}, io.BytesIO(b"")),
        ])
        with patch("urllib.request.urlopen", urlopen):
            with self.assertRaises(SemanticScholarUnavailable):
                client.lookup({"title": "T", "doi": "10.1/y"})
        # 5xx fired but client should not be latched
        self.assertFalse(client._latched_unavailable)


class CLIWiringTest(unittest.TestCase):
    """Codex R1-1 closure: CLI was unrunnable because NotImplementedError
    fired before reading the passport. Verify the production wiring path
    now actually constructs a SemanticScholarClient instance."""

    def test_build_default_ss_client_returns_real_client(self) -> None:
        import migrate_literature_corpus_to_v3_7_3 as mig
        client = mig._build_default_ss_client()
        self.assertIsInstance(client, ssc.SemanticScholarClient)


if __name__ == "__main__":
    unittest.main()
