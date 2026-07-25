#!/usr/bin/env python3
"""#431 — exact-title-or-bust acceptance regression tests.

The v5 architecture pivot (spec docs/design/2026-06-13-431-title-match-hardening-spec.md
§0.12): a NON-exact title is never promoted to `matched` on title-similarity +
year/author alone — that high-overlap-same-author signal is the shared signature
of an author's own related-but-distinct works (a correction and its original, a
reply and its target, Part I / Part II, a no-ordinal companion). The only
disambiguator all four resolvers can compute is the exact normalized title.

These tests pin the behavior the pre-existing client tests did NOT cover: the
pre-#431 clients returned the highest-ratio candidate regardless of exactness,
so a high-ratio related work was wrongly `matched`. Each client test below feeds
a candidate that clears the 0.70 ratio but is NOT an exact normalized title and
asserts the title fallback now yields no match; the legitimate exact / acronym /
case variants still match; F3 ordering reaches a correct exact #2 past a
non-exact #1; an exact-but-generic title with no corroborating ID stays
unmatched; and the resolver→reducer chain maps a title-keyed miss to
`unresolvable` (never a false `false`).
"""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))


def _json_resp(payload: dict) -> MagicMock:
    resp = MagicMock()
    resp.read.return_value = json.dumps(payload).encode("utf-8")
    resp.__enter__ = MagicMock(return_value=resp)
    resp.__exit__ = MagicMock(return_value=None)
    return resp


def _atom(*titles: str) -> bytes:
    entries = "".join(
        "<entry>"
        "<id>http://arxiv.org/abs/1706.03762v5</id>"
        f"<title>{t}</title>"
        "<published>2017-06-12T00:00:00Z</published>"
        "</entry>"
        for t in titles
    )
    body = (
        '<?xml version="1.0" encoding="UTF-8"?>'
        '<feed xmlns="http://www.w3.org/2005/Atom">'
        + entries
        + "</feed>"
    )
    return body.encode("utf-8")


def _atom_resp(*titles: str) -> MagicMock:
    resp = MagicMock()
    resp.read.return_value = _atom(*titles)
    resp.__enter__ = MagicMock(return_value=resp)
    resp.__exit__ = MagicMock(return_value=None)
    return resp


# A real R4 false-positive (spec §0.12): same first 4 words, ratio ~0.90, but a
# DISTINCT work — different topic in the tail. Non-exact ⇒ must NOT match.
_CITED = "Federated Learning for Mobile Keyboard Prediction"
_RELATED_WORK = "Federated Learning for Mobile Health Prediction"


class CrossrefExactOrBustTest(unittest.TestCase):
    def _search(self, *cand_titles, year=None):
        from crossref_client import CrossrefClient

        payload = {"message": {"items": [{"title": [t]} for t in cand_titles]}}
        with patch("urllib.request.urlopen", return_value=_json_resp(payload)):
            return CrossrefClient().title_search(_CITED, year=year)

    def test_non_exact_high_ratio_does_not_match(self):
        self.assertIsNone(self._search(_RELATED_WORK))

    def test_exact_title_matches(self):
        result = self._search(_CITED)
        self.assertIsNotNone(result)
        self.assertEqual(result["title"], [_CITED])

    def test_acronym_variant_matches(self):
        from crossref_client import CrossrefClient

        payload = {"message": {"items": [
            {"title": ["RAG: Retrieval Augmented Generation"]}
        ]}}
        with patch("urllib.request.urlopen", return_value=_json_resp(payload)):
            result = CrossrefClient().title_search(
                "R.A.G.: Retrieval Augmented Generation"
            )
        self.assertIsNotNone(result)  # dotted-acronym normalizes byte-equal

    def test_f3_ordering_reaches_exact_second_candidate(self):
        # #1 is the high-ratio related work (non-exact), #2 is the exact work.
        # Pre-#431 returned #1 and dropped the real work to unresolvable.
        result = self._search(_RELATED_WORK, _CITED)
        self.assertIsNotNone(result)
        self.assertEqual(result["title"], [_CITED])

    def test_generic_exact_title_no_id_does_not_match(self):
        # §0.12.2: a bare generic title is never promoted on the title path
        # (no ID can corroborate here). Even an exact 'Editorial'/'Editorial'
        # returns no match.
        from crossref_client import CrossrefClient

        payload = {"message": {"items": [{"title": ["Editorial"]}]}}
        with patch("urllib.request.urlopen", return_value=_json_resp(payload)):
            result = CrossrefClient().title_search("Editorial")
        self.assertIsNone(result)


class OpenAlexExactOrBustTest(unittest.TestCase):
    def _search(self, *cand_titles, year=None):
        from openalex_client import OpenAlexClient

        payload = {"results": [{"title": t} for t in cand_titles]}
        with patch("urllib.request.urlopen", return_value=_json_resp(payload)):
            return OpenAlexClient().title_search(_CITED, year=year)

    def test_non_exact_high_ratio_does_not_match(self):
        self.assertIsNone(self._search(_RELATED_WORK))

    def test_exact_title_matches(self):
        result = self._search(_CITED)
        self.assertIsNotNone(result)
        self.assertEqual(result["title"], _CITED)

    def test_generic_exact_title_no_id_does_not_match(self):
        from openalex_client import OpenAlexClient

        payload = {"results": [{"title": "Editorial"}]}
        with patch("urllib.request.urlopen", return_value=_json_resp(payload)):
            self.assertIsNone(OpenAlexClient().title_search("Editorial"))


class ArxivExactOrBustTest(unittest.TestCase):
    def _search(self, *cand_titles, year=None):
        from arxiv_client import ArxivClient

        with patch("urllib.request.urlopen", return_value=_atom_resp(*cand_titles)):
            return ArxivClient().title_search(_CITED, year=year)

    def test_non_exact_high_ratio_does_not_match(self):
        self.assertIsNone(self._search(_RELATED_WORK))

    def test_exact_title_matches(self):
        result = self._search(_CITED)
        self.assertIsNotNone(result)
        self.assertEqual(result["title"], _CITED)

    def test_generic_exact_title_no_id_does_not_match(self):
        from arxiv_client import ArxivClient

        with patch("urllib.request.urlopen", return_value=_atom_resp("Editorial")):
            self.assertIsNone(ArxivClient().title_search("Editorial"))


class SemanticScholarExactOrBustTest(unittest.TestCase):
    def _search(self, *cand_titles, year=None):
        import semantic_scholar_client as ssc

        payload = {"data": [{"title": t, "paperId": f"p{i}"}
                            for i, t in enumerate(cand_titles)]}
        resp = _json_resp(payload)
        with patch("urllib.request.urlopen", return_value=resp):
            client = ssc.SemanticScholarClient(sleep=MagicMock())
            return client._lookup_by_title(_CITED, year)

    def test_non_exact_high_ratio_does_not_match(self):
        self.assertIs(self._search(_RELATED_WORK)["matched"], False)

    def test_exact_title_matches(self):
        self.assertIs(self._search(_CITED)["matched"], True)

    def test_f3_ordering_reaches_exact_second_candidate(self):
        result = self._search(_RELATED_WORK, _CITED)
        self.assertIs(result["matched"], True)

    def test_generic_exact_title_no_id_does_not_match(self):
        self.assertIs(self._search("Editorial")["matched"], False)


class ExactNormalizedTitleHelperTest(unittest.TestCase):
    """Direct pins on the exact_normalized_title helper (#431 §0.12.1). The
    acronym pre-pass must only ADD matches over the base normalization, never
    drop one the base form already had — codex round-6 P2 caught that an
    acronym-only equality check regressed a punctuation-only variant where
    exactly one side is a contiguous initialism."""

    def test_base_equal_punctuation_variant_matches(self):
        from _text_similarity import exact_normalized_title

        # base form makes these byte-equal ('d h lawrence'), but the acronym
        # form does not ('dh' vs 'd h') — must still be exact via base equality.
        self.assertTrue(exact_normalized_title("D.H. Lawrence", "D. H. Lawrence"))
        self.assertTrue(exact_normalized_title("U.S. policy", "U. S. policy"))
        self.assertTrue(
            exact_normalized_title("U.S.A. policy", "U. S. A. policy")
        )

    def test_acronym_only_equal_variant_matches(self):
        from _text_similarity import exact_normalized_title

        # base form differs ('r a g x' vs 'rag x'); acronym collapse makes them
        # equal — the original #431 acronym carve-out.
        self.assertTrue(exact_normalized_title("R.A.G.: x", "RAG: x"))

    def test_distinct_initialisms_do_not_match(self):
        from _text_similarity import exact_normalized_title

        # different initials are a different work — neither form equal.
        self.assertFalse(
            exact_normalized_title("D.H. Lawrence", "D.K. Lawrence")
        )


class ResolverVerdictNarrowingTest(unittest.TestCase):
    """End-to-end (spec §0.5 / §0.12.1): a non-exact title fallback on a
    title-only entry (no resolvable ID) must reduce to `unresolvable`, NEVER
    `false`. `false` is reserved for an ID-keyed miss (C-V6(a))."""

    def test_title_only_non_exact_reduces_to_unresolvable(self):
        import contamination_signals as cs
        from citation_verification_summary import reduce_lookup_verified

        # No DOI ⇒ queried_by='title'. Client title_search returns None (the v5
        # non-exact verdict). The resolver flow reports unmatched + title-keyed.
        client = MagicMock()
        client.title_search.return_value = None
        entry = {"citation_key": "x", "title": _CITED}  # no doi
        unmatched, matched_by, queried_by = cs._resolve_doi_then_title(entry, client)
        self.assertIs(unmatched, True)
        self.assertIsNone(matched_by)
        self.assertEqual(queried_by, "title")

        # The reducer maps a title-keyed unmatched to `unresolvable`, not false.
        verdict = reduce_lookup_verified({
            "crossref": {"status": "unmatched", "queried_by": "title"},
        })
        self.assertEqual(verdict, "unresolvable")


if __name__ == "__main__":
    unittest.main()
