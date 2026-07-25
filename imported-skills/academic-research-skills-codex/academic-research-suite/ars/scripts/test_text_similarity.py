#!/usr/bin/env python3
"""Tests for `scripts/_text_similarity.py` — shared title-similarity helpers
extracted from `semantic_scholar_client.py` / `openalex_client.py` /
`crossref_client.py` to prevent sibling drift (#128 v3.9.1 housekeeping).

These tests rebuild the byte-equivalent behavior previously triple-implemented
in each client. The 3 client modules will import these helpers after the
extraction lands; their existing tests continue to verify the *integration*
(client uses similarity correctly) while these tests verify the *behavior*
(normalization + threshold semantics) of the shared module itself.
"""
from __future__ import annotations

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import _text_similarity as ts  # noqa: E402


class NormalizeTitleTest(unittest.TestCase):
    """Per protocol §"Query Patterns" Pattern 1: case-insensitive, punctuation
    stripped (becomes whitespace), whitespace collapsed."""

    def test_lowercases(self) -> None:
        self.assertEqual(ts._normalize_title("Foo Bar Baz"), "foo bar baz")

    def test_punctuation_becomes_whitespace_then_collapsed(self) -> None:
        self.assertEqual(ts._normalize_title("Foo,  Bar... Baz!"), "foo bar baz")

    def test_acronym_dots_collapse(self) -> None:
        self.assertEqual(ts._normalize_title("R.A.G."), "r a g")

    def test_empty_string(self) -> None:
        self.assertEqual(ts._normalize_title(""), "")

    def test_whitespace_only(self) -> None:
        self.assertEqual(ts._normalize_title("   \t\n  "), "")

    def test_already_normalized_unchanged(self) -> None:
        self.assertEqual(ts._normalize_title("attention is all you need"), "attention is all you need")


class SimilarityTest(unittest.TestCase):
    """SequenceMatcher.ratio over normalized titles."""

    def test_acronym_punctuation_clears_threshold(self) -> None:
        """Codex R4-1 closure (preserved from S2 client tests): 'R.A.G.' vs
        'RAG' clears 0.70 after normalize."""
        self.assertGreaterEqual(ts._similarity("R.A.G.", "RAG"), 0.70)

    def test_punctuation_stripped_before_similarity(self) -> None:
        self.assertGreater(
            ts._similarity(
                "Attention Is All You Need: A Transformers Story",
                "attention is all you need a transformers story",
            ),
            0.95,
        )

    def test_identical_strings_score_one(self) -> None:
        self.assertEqual(ts._similarity("foo bar", "foo bar"), 1.0)

    def test_completely_different_strings_score_low(self) -> None:
        self.assertLess(ts._similarity("alpha beta gamma", "xyz qrs uvw"), 0.3)


class ConstantsTest(unittest.TestCase):
    """Lock the magic numbers — these are protocol-level invariants, not
    arbitrary tuning."""

    def test_title_similarity_threshold_is_protocol_value(self) -> None:
        """Per PaperOrchestra (Song et al. 2026 Appx D.3) + protocol §Query
        Patterns Pattern 1."""
        self.assertEqual(ts._TITLE_SIMILARITY_THRESHOLD, 0.70)

    def test_backoff_seconds(self) -> None:
        """Per protocol: 429 → 2s backoff × 3 retries."""
        self.assertEqual(ts._BACKOFF_SECONDS, 2.0)

    def test_max_retries(self) -> None:
        self.assertEqual(ts._MAX_RETRIES, 3)

    def test_punct_translation_has_all_punctuation(self) -> None:
        """`_PUNCT_TRANSLATION` should map every string.punctuation char to ' '."""
        import string

        for c in string.punctuation:
            self.assertEqual(ts._PUNCT_TRANSLATION[ord(c)], " ", f"char {c!r} not mapped to space")


if __name__ == "__main__":
    unittest.main()
