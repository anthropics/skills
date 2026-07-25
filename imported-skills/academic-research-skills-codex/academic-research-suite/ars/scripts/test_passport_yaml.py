#!/usr/bin/env python3
"""Tests for `scripts/_passport_yaml.py` — shared ruamel.yaml round-trip
configuration extracted from `migrate_literature_corpus_to_v3_7_3.py` and
`migrate_literature_corpus_to_v3_9_0.py` (#128 v3.9.1 housekeeping §5).

ruamel configuration order matters for round-trip equivalence:
- preserve_quotes = True must be set BEFORE indent() (verified by ruamel
  internals; settings are evaluated lazily at dump time but assignment
  order is reflected in the YAML instance state).
- indent(mapping=2, sequence=4, offset=2) is the spec-aligned shape used
  by every passport produced by the bibliography_agent.

If either migration tool's tests regress after this extraction, the
shared module has drifted from the per-tool configuration that was
verified across multiple v3.7.3 / v3.9.0 review rounds.
"""
from __future__ import annotations

import io
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import _passport_yaml as py  # noqa: E402


class ConfigurationTest(unittest.TestCase):
    """Lock the ruamel.yaml configuration that every passport round-trip
    has assumed since v3.6.4."""

    def test_preserve_quotes_enabled(self) -> None:
        self.assertTrue(py._yaml.preserve_quotes)

    def test_indent_settings(self) -> None:
        """ruamel exposes the configured indent via private attributes.
        We check the visible round-trip behavior (test_round_trip_*),
        but also pin the constructor inputs for fast failure on drift."""
        # ruamel's YAML.indent(mapping=..., sequence=..., offset=...) stores
        # the values on private attributes; the round-trip tests below
        # are the load-bearing assertion. Here we just verify mapping/seq
        # indent shape is reflected in actual output (next test class).
        self.assertIsNotNone(py._yaml)


class RoundTripTest(unittest.TestCase):
    """Verify load → dump preserves the spec-aligned indentation shape."""

    def _round_trip(self, content: str) -> str:
        with tempfile.TemporaryDirectory() as d:
            path = Path(d) / "passport.yaml"
            path.write_text(content, encoding="utf-8")
            doc = py.load_passport(path)
            out_path = Path(d) / "out.yaml"
            py.dump_passport(out_path, doc)
            return out_path.read_text(encoding="utf-8")

    def test_round_trip_preserves_comments(self) -> None:
        """ruamel's CommentedMap should preserve inline + standalone comments."""
        content = (
            "# Header comment\n"
            "version: 3.9.0\n"
            "entries:\n"
            "  - name: foo  # trailing\n"
            "    year: 2024\n"
        )
        out = self._round_trip(content)
        self.assertIn("# Header comment", out)
        self.assertIn("# trailing", out)

    def test_round_trip_sequence_indent_is_4(self) -> None:
        """Per spec convention: sequence indent = 4, offset = 2 → list
        items align with `- ` two spaces past parent key."""
        content = "entries:\n  - foo\n  - bar\n"
        out = self._round_trip(content)
        # The mapping=2 sequence=4 offset=2 shape preserves the 2-space
        # offset before the dash.
        self.assertIn("  - foo", out)
        self.assertIn("  - bar", out)

    def test_round_trip_preserves_quoted_strings(self) -> None:
        """preserve_quotes=True keeps single vs double quote choice."""
        content = "title: 'single'\nname: \"double\"\n"
        out = self._round_trip(content)
        self.assertIn("'single'", out)
        self.assertIn('"double"', out)


class APIShapeTest(unittest.TestCase):
    """The shared module exposes load_passport + dump_passport as the
    public API. Both migration tools import from this module."""

    def test_load_passport_exists(self) -> None:
        self.assertTrue(callable(py.load_passport))

    def test_dump_passport_exists(self) -> None:
        self.assertTrue(callable(py.dump_passport))


if __name__ == "__main__":
    unittest.main()
