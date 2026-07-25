"""Tests for the #127 v3.10 terminal-policy-layer seed migration tool.

Pure local YAML transform — NO API client / mock (codex consult 2026-05-31 Q3:
carrying the v3.9.0 client fixtures forward would add test noise without covering
the new risk). Covers the deep-merge idempotent seed matrix + codex Q3's added
structural / malformed cases.

Spec: docs/design/2026-05-31-ars-v3.10-policy-layer-rescope-spec.md §3 PR-B item 12
      + §4 acceptance #7.
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import migrate_literature_corpus_to_v3_10 as mig  # noqa: E402


def _yaml():
    from ruamel.yaml import YAML
    y = YAML()
    y.preserve_quotes = True
    y.indent(mapping=2, sequence=4, offset=2)
    return y


def _v3_9_0_entry(**overrides):
    """A v3.9.0-onward entry (carries a lookup signal → passport in scope)."""
    e = {
        "citation_key": "smith2024",
        "title": "Sample",
        "authors": [{"family": "Smith"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "contamination_signals": {"semantic_scholar_unmatched": False},
    }
    e.update(overrides)
    return e


def _write_passport(tmp_path, doc):
    p = tmp_path / "passport.yaml"
    with p.open("w") as f:
        _yaml().dump(doc, f)
    return p


def _read_passport(p):
    with p.open() as f:
        return _yaml().load(f)


class SeedWholeBlockTest(unittest.TestCase):
    def test_seeds_both_keys_advisory_when_absent(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {"literature_corpus": [_v3_9_0_entry()]})
            report = mig.migrate_passport(p, dry_run=False)
            self.assertEqual(
                report["seeded_keys"],
                ["contamination_triangulation", "temporal_integrity"],
            )
            doc = _read_passport(p)
            self.assertEqual(doc["terminal_policies"]["contamination_triangulation"], "advisory")
            self.assertEqual(doc["terminal_policies"]["temporal_integrity"], "advisory")


class DeepMergeTest(unittest.TestCase):
    def test_partial_preexisting_strict_preserved(self) -> None:
        """User pre-set contamination_triangulation: strict → preserved; the
        missing temporal_integrity key seeded advisory (deep-merge, R1 P1)."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {
                "terminal_policies": {"contamination_triangulation": "strict"},
                "literature_corpus": [_v3_9_0_entry()],
            })
            report = mig.migrate_passport(p, dry_run=False)
            self.assertEqual(report["seeded_keys"], ["temporal_integrity"])
            self.assertEqual(report["preserved_keys"], ["contamination_triangulation"])
            doc = _read_passport(p)
            self.assertEqual(doc["terminal_policies"]["contamination_triangulation"], "strict")
            self.assertEqual(doc["terminal_policies"]["temporal_integrity"], "advisory")

    def test_strict_articles_only_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {
                "terminal_policies": {"contamination_triangulation": "strict_articles_only"},
                "literature_corpus": [_v3_9_0_entry()],
            })
            mig.migrate_passport(p, dry_run=False)
            doc = _read_passport(p)
            self.assertEqual(
                doc["terminal_policies"]["contamination_triangulation"], "strict_articles_only"
            )


class IdempotencyTest(unittest.TestCase):
    def test_rerun_byte_stable(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {"literature_corpus": [_v3_9_0_entry()]})
            mig.migrate_passport(p, dry_run=False)
            first = p.read_text()
            report2 = mig.migrate_passport(p, dry_run=False)
            second = p.read_text()
            self.assertEqual(report2["seeded_keys"], [])  # nothing left to seed
            self.assertEqual(first, second, "second run must be byte-stable")


class DryRunTest(unittest.TestCase):
    def test_dry_run_writes_nothing(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {"literature_corpus": [_v3_9_0_entry()]})
            before = p.read_text()
            report = mig.migrate_passport(p, dry_run=True)
            self.assertEqual(
                report["seeded_keys"],
                ["contamination_triangulation", "temporal_integrity"],
            )
            self.assertEqual(p.read_text(), before, "dry-run must not write")


class NoVenueBackfillTest(unittest.TestCase):
    def test_does_not_touch_venue_type(self) -> None:
        """Forbidden: backfill venue_type from free-form venue (R-L3-2-D)."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            entry = _v3_9_0_entry(venue="Journal of Examples")
            p = _write_passport(tmp, {"literature_corpus": [entry]})
            mig.migrate_passport(p, dry_run=False)
            doc = _read_passport(p)
            self.assertNotIn("venue_type", doc["literature_corpus"][0])
            self.assertNotIn("venue_type_provenance", doc["literature_corpus"][0])


class ScopeBoundaryTest(unittest.TestCase):
    def test_pre_v3_9_0_passport_reported_out_of_scope(self) -> None:
        """A non-empty corpus with no v3.9.0 lookup signal anywhere is pre-v3.9.0:
        out of scope, NOT silently skipped (run v3.9.0 migration first)."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            entry = {
                "citation_key": "old2020",
                "title": "Old",
                "authors": [{"family": "Old"}],
                "year": 2020,
                "source_pointer": "file:///old.pdf",
            }  # no contamination_signals at all
            p = _write_passport(tmp, {"literature_corpus": [entry]})
            before = p.read_text()
            report = mig.migrate_passport(p, dry_run=False)
            self.assertTrue(report["out_of_scope"])
            self.assertFalse(report["in_scope"])
            self.assertEqual(p.read_text(), before, "out-of-scope passport untouched")

    def test_empty_corpus_seeded_corpus_independent(self) -> None:
        """Empty corpus → seed is corpus-independent, treated as in scope."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {"literature_corpus": []})
            report = mig.migrate_passport(p, dry_run=False)
            self.assertTrue(report["in_scope"])
            self.assertEqual(
                report["seeded_keys"],
                ["contamination_triangulation", "temporal_integrity"],
            )


class MalformedShapeTest(unittest.TestCase):
    """codex Q3: malformed / round-trip structural cases."""

    def test_top_level_not_a_dict_errors(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = tmp / "passport.yaml"
            with p.open("w") as f:
                _yaml().dump(["just", "a", "list"], f)
            with self.assertRaises(mig.PassportShapeError):
                mig.migrate_passport(p, dry_run=False)

    def test_terminal_policies_null_errors(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = tmp / "passport.yaml"
            p.write_text("terminal_policies: null\nliterature_corpus:\n  - citation_key: smith2024\n    title: S\n    authors:\n      - family: Smith\n    year: 2024\n    source_pointer: file:///x.pdf\n    contamination_signals:\n      semantic_scholar_unmatched: false\n")
            with self.assertRaises(mig.PassportShapeError):
                mig.migrate_passport(p, dry_run=False)

    def test_terminal_policies_scalar_errors(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {
                "terminal_policies": "strict",  # scalar, not a mapping
                "literature_corpus": [_v3_9_0_entry()],
            })
            with self.assertRaises(mig.PassportShapeError):
                mig.migrate_passport(p, dry_run=False)


class CommentPreservationTest(unittest.TestCase):
    def test_existing_comments_survive_round_trip(self) -> None:
        """ruamel round-trip must preserve comments / key order (codex Q3)."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = tmp / "passport.yaml"
            p.write_text(
                "# top comment\n"
                "version: 9  # inline\n"
                "literature_corpus:\n"
                "  - citation_key: smith2024\n"
                "    title: S\n"
                "    authors:\n"
                "      - family: Smith\n"
                "    year: 2024\n"
                "    source_pointer: file:///x.pdf\n"
                "    contamination_signals:\n"
                "      semantic_scholar_unmatched: false\n"
            )
            mig.migrate_passport(p, dry_run=False)
            text = p.read_text()
            self.assertIn("# top comment", text)
            self.assertIn("# inline", text)
            self.assertIn("terminal_policies", text)

    def test_unknown_existing_terminal_policies_key_preserved(self) -> None:
        """A future / unknown key already under terminal_policies is preserved
        (the seed only ADDS the two known default keys)."""
        with tempfile.TemporaryDirectory() as d:
            tmp = Path(d)
            p = _write_passport(tmp, {
                "terminal_policies": {"future_key": "some_value"},
                "literature_corpus": [_v3_9_0_entry()],
            })
            mig.migrate_passport(p, dry_run=False)
            doc = _read_passport(p)
            self.assertEqual(doc["terminal_policies"]["future_key"], "some_value")
            self.assertEqual(doc["terminal_policies"]["contamination_triangulation"], "advisory")


if __name__ == "__main__":
    unittest.main()
