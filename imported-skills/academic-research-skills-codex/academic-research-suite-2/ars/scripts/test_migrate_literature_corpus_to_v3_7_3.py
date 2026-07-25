#!/usr/bin/env python3
"""#105 v3.7.3 contamination_signals backfill migration tool tests.

Tests scripts/migrate_literature_corpus_to_v3_7_3.py — the CLI that
backfills `contamination_signals` on pre-v3.7.3 literature_corpus[]
entries per v3.7.3 spec §3.2 R-L3-2-B.

Design: docs/design/2026-05-15-issue-105-contamination-signals-backfill-design.md
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import migrate_literature_corpus_to_v3_7_3 as mig  # noqa: E402


SAMPLE_PASSPORT_YAML = """\
# Material Passport for the SLR run
origin_skill: deep-research
origin_mode: systematic-review
origin_date: '2026-05-01T10:00:00Z'
verification_status: VERIFIED
version_label: research_v1
literature_corpus:
  - citation_key: chen2024ai
    title: AI in education
    authors:
      - family: Chen
        given: A
    year: 2024
    venue: arXiv
    doi: 10.1234/abc
    obtained_via: folder-scan
    source_pointer: file:///refs/chen2024.pdf
  - citation_key: smith2020old
    title: Old paper
    authors:
      - family: Smith
        given: B
    year: 2020
    venue: Nature
    doi: 10.5678/def
    obtained_via: folder-scan
    source_pointer: file:///refs/smith2020.pdf
  - citation_key: lopez2024manual
    title: Manual entry
    authors:
      - family: Lopez
        given: C
    year: 2024
    venue: bioRxiv
    obtained_via: manual
    source_pointer: file:///refs/lopez2024.pdf
"""


def _make_ss_client(unmatched_for_keys=()):
    """Build a mock SS client that returns no-match for the listed citation
    keys (so the entry gets semantic_scholar_unmatched: true) and match
    otherwise."""
    client = MagicMock()
    def lookup(entry):
        return {"matched": entry.get("citation_key") not in set(unmatched_for_keys)}
    client.lookup.side_effect = lookup
    return client


# ============================================================================
# Single-passport migration
# ============================================================================
class SinglePassportMigrationTest(unittest.TestCase):
    def test_dry_run_writes_no_file(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(SAMPLE_PASSPORT_YAML)
            before = p.read_text()
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=True
            )
            after = p.read_text()
            self.assertEqual(before, after, "dry-run must not write")
            self.assertEqual(report["patched"], 3)
            self.assertEqual(report["manual_unmatched_omitted"], 1)

    def test_patches_three_entries_per_emission_rules(self) -> None:
        """Per spec §3.2: emit object on every non-skipped entry, even
        when both signals are False (computed-and-clean is distinct from
        not-computed). All 3 sample entries get the object; manual entry
        omits the unmatched field."""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(SAMPLE_PASSPORT_YAML)
            report = mig.migrate_passport(
                p,
                ss_client=_make_ss_client(unmatched_for_keys=["chen2024ai"]),
                dry_run=False,
            )
            self.assertEqual(report["patched"], 3)
            doc = mig.load_passport(p)
            entries = doc["literature_corpus"]
            # chen2024ai: arXiv 2024 → preprint=true; SS no-match → unmatched=true
            chen = entries[0]
            self.assertEqual(
                chen["contamination_signals"],
                {"preprint_post_llm_inflection": True, "semantic_scholar_unmatched": True},
            )
            self.assertIn("contamination_signals_backfilled_at", chen)
            # smith2020old: Nature 2020 → preprint=false; SS match → unmatched=false
            smith = entries[1]
            self.assertEqual(
                smith["contamination_signals"],
                {"preprint_post_llm_inflection": False, "semantic_scholar_unmatched": False},
            )
            # lopez2024manual: bioRxiv 2024 manual → preprint=true; unmatched OMITTED
            lopez = entries[2]
            self.assertEqual(
                lopez["contamination_signals"],
                {"preprint_post_llm_inflection": True},
            )
            self.assertNotIn("semantic_scholar_unmatched", lopez["contamination_signals"])

    def test_idempotency_already_migrated_entry_skipped(self) -> None:
        """Re-running on an already-migrated entry must not re-compute,
        re-write, or update the backfilled_at timestamp."""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(SAMPLE_PASSPORT_YAML)
            mig.migrate_passport(p, ss_client=_make_ss_client(), dry_run=False)
            after_first = p.read_text()
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=False
            )
            after_second = p.read_text()
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_already_migrated"], 3)
            self.assertEqual(
                after_first, after_second,
                "re-run on migrated passport must be byte-identical",
            )

    def test_missing_venue_does_not_skip_entry(self) -> None:
        """Codex R1-2 closure: venue is schema-optional. When absent,
        Signal 1 correctly evaluates to False (venue not in PREPRINT_VENUES)
        and emission proceeds — that's a defined computation, not half-
        truth. Signal 2 (SS API) is still attempted. Skipping on venue
        absence would prevent the migration from filling in usable data."""
        yaml_no_venue = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: novenue2024
    title: No venue
    authors:
      - family: X
        given: Y
    year: 2024
    obtained_via: folder-scan
    source_pointer: file:///refs/novenue.pdf
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(yaml_no_venue)
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=False
            )
            self.assertEqual(report["patched"], 1)
            self.assertEqual(report["skipped_insufficient_data"], 0)
            doc = mig.load_passport(p)
            sig = doc["literature_corpus"][0]["contamination_signals"]
            self.assertEqual(sig["preprint_post_llm_inflection"], False)
            self.assertIn("semantic_scholar_unmatched", sig)

    def test_partial_fill_recovery_fills_unmatched_field(self) -> None:
        """Codex R1-3 closure: a previous run hit API degradation and
        wrote contamination_signals with only preprint_post_llm_inflection.
        Re-running with a healthy API must fill in semantic_scholar_unmatched
        without overwriting the original backfilled_at timestamp."""
        partial_yaml = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: chen2024ai
    title: AI in education
    authors:
      - family: Chen
        given: A
    year: 2024
    venue: arXiv
    doi: 10.1234/abc
    obtained_via: folder-scan
    source_pointer: file:///refs/chen2024.pdf
    contamination_signals:
      preprint_post_llm_inflection: true
    contamination_signals_backfilled_at: '2026-05-15T10:30:00Z'
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(partial_yaml)
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(unmatched_for_keys=["chen2024ai"]),
                dry_run=False,
            )
            self.assertEqual(report["patched"], 1)
            doc = mig.load_passport(p)
            entry = doc["literature_corpus"][0]
            self.assertEqual(
                entry["contamination_signals"],
                {"preprint_post_llm_inflection": True, "semantic_scholar_unmatched": True},
            )
            # Original timestamp preserved (no re-stamping on partial fill)
            self.assertEqual(
                entry["contamination_signals_backfilled_at"],
                "2026-05-15T10:30:00Z",
            )

    def test_partial_fill_without_provenance_sets_backfilled_at(self) -> None:
        """Codex R5-1 closure: an ingest-time partial entry (v3.7.3
        bibliography_agent wrote contamination_signals during S2
        degradation) lacks backfilled_at. When the migration fills in
        the missing field post-hoc, record provenance — otherwise the
        post-hoc mutation is indistinguishable from ingest-time data."""
        ingest_partial_yaml = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: chen2024ai
    title: AI in education
    authors:
      - family: Chen
        given: A
    year: 2024
    venue: arXiv
    doi: 10.1234/abc
    obtained_via: folder-scan
    source_pointer: file:///refs/chen2024.pdf
    contamination_signals:
      preprint_post_llm_inflection: true
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(ingest_partial_yaml)
            mig.migrate_passport(
                p,
                ss_client=_make_ss_client(unmatched_for_keys=["chen2024ai"]),
                dry_run=False,
            )
            doc = mig.load_passport(p)
            entry = doc["literature_corpus"][0]
            self.assertEqual(
                entry["contamination_signals"],
                {"preprint_post_llm_inflection": True, "semantic_scholar_unmatched": True},
            )
            self.assertIn("contamination_signals_backfilled_at", entry)

    def test_partial_fill_with_existing_provenance_preserves_timestamp(self) -> None:
        """R5-1 closure (companion): when partial entry already has
        backfilled_at (R1-3 case: prior migration run that hit API
        degradation), DON'T overwrite — the original timestamp is the
        canonical backfill record."""
        partial_with_ts = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: chen2024ai
    title: AI in education
    authors:
      - family: Chen
        given: A
    year: 2024
    venue: arXiv
    doi: 10.1234/abc
    obtained_via: folder-scan
    source_pointer: file:///refs/chen2024.pdf
    contamination_signals:
      preprint_post_llm_inflection: true
    contamination_signals_backfilled_at: '2025-01-01T00:00:00Z'
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(partial_with_ts)
            mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=False
            )
            doc = mig.load_passport(p)
            self.assertEqual(
                doc["literature_corpus"][0]["contamination_signals_backfilled_at"],
                "2025-01-01T00:00:00Z",
            )

    def test_verbose_emits_per_entry_decisions(self) -> None:
        """Codex R3-2 closure: --verbose must produce per-entry lines on
        stderr so users can audit what got patched / skipped / why."""
        import io
        from contextlib import redirect_stderr
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(SAMPLE_PASSPORT_YAML)
            buf = io.StringIO()
            with redirect_stderr(buf):
                mig.migrate_passport(
                    p,
                    ss_client=_make_ss_client(unmatched_for_keys=["chen2024ai"]),
                    dry_run=True,
                    verbose=True,
                )
            output = buf.getvalue()
            # Per-entry citation_key tags surface for all 3 entries
            self.assertIn("chen2024ai", output)
            self.assertIn("smith2020old", output)
            self.assertIn("lopez2024manual", output)
            self.assertIn("patch", output)

    def test_partial_fill_with_persistent_api_degradation_does_not_re_patch(self) -> None:
        """Codex R2-3 closure: when a partial entry's missing field
        STILL cannot be computed (API still degraded), the merge loop
        adds nothing. Don't claim it was patched, don't mark mutated."""
        partial_yaml = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: chen2024ai
    title: AI in education
    authors:
      - family: Chen
        given: A
    year: 2024
    venue: arXiv
    doi: 10.1234/abc
    obtained_via: folder-scan
    source_pointer: file:///refs/chen2024.pdf
    contamination_signals:
      preprint_post_llm_inflection: true
    contamination_signals_backfilled_at: '2026-05-15T10:30:00Z'
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(partial_yaml)
            before = p.read_text()
            # Simulate API still degraded — SS lookup raises
            from contamination_signals import SemanticScholarUnavailable
            bad_client = MagicMock()
            bad_client.lookup.side_effect = SemanticScholarUnavailable("still down")
            report = mig.migrate_passport(p, ss_client=bad_client, dry_run=False)
            after = p.read_text()
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_already_migrated"], 1)
            self.assertEqual(before, after, "no rewrite when nothing was added")

    def test_manual_entry_with_only_preprint_signal_is_complete(self) -> None:
        """A manual entry permanently omits semantic_scholar_unmatched
        (per spec §3.2 + schema allOf rule #4). An object with only
        preprint_post_llm_inflection on a manual entry is COMPLETE, not
        partial — re-running must skip."""
        manual_yaml = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: lopez2024manual
    title: Manual entry
    authors:
      - family: Lopez
        given: C
    year: 2024
    venue: bioRxiv
    obtained_via: manual
    source_pointer: file:///refs/lopez2024.pdf
    contamination_signals:
      preprint_post_llm_inflection: true
    contamination_signals_backfilled_at: '2026-05-15T10:30:00Z'
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(manual_yaml)
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=False
            )
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_already_migrated"], 1)

    def test_insufficient_data_entry_skipped(self) -> None:
        """An entry missing year cannot have Signal 1 computed reliably
        (year is in the AND); migration tool skips and logs the reason
        rather than emitting half-truth."""
        yaml_no_year = """\
origin_skill: deep-research
literature_corpus:
  - citation_key: noyear2024
    title: No year
    authors:
      - family: X
        given: Y
    venue: arXiv
    obtained_via: folder-scan
    source_pointer: file:///refs/noyear.pdf
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(yaml_no_year)
            # Note: schema-invalid passport — `year` is required. This test
            # exercises the migration tool's defensive behavior, not the
            # schema validator. Real corpora won't reach here, but if they
            # do (e.g., user hand-edited their YAML), we degrade gracefully.
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=False
            )
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_insufficient_data"], 1)

    def test_passport_without_literature_corpus_returns_zero_report(self) -> None:
        yaml_no_corpus = """\
origin_skill: deep-research
verification_status: VERIFIED
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(yaml_no_corpus)
            report = mig.migrate_passport(
                p, ss_client=_make_ss_client(), dry_run=False
            )
            self.assertEqual(report["processed"], 0)
            self.assertEqual(report["patched"], 0)


# ============================================================================
# Directory-scan mode
# ============================================================================
class DirectoryScanTest(unittest.TestCase):
    def test_scan_dir_finds_yaml_files(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "passport_a.yaml").write_text(SAMPLE_PASSPORT_YAML)
            (d / "passport_b.yaml").write_text(SAMPLE_PASSPORT_YAML)
            (d / "notes.txt").write_text("ignore me")
            paths = sorted(mig.discover_passports(d))
            self.assertEqual(
                [p.name for p in paths],
                ["passport_a.yaml", "passport_b.yaml"],
            )

    def test_scan_dir_is_non_recursive(self) -> None:
        """Per design §4.2: directory scan finds *.yaml non-recursively.
        A passport in a subdir is intentionally NOT discovered."""
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            (d / "passport.yaml").write_text(SAMPLE_PASSPORT_YAML)
            sub = d / "subdir"
            sub.mkdir()
            (sub / "nested.yaml").write_text(SAMPLE_PASSPORT_YAML)
            paths = sorted(mig.discover_passports(d))
            self.assertEqual([p.name for p in paths], ["passport.yaml"])

    def test_migrate_dir_runs_each_passport(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            d = Path(td)
            for name in ("a.yaml", "b.yaml"):
                (d / name).write_text(SAMPLE_PASSPORT_YAML)
            client = _make_ss_client(unmatched_for_keys=["chen2024ai"])
            agg = mig.migrate_directory(d, ss_client=client, dry_run=False)
            self.assertEqual(agg["files_processed"], 2)
            self.assertEqual(agg["entries_patched"], 6)  # 3 per passport × 2


# ============================================================================
# Comment + key-order preservation (ruamel.yaml round-trip)
# ============================================================================
class RoundTripPreservationTest(unittest.TestCase):
    def test_comments_preserved_after_migration(self) -> None:
        yaml_with_comments = """\
# Top-level comment about this passport
origin_skill: deep-research
literature_corpus:
  - citation_key: chen2024ai  # inline note about chen
    title: AI in education
    authors:
      - family: Chen
        given: A
    year: 2024
    venue: arXiv
    obtained_via: folder-scan
    source_pointer: file:///refs/chen2024.pdf
"""
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "passport.yaml"
            p.write_text(yaml_with_comments)
            mig.migrate_passport(p, ss_client=_make_ss_client(), dry_run=False)
            after = p.read_text()
            self.assertIn("# Top-level comment", after)
            self.assertIn("# inline note about chen", after)


if __name__ == "__main__":
    unittest.main()
