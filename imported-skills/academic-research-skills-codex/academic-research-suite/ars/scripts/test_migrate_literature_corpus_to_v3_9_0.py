#!/usr/bin/env python3
"""#102 v3.9.0 cross-index triangulation backfill migration tool tests.

Tests scripts/migrate_literature_corpus_to_v3_9_0.py — the CLI that
backfills `openalex_unmatched` and `crossref_unmatched` on v3.7.3-onward
literature_corpus[] entries per v3.9.0 spec §3.7.

Design: docs/design/2026-05-17-ars-v3.9.0-cross-index-triangulation-measurement-spec.md
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import migrate_literature_corpus_to_v3_9_0 as mig  # noqa: E402

from openalex_client import OpenAlexUnavailable  # noqa: E402
from crossref_client import CrossrefUnavailable  # noqa: E402


# ---------------------------------------------------------------------------
# Mock client helpers
# ---------------------------------------------------------------------------

def _make_oa_client(matched_dois: frozenset[str] | None = None, matched_titles: frozenset[str] | None = None):
    """Mock OpenAlexClient.

    `matched_dois`: set of DOI strings that return a hit on doi_lookup_with_title_check.
    `matched_titles`: set of title strings that return a hit on title_search.
    Both default to empty (everything unmatched).
    """
    matched_dois = matched_dois or frozenset()
    matched_titles = matched_titles or frozenset()
    client = MagicMock()

    def doi_lookup(doi, expected_title):
        if doi in matched_dois:
            return {"title": expected_title}
        return None

    def title_search(title, year=None):
        if title in matched_titles:
            return {"title": title}
        return None

    client.doi_lookup_with_title_check.side_effect = doi_lookup
    client.title_search.side_effect = title_search
    return client


def _make_cr_client(matched_dois: frozenset[str] | None = None, matched_titles: frozenset[str] | None = None):
    """Mirror of _make_oa_client for CrossrefClient."""
    matched_dois = matched_dois or frozenset()
    matched_titles = matched_titles or frozenset()
    client = MagicMock()

    def doi_lookup(doi, expected_title):
        if doi in matched_dois:
            return {"title": expected_title}
        return None

    def title_search(title, year=None):
        if title in matched_titles:
            return {"title": title}
        return None

    client.doi_lookup_with_title_check.side_effect = doi_lookup
    client.title_search.side_effect = title_search
    return client


def _make_passport(tmp_path, entries):
    """Write a minimal passport YAML and return its Path."""
    from ruamel.yaml import YAML
    p = tmp_path / "passport.yaml"
    y = YAML()
    y.preserve_quotes = True
    y.indent(mapping=2, sequence=4, offset=2)
    with p.open("w") as f:
        y.dump({"version": 9, "literature_corpus": entries}, f)
    return p


# ============================================================================
# 1. Dry-run: no file write
# ============================================================================
class DryRunTest(unittest.TestCase):
    def test_dry_run_does_not_modify_file(self) -> None:
        """--dry-run prints diff but leaves file untouched."""
        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "smith2024",
                "title": "Some Paper",
                "authors": [{"family": "Smith"}],
                "year": 2024,
                "source_pointer": "doi:10.5555/abc",
                "doi": "10.5555/abc",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": True,
                },
            }])
            before = p.read_bytes()
            # OpenAlex/Crossref return no match — would set True on real run.
            report = mig.migrate_passport(
                p,
                oa_client=_make_oa_client(),
                cr_client=_make_cr_client(),
                dry_run=True,
            )
            after = p.read_bytes()
            self.assertEqual(before, after, "dry-run must not write")
            # Would-add should be 1 (both fields to be added to 1 entry)
            self.assertEqual(report["would_add"] if "would_add" in report else report["patched"], 1)


# ============================================================================
# 2. Full backfill: both new fields populated correctly
# ============================================================================
class BackfillTest(unittest.TestCase):
    def test_backfill_populates_two_new_fields(self) -> None:
        """openalex_unmatched + crossref_unmatched are added to eligible entry."""
        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "smith2024",
                "title": "Real Paper",
                "authors": [{"family": "Smith"}],
                "year": 2024,
                "source_pointer": "doi:10.5555/abc",
                "doi": "10.5555/abc",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": False,
                },
            }])
            # OpenAlex: DOI matches → openalex_unmatched=False
            # Crossref: DOI miss, title miss → crossref_unmatched=True
            oa = _make_oa_client(matched_dois=frozenset(["10.5555/abc"]))
            cr = _make_cr_client()

            report = mig.migrate_passport(
                p, oa_client=oa, cr_client=cr, dry_run=False
            )
            self.assertEqual(report["patched"], 1)
            doc = mig.load_passport(p)
            sig = doc["literature_corpus"][0]["contamination_signals"]
            self.assertIs(sig["openalex_unmatched"], False)
            self.assertIs(sig["crossref_unmatched"], True)


# ============================================================================
# 3. Manual entry: untouched entirely
# ============================================================================
class ManualSkipTest(unittest.TestCase):
    def test_manual_entry_skipped_entirely(self) -> None:
        """obtained_via='manual' entries are not modified."""
        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "manual1",
                "title": "User curated",
                "authors": [{"family": "User"}],
                "year": 2024,
                "source_pointer": "manual:1",
                "obtained_via": "manual",
                "contamination_signals": {
                    "preprint_post_llm_inflection": True,
                },
            }])
            before = p.read_bytes()
            report = mig.migrate_passport(
                p,
                oa_client=_make_oa_client(),
                cr_client=_make_cr_client(),
                dry_run=False,
            )
            after = p.read_bytes()
            self.assertEqual(before, after, "Manual entry was modified")
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_manual"], 1)


# ============================================================================
# 4. Pre-v3.7.3 entry: no semantic_scholar_unmatched → out of scope
# ============================================================================
class PreV373SkipTest(unittest.TestCase):
    def test_pre_v3_7_3_entry_skipped(self) -> None:
        """Entry without semantic_scholar_unmatched is out of v3.9.0 scope."""
        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "legacy1",
                "title": "Old entry",
                "authors": [{"family": "Old"}],
                "year": 2020,
                "source_pointer": "doi:10.5555/old",
                "obtained_via": "folder-scan",
                # No contamination_signals at all.
            }])
            before = p.read_bytes()
            report = mig.migrate_passport(
                p,
                oa_client=_make_oa_client(),
                cr_client=_make_cr_client(),
                dry_run=False,
            )
            after = p.read_bytes()
            self.assertEqual(before, after, "Pre-v3.7.3 entry was modified")
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_pre_v3_7_3"], 1)


# ============================================================================
# 5. Idempotency: already-complete entry untouched
# ============================================================================
class IdempotencyTest(unittest.TestCase):
    def test_idempotent_stable_fields(self) -> None:
        """Re-running on a fully-populated entry produces no change."""
        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "complete",
                "title": "Fully indexed",
                "authors": [{"family": "Yes"}],
                "year": 2024,
                "source_pointer": "doi:10.5555/yes",
                "doi": "10.5555/yes",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": False,
                    "openalex_unmatched": False,
                    "crossref_unmatched": False,
                },
            }])
            before = p.read_bytes()
            report = mig.migrate_passport(
                p,
                oa_client=_make_oa_client(),
                cr_client=_make_cr_client(),
                dry_run=False,
            )
            after = p.read_bytes()
            self.assertEqual(before, after, "Already-complete entry was modified")
            self.assertEqual(report["patched"], 0)
            self.assertEqual(report["skipped_complete"], 1)


# ============================================================================
# 6. Partial degradation: one field absent, one populated — only fills missing
# ============================================================================
class PartialDegradationTest(unittest.TestCase):
    def test_partial_degradation_fills_only_missing_field(self) -> None:
        """crossref_unmatched already set from prior run, openalex absent.

        OpenAlex now up → openalex_unmatched filled; crossref_unmatched preserved.
        Tests both stable-fields idempotency AND partial-fill eligibility.
        """
        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "partial",
                "title": "Partial backfill",
                "authors": [{"family": "X"}],
                "year": 2024,
                "source_pointer": "doi:10.5555/p",
                "doi": "10.5555/p",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": False,
                    "crossref_unmatched": False,  # populated from a prior run
                    # openalex_unmatched absent — to be filled
                },
            }])
            # OpenAlex: DOI match → False
            oa = _make_oa_client(matched_dois=frozenset(["10.5555/p"]))
            cr = _make_cr_client()  # not called (crossref already set)

            report = mig.migrate_passport(
                p, oa_client=oa, cr_client=cr, dry_run=False
            )
            self.assertEqual(report["patched"], 1)

            doc = mig.load_passport(p)
            sig = doc["literature_corpus"][0]["contamination_signals"]
            self.assertIs(sig["openalex_unmatched"], False)   # added
            self.assertIs(sig["crossref_unmatched"], False)   # preserved (not overwritten)

            # Crossref client must NOT have been consulted (field was already set)
            cr.doi_lookup_with_title_check.assert_not_called()
            cr.title_search.assert_not_called()


class ParallelDispatchTest(unittest.TestCase):
    """#138: when both fields are missing, the OpenAlex and Crossref calls for a
    single entry must be dispatched in parallel, not one-after-the-other.

    Verified with a 2-party threading.Barrier injected into both mock clients:
    each resolver call blocks on the barrier and only proceeds once *both* have
    arrived. A sequential implementation calls OpenAlex first and waits for it to
    return before it ever calls Crossref, so the second party never arrives and
    the barrier times out (BrokenBarrierError). A parallel implementation has
    both calls in flight at once, so the barrier releases and both return.
    """

    # Barrier timeout: large enough that a correct parallel impl never trips it
    # even on a loaded CI runner (the gated calls do no real I/O), small enough
    # that a sequential impl fails fast. Bump this if CI thread-starvation ever
    # produces a false BrokenBarrierError on a known-parallel implementation.
    _BARRIER_TIMEOUT_S = 5

    def test_both_resolvers_dispatched_in_parallel(self) -> None:
        import threading

        barrier = threading.Barrier(2, timeout=self._BARRIER_TIMEOUT_S)

        def _gated_oa_doi_lookup(doi, expected_title):
            barrier.wait()  # only releases if Crossref also arrives concurrently
            return None  # no match → openalex_unmatched True

        def _gated_cr_doi_lookup(doi, expected_title):
            barrier.wait()
            return None  # no match → crossref_unmatched True

        oa = MagicMock()
        oa.doi_lookup_with_title_check.side_effect = _gated_oa_doi_lookup
        oa.title_search.side_effect = lambda title, year=None: None
        cr = MagicMock()
        cr.doi_lookup_with_title_check.side_effect = _gated_cr_doi_lookup
        cr.title_search.side_effect = lambda title, year=None: None

        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "parallel",
                "title": "Parallel dispatch",
                "authors": [{"family": "P"}],
                "year": 2024,
                "source_pointer": "doi:10.5555/par",
                "doi": "10.5555/par",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": True,
                    # both openalex_unmatched + crossref_unmatched absent
                },
            }])

            # Sequential impl → barrier never gets its 2nd party → BrokenBarrierError.
            report = mig.migrate_passport(
                p, oa_client=oa, cr_client=cr, dry_run=False
            )

            self.assertEqual(report["patched"], 1)
            doc = mig.load_passport(p)
            sig = doc["literature_corpus"][0]["contamination_signals"]
            self.assertIs(sig["openalex_unmatched"], True)
            self.assertIs(sig["crossref_unmatched"], True)


class ApiDownDegradationTest(unittest.TestCase):
    """#138 risk 2+3: when one resolver raises its Unavailable exception inside
    the thread pool, that exception must surface back on the orchestrator thread,
    its field must be omitted (not written), the matching degraded_* counter must
    increment, and the OTHER resolver's field must still be filled cleanly.

    This path was previously untested for both the sequential and the parallel
    implementations; with the thread pool the exception now propagates out of
    Future.result(), so it is the most important behaviour to pin down.
    """

    def test_openalex_down_omits_field_and_fills_crossref(self) -> None:
        oa = MagicMock()
        oa.doi_lookup_with_title_check.side_effect = OpenAlexUnavailable(
            "openalex 503"
        )
        oa.title_search.side_effect = OpenAlexUnavailable("openalex 503")
        # Crossref healthy, no match → crossref_unmatched True.
        cr = _make_cr_client()

        with tempfile.TemporaryDirectory() as td:
            p = _make_passport(Path(td), [{
                "citation_key": "oa_down",
                "title": "OpenAlex down",
                "authors": [{"family": "D"}],
                "year": 2024,
                "source_pointer": "doi:10.5555/down",
                "doi": "10.5555/down",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": True,
                },
            }])

            report = mig.migrate_passport(
                p, oa_client=oa, cr_client=cr, dry_run=False
            )

            # Crossref filled, so the entry counts as patched.
            self.assertEqual(report["patched"], 1)
            self.assertEqual(report["degraded_openalex"], 1)
            self.assertEqual(report["degraded_crossref"], 0)

            doc = mig.load_passport(p)
            sig = doc["literature_corpus"][0]["contamination_signals"]
            # Failed API field omitted entirely, not written as a guessed value.
            self.assertNotIn("openalex_unmatched", sig)
            self.assertIs(sig["crossref_unmatched"], True)


if __name__ == "__main__":
    unittest.main()
