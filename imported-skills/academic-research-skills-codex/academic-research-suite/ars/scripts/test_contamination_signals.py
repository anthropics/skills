#!/usr/bin/env python3
"""#105 v3.7.3 contamination_signals resolver tests.

Tests the two pure-function signals defined in v3.7.3 spec §3.2 that
the migration tool uses to backfill pre-v3.7.3 literature_corpus entries.

Signal 1 (preprint_post_llm_inflection): year >= 2024 AND venue in 10-server
closed list (per spec §3.2 Vector 1 + schema description).

Signal 2 (semantic_scholar_unmatched): SS API lookup with manual exemption
+ API degradation handling (per spec §3.2 Vector 2 + R-L3-2-B).

Design: docs/design/2026-05-15-issue-105-contamination-signals-backfill-design.md
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path
from unittest.mock import MagicMock

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import contamination_signals as cs  # noqa: E402


# ============================================================================
# Signal 1 — preprint_post_llm_inflection
# ============================================================================
class PreprintSignalTest(unittest.TestCase):
    """Signal 1 per v3.7.3 spec §3.2 Vector 1: True iff year >= 2024 AND
    venue ∈ 10-server closed list."""

    def test_arxiv_2024_returns_true(self) -> None:
        self.assertTrue(cs.compute_preprint_signal({"year": 2024, "venue": "arXiv"}))

    def test_arxiv_2023_returns_false(self) -> None:
        # Year boundary: 2023 is below threshold
        self.assertFalse(cs.compute_preprint_signal({"year": 2023, "venue": "arXiv"}))

    def test_arxiv_2025_returns_true(self) -> None:
        self.assertTrue(cs.compute_preprint_signal({"year": 2025, "venue": "arXiv"}))

    def test_biorxiv_2024_returns_true(self) -> None:
        self.assertTrue(cs.compute_preprint_signal({"year": 2024, "venue": "bioRxiv"}))

    def test_medrxiv_2024_returns_true(self) -> None:
        self.assertTrue(cs.compute_preprint_signal({"year": 2024, "venue": "medRxiv"}))

    def test_ssrn_2024_returns_true(self) -> None:
        self.assertTrue(cs.compute_preprint_signal({"year": 2024, "venue": "SSRN"}))

    def test_research_square_2024_returns_true(self) -> None:
        self.assertTrue(
            cs.compute_preprint_signal({"year": 2024, "venue": "Research Square"})
        )

    def test_preprints_org_2024_returns_true(self) -> None:
        self.assertTrue(
            cs.compute_preprint_signal({"year": 2024, "venue": "Preprints.org"})
        )

    def test_chemrxiv_2024_returns_true(self) -> None:
        """v3.7.3 codex F6 / gemini review F6 expansion."""
        self.assertTrue(cs.compute_preprint_signal({"year": 2024, "venue": "ChemRxiv"}))

    def test_eartharxiv_2024_returns_true(self) -> None:
        self.assertTrue(
            cs.compute_preprint_signal({"year": 2024, "venue": "EarthArXiv"})
        )

    def test_osf_preprints_2024_returns_true(self) -> None:
        self.assertTrue(
            cs.compute_preprint_signal({"year": 2024, "venue": "OSF Preprints"})
        )

    def test_techrxiv_2024_returns_true(self) -> None:
        self.assertTrue(cs.compute_preprint_signal({"year": 2024, "venue": "TechRxiv"}))

    def test_non_preprint_venue_2024_returns_false(self) -> None:
        # Year passes threshold but venue is not in the closed list
        self.assertFalse(
            cs.compute_preprint_signal({"year": 2024, "venue": "Nature"})
        )

    def test_missing_venue_returns_false(self) -> None:
        # Defensive: entries lacking venue cannot satisfy the AND
        self.assertFalse(cs.compute_preprint_signal({"year": 2024}))

    def test_missing_year_returns_false(self) -> None:
        # Defensive: entries lacking year cannot satisfy the AND
        self.assertFalse(cs.compute_preprint_signal({"venue": "arXiv"}))

    def test_source_pointer_infers_arxiv(self) -> None:
        """Codex R2-1 closure: when venue is missing, source_pointer
        URLs to preprint servers must satisfy Signal 1."""
        self.assertTrue(
            cs.compute_preprint_signal(
                {"year": 2024, "source_pointer": "https://arxiv.org/abs/2401.12345"}
            )
        )

    def test_source_pointer_infers_biorxiv(self) -> None:
        self.assertTrue(
            cs.compute_preprint_signal(
                {"year": 2025, "source_pointer": "https://www.biorxiv.org/content/10.1101/2025.01.01.000000v1"}
            )
        )

    def test_source_pointer_infers_osf_preprints(self) -> None:
        self.assertTrue(
            cs.compute_preprint_signal(
                {"year": 2024, "source_pointer": "https://osf.io/preprints/socarxiv/xyz123"}
            )
        )

    def test_source_pointer_non_preprint_returns_false(self) -> None:
        """An arbitrary URL with no preprint-server hint stays False."""
        self.assertFalse(
            cs.compute_preprint_signal(
                {"year": 2024, "source_pointer": "https://nature.com/articles/x"}
            )
        )

    def test_source_pointer_ignored_when_venue_present(self) -> None:
        """Explicit `venue` field takes precedence — Nature 2024 with an
        arxiv source_pointer is still venue=Nature (Signal 1 false)."""
        self.assertFalse(
            cs.compute_preprint_signal(
                {
                    "year": 2024,
                    "venue": "Nature",
                    "source_pointer": "https://arxiv.org/abs/2401.x",
                }
            )
        )

    def test_source_pointer_pre_2024_returns_false(self) -> None:
        """Year < 2024 short-circuits before pointer inference fires."""
        self.assertFalse(
            cs.compute_preprint_signal(
                {"year": 2023, "source_pointer": "https://arxiv.org/abs/2301.x"}
            )
        )


# ============================================================================
# Signal 2 — semantic_scholar_unmatched
# ============================================================================
class SemanticScholarSignalTest(unittest.TestCase):
    """Signal 2 per v3.7.3 spec §3.2 Vector 2: SS API lookup. Returns None
    on (a) manual exemption (b) API degradation; True/False otherwise.

    The SS client is dependency-injected — tests use a MagicMock that
    returns whatever match shape the test specifies."""

    def _entry(self, **overrides):
        base = {
            "citation_key": "chen2024ai",
            "title": "Test paper",
            "authors": [{"family": "Chen", "given": "A"}],
            "year": 2024,
            "doi": "10.1234/xyz",
            "obtained_via": "folder-scan",
        }
        return base | overrides

    def test_manual_entry_returns_none(self) -> None:
        """v3.7.3 spec §3.2 + schema allOf rule #4: obtained_via='manual'
        triggers SKIP — the field MUST be omitted from the emission."""
        client = MagicMock()
        result = cs.compute_ss_unmatched_signal(
            self._entry(obtained_via="manual"), client
        )
        self.assertIsNone(result)
        # The exemption is a skip, not an API call
        client.lookup.assert_not_called()

    def test_ss_match_returns_false(self) -> None:
        client = MagicMock()
        client.lookup.return_value = {"matched": True, "paperId": "abc123"}
        self.assertFalse(cs.compute_ss_unmatched_signal(self._entry(), client))

    def test_ss_no_match_returns_true(self) -> None:
        client = MagicMock()
        client.lookup.return_value = {"matched": False, "paperId": None}
        self.assertTrue(cs.compute_ss_unmatched_signal(self._entry(), client))

    def test_ss_api_degradation_returns_none(self) -> None:
        """Per spec §3.2: API unreachable (network failure / rate-limit-
        exhausted / 5xx) returns None. Absence ≠ negative confirmation;
        setting False would imply 'checked and found'."""
        client = MagicMock()
        client.lookup.side_effect = cs.SemanticScholarUnavailable("rate limit exhausted")
        self.assertIsNone(cs.compute_ss_unmatched_signal(self._entry(), client))

    def test_ss_network_failure_returns_none(self) -> None:
        client = MagicMock()
        client.lookup.side_effect = cs.SemanticScholarUnavailable("connection refused")
        self.assertIsNone(cs.compute_ss_unmatched_signal(self._entry(), client))

    def test_unexpected_exception_propagates(self) -> None:
        """Distinguish 'API degradation' (a known-handled signal) from
        unknown bugs. ValueError isn't SS-API-degradation; let it surface
        so the migration tool can fail loudly rather than silently OMIT."""
        client = MagicMock()
        client.lookup.side_effect = ValueError("bug in client")
        with self.assertRaises(ValueError):
            cs.compute_ss_unmatched_signal(self._entry(), client)


# ============================================================================
# Emission rules — building the contamination_signals object
# ============================================================================
class EmissionRulesTest(unittest.TestCase):
    """Per spec §3.2 emission rules: emit object with both fields false
    when computed-and-clean; emit partial object when one signal can't
    be computed; omit semantic_scholar_unmatched on manual exemption."""

    def _entry(self, **overrides):
        base = {
            "year": 2024,
            "venue": "arXiv",
            "obtained_via": "folder-scan",
        }
        return base | overrides

    def test_both_signals_computed_emits_full_object(self) -> None:
        client = MagicMock()
        client.lookup.return_value = {"matched": False}
        result = cs.build_signals_object(self._entry(), client)
        self.assertEqual(
            result,
            {"preprint_post_llm_inflection": True, "semantic_scholar_unmatched": True},
        )

    def test_clean_entry_emits_both_false(self) -> None:
        client = MagicMock()
        client.lookup.return_value = {"matched": True}
        result = cs.build_signals_object(self._entry(year=2023, venue="Nature"), client)
        self.assertEqual(
            result,
            {"preprint_post_llm_inflection": False, "semantic_scholar_unmatched": False},
        )

    def test_manual_entry_omits_unmatched_field(self) -> None:
        client = MagicMock()
        result = cs.build_signals_object(
            self._entry(obtained_via="manual"), client
        )
        self.assertEqual(result, {"preprint_post_llm_inflection": True})
        self.assertNotIn("semantic_scholar_unmatched", result)

    def test_api_degradation_omits_unmatched_field(self) -> None:
        """Partial computation: Signal 1 still emits (trivial from
        year+venue), Signal 2 omitted (API down). Per spec §3.2."""
        client = MagicMock()
        client.lookup.side_effect = cs.SemanticScholarUnavailable("5xx")
        result = cs.build_signals_object(self._entry(), client)
        self.assertEqual(result, {"preprint_post_llm_inflection": True})
        self.assertNotIn("semantic_scholar_unmatched", result)


class ResetClientOutageLatchHelperTest(unittest.TestCase):
    """#115 R5-3 helper: production clients implementing the outage-latch
    pattern expose `reset_outage_latch()`; minimal mocks may not. The
    helper invokes when present, no-ops when absent. Avoids
    AttributeError for callers that swap in test mocks."""

    def test_helper_invokes_reset_when_present(self) -> None:
        client = MagicMock()
        cs.reset_client_outage_latch(client)
        client.reset_outage_latch.assert_called_once()

    def test_helper_no_ops_when_method_absent(self) -> None:
        client = MagicMock(spec=["lookup"])  # only the Protocol's lookup
        # Should NOT raise AttributeError
        cs.reset_client_outage_latch(client)


if __name__ == "__main__":
    unittest.main()


# ============================================================================
# v3.9.0 — resolve_openalex_unmatched
# ============================================================================


class ResolveOpenAlexUnmatchedTest(unittest.TestCase):
    """Tests for resolve_openalex_unmatched per spec v3.9.0 §3.4."""

    def test_match(self):
        """OpenAlex hit via DOI cross-check → False."""
        from contamination_signals import resolve_openalex_unmatched

        mock_client = MagicMock()
        mock_client.doi_lookup_with_title_check.return_value = {"title": "X"}

        entry = {
            "title": "X",
            "doi": "10.5555/abc",
            "obtained_via": "zotero-bbt-export",
        }
        result = resolve_openalex_unmatched(entry, mock_client)
        self.assertIs(result, False)

    def test_no_match(self):
        """OpenAlex no DOI hit + no title hit → True."""
        from contamination_signals import resolve_openalex_unmatched

        mock_client = MagicMock()
        mock_client.doi_lookup_with_title_check.return_value = None
        mock_client.title_search.return_value = None

        entry = {
            "title": "Nonexistent Paper",
            "doi": "10.5555/fake",
            "obtained_via": "folder-scan",
        }
        result = resolve_openalex_unmatched(entry, mock_client)
        self.assertIs(result, True)

    def test_manual_exempt(self):
        """obtained_via='manual' → return None, no client calls."""
        from contamination_signals import resolve_openalex_unmatched

        mock_client = MagicMock()
        entry = {"title": "X", "obtained_via": "manual"}
        result = resolve_openalex_unmatched(entry, mock_client)
        self.assertIsNone(result)
        mock_client.doi_lookup_with_title_check.assert_not_called()
        mock_client.title_search.assert_not_called()

    def test_doi_absent_falls_through_to_title(self):
        """DOI absent: title search alone, NO DOI lookup attempted."""
        from contamination_signals import resolve_openalex_unmatched

        mock_client = MagicMock()
        mock_client.title_search.return_value = {"title": "X"}

        entry = {"title": "X", "obtained_via": "zotero-bbt-export"}  # no doi
        result = resolve_openalex_unmatched(entry, mock_client)
        self.assertIs(result, False)
        mock_client.doi_lookup_with_title_check.assert_not_called()

    def test_api_down_raises(self):
        """API degraded → re-raise OpenAlexUnavailable for caller to omit field."""
        from contamination_signals import resolve_openalex_unmatched
        from openalex_client import OpenAlexUnavailable

        mock_client = MagicMock()
        mock_client.doi_lookup_with_title_check.side_effect = OpenAlexUnavailable("down")

        entry = {"title": "X", "doi": "10.5555/abc", "obtained_via": "folder-scan"}
        with self.assertRaises(OpenAlexUnavailable):
            resolve_openalex_unmatched(entry, mock_client)


# ============================================================================
# v3.9.0 — resolve_crossref_unmatched
# ============================================================================


class ResolveCrossrefUnmatchedTest(unittest.TestCase):
    """Tests for resolve_crossref_unmatched per spec v3.9.0 §3.5."""

    def test_match(self):
        """Crossref hit via DOI cross-check → False."""
        from contamination_signals import resolve_crossref_unmatched

        mock_client = MagicMock()
        mock_client.doi_lookup_with_title_check.return_value = {"title": ["X"]}

        entry = {
            "title": "X",
            "doi": "10.5555/abc",
            "obtained_via": "zotero-bbt-export",
        }
        result = resolve_crossref_unmatched(entry, mock_client)
        self.assertIs(result, False)

    def test_no_match(self):
        """Crossref no DOI hit + no title hit → True."""
        from contamination_signals import resolve_crossref_unmatched

        mock_client = MagicMock()
        mock_client.doi_lookup_with_title_check.return_value = None
        mock_client.title_search.return_value = None

        entry = {
            "title": "Nonexistent",
            "doi": "10.5555/fake",
            "obtained_via": "folder-scan",
        }
        result = resolve_crossref_unmatched(entry, mock_client)
        self.assertIs(result, True)

    def test_manual_exempt(self):
        """obtained_via='manual' → return None, no client calls."""
        from contamination_signals import resolve_crossref_unmatched

        mock_client = MagicMock()
        entry = {"title": "X", "obtained_via": "manual"}
        result = resolve_crossref_unmatched(entry, mock_client)
        self.assertIsNone(result)
        mock_client.doi_lookup_with_title_check.assert_not_called()
        mock_client.title_search.assert_not_called()

    def test_doi_absent_falls_through_to_title(self):
        """DOI absent: title search alone, NO DOI lookup attempted."""
        from contamination_signals import resolve_crossref_unmatched

        mock_client = MagicMock()
        mock_client.title_search.return_value = {"title": ["X"]}

        entry = {"title": "X", "obtained_via": "obsidian-vault"}  # no doi
        result = resolve_crossref_unmatched(entry, mock_client)
        self.assertIs(result, False)
        mock_client.doi_lookup_with_title_check.assert_not_called()

    def test_api_down_raises(self):
        """API degraded → re-raise CrossrefUnavailable for caller to omit field."""
        from contamination_signals import resolve_crossref_unmatched
        from crossref_client import CrossrefUnavailable

        mock_client = MagicMock()
        mock_client.doi_lookup_with_title_check.side_effect = CrossrefUnavailable("down")

        entry = {"title": "X", "doi": "10.5555/abc", "obtained_via": "folder-scan"}
        with self.assertRaises(CrossrefUnavailable):
            resolve_crossref_unmatched(entry, mock_client)


# ============================================================================
# v3.11 #182 Delta 1 — resolve_arxiv_unmatched
# ============================================================================


class ResolveArxivUnmatchedTest(unittest.TestCase):
    """Tests for resolve_arxiv_unmatched per spec v3.11 #182 Delta 1.

    Differs from the crossref/openalex resolvers: keyed by entry['arxiv_id']
    (not 'doi'), and the client exact-key method is arxiv_id_lookup, not
    doi_lookup_with_title_check."""

    def test_match(self):
        """arXiv hit via ID cross-check → False."""
        from contamination_signals import resolve_arxiv_unmatched

        mock_client = MagicMock()
        mock_client.arxiv_id_lookup.return_value = {"title": "X", "year": 2017}

        entry = {
            "title": "X",
            "arxiv_id": "1706.03762",
            "obtained_via": "zotero-bbt-export",
        }
        result = resolve_arxiv_unmatched(entry, mock_client)
        self.assertIs(result, False)

    def test_no_match(self):
        """arXiv no ID hit + no title hit → True."""
        from contamination_signals import resolve_arxiv_unmatched

        mock_client = MagicMock()
        mock_client.arxiv_id_lookup.return_value = None
        mock_client.title_search.return_value = None

        entry = {
            "title": "Nonexistent",
            "arxiv_id": "9999.99999",
            "obtained_via": "folder-scan",
        }
        result = resolve_arxiv_unmatched(entry, mock_client)
        self.assertIs(result, True)

    def test_manual_exempt(self):
        """obtained_via='manual' → return None, no client calls."""
        from contamination_signals import resolve_arxiv_unmatched

        mock_client = MagicMock()
        entry = {"title": "X", "arxiv_id": "1706.03762", "obtained_via": "manual"}
        result = resolve_arxiv_unmatched(entry, mock_client)
        self.assertIsNone(result)
        mock_client.arxiv_id_lookup.assert_not_called()
        mock_client.title_search.assert_not_called()

    def test_arxiv_id_absent_skips_resolver(self):
        """arXiv ID absent (#331 P2): the arXiv resolver is SKIPPED — return None
        (caller omits arxiv_unmatched) and run NO network query. A non-arXiv
        citation (e.g. a DOI-keyed journal article) must not be title-searched
        against arXiv: a title miss there is a coverage gap, not non-existence
        evidence, and would emit a false arxiv_unmatched=true (inflating the
        triangulation k on a clean citation). Spec §4 / the orchestrator k_max
        rule both state arxiv_unmatched is ABSENT on citations with no arXiv ID
        ('arXiv resolver skipped on a non-arXiv citation per Delta 1')."""
        from contamination_signals import resolve_arxiv_unmatched

        mock_client = MagicMock()

        entry = {"title": "X", "obtained_via": "obsidian-vault"}  # no arxiv_id
        result = resolve_arxiv_unmatched(entry, mock_client)
        self.assertIsNone(result)
        mock_client.arxiv_id_lookup.assert_not_called()
        mock_client.title_search.assert_not_called()

    def test_arxiv_id_miss_falls_through_to_title(self):
        """ID present but ID lookup misses → fall through to title search."""
        from contamination_signals import resolve_arxiv_unmatched

        mock_client = MagicMock()
        mock_client.arxiv_id_lookup.return_value = None
        mock_client.title_search.return_value = {"title": "X", "year": 2017}

        entry = {"title": "X", "arxiv_id": "1706.03762", "obtained_via": "folder-scan"}
        result = resolve_arxiv_unmatched(entry, mock_client)
        self.assertIs(result, False)
        mock_client.title_search.assert_called_once()

    def test_api_down_raises(self):
        """API degraded → re-raise ArxivUnavailable for caller to omit field."""
        from contamination_signals import resolve_arxiv_unmatched
        from arxiv_client import ArxivUnavailable

        mock_client = MagicMock()
        mock_client.arxiv_id_lookup.side_effect = ArxivUnavailable("down")

        entry = {"title": "X", "arxiv_id": "1706.03762", "obtained_via": "folder-scan"}
        with self.assertRaises(ArxivUnavailable):
            resolve_arxiv_unmatched(entry, mock_client)


# ============================================================================
# v3.11 #182 Delta 1 — build_signals_object arxiv extension
# ============================================================================


class BuildSignalsArxivExtensionTest(unittest.TestCase):
    """build_signals_object grows an optional arxiv_client keyword arg; when
    omitted, behavior is byte-equivalent to the v3.7.3 caller (no arxiv field).
    Per spec §2 Delta 1 'signal computation only' scope."""

    def _entry(self, **overrides):
        base = {"year": 2024, "venue": "arXiv", "obtained_via": "folder-scan"}
        return base | overrides

    def test_no_arxiv_client_omits_arxiv_field(self) -> None:
        """Byte-equivalent v3.7.3 path: no arxiv_client → no arxiv_unmatched."""
        ss = MagicMock()
        ss.lookup.return_value = {"matched": True}
        result = cs.build_signals_object(self._entry(), ss)
        self.assertNotIn("arxiv_unmatched", result)

    def test_arxiv_client_emits_arxiv_field(self) -> None:
        """With arxiv_client, a non-manual entry emits arxiv_unmatched."""
        ss = MagicMock()
        ss.lookup.return_value = {"matched": True}
        ax = MagicMock()
        ax.arxiv_id_lookup.return_value = None
        ax.title_search.return_value = None
        result = cs.build_signals_object(
            self._entry(arxiv_id="9999.99999"), ss, arxiv_client=ax
        )
        self.assertIs(result["arxiv_unmatched"], True)

    def test_no_arxiv_id_omits_arxiv_field_even_with_client(self) -> None:
        """#331: a non-arXiv citation (arxiv_client present but entry has no
        arxiv_id) omits arxiv_unmatched and runs NO arXiv query. Without the
        skip, the resolver would title-search arXiv and emit a false
        arxiv_unmatched=true, inflating triangulation k on a clean citation."""
        ss = MagicMock()
        ss.lookup.return_value = {"matched": True}
        ax = MagicMock()
        result = cs.build_signals_object(
            self._entry(), ss, arxiv_client=ax  # _entry() carries no arxiv_id
        )
        self.assertNotIn("arxiv_unmatched", result)
        ax.arxiv_id_lookup.assert_not_called()
        ax.title_search.assert_not_called()

    def test_manual_entry_omits_arxiv_field_even_with_client(self) -> None:
        """Manual entry: arxiv_unmatched omitted (not-rule), like the ss field."""
        ss = MagicMock()
        ax = MagicMock()
        result = cs.build_signals_object(
            self._entry(obtained_via="manual", arxiv_id="1706.03762"), ss,
            arxiv_client=ax
        )
        self.assertNotIn("arxiv_unmatched", result)
        ax.arxiv_id_lookup.assert_not_called()

    def test_arxiv_api_down_omits_arxiv_field(self) -> None:
        """arXiv API degradation → omit arxiv_unmatched (absent != false)."""
        ss = MagicMock()
        ss.lookup.return_value = {"matched": True}
        ax = MagicMock()
        ax.arxiv_id_lookup.side_effect = cs.ArxivUnavailable("5xx")
        result = cs.build_signals_object(
            self._entry(arxiv_id="1706.03762"), ss, arxiv_client=ax
        )
        self.assertNotIn("arxiv_unmatched", result)


# ============================================================================
# v3.11 #182 Delta 2 — resolver cache integration (wrapper layer)
# ============================================================================


class _FakeCache:
    """Minimal in-memory stand-in for VerificationCache. Records get/put calls
    so tests can assert hit/skip behavior without SQLite."""

    def __init__(self, seed=None):
        self._store = dict(seed or {})
        self.get_calls = []
        self.put_calls = []

    def get(self, citation_key, resolver_name, query_form):
        self.get_calls.append((citation_key, resolver_name, query_form))
        return self._store.get((citation_key, resolver_name, query_form))

    def put(self, citation_key, resolver_name, query_form, response):
        self.put_calls.append((citation_key, resolver_name, query_form, response))
        self._store[(citation_key, resolver_name, query_form)] = response


class ResolveCrossrefCacheTest(unittest.TestCase):
    """Cache integration is byte-equivalent when cache=None, consults the cache
    before the network on hit, and populates on miss. Per spec §2 Delta 2."""

    def _entry(self, **overrides):
        base = {
            "citation_key": "vaswani2017",
            "title": "Attention Is All You Need",
            "doi": "10.5555/abc",
            "obtained_via": "folder-scan",
        }
        return base | overrides

    def test_cache_none_is_byte_equivalent(self):
        from contamination_signals import resolve_crossref_unmatched

        client = MagicMock()
        client.doi_lookup_with_title_check.return_value = {"title": ["X"]}
        result = resolve_crossref_unmatched(self._entry(), client, cache=None)
        self.assertIs(result, False)
        client.doi_lookup_with_title_check.assert_called_once()

    def test_cache_hit_skips_network(self):
        from contamination_signals import resolve_crossref_unmatched

        client = MagicMock()
        qf = "doi:10.5555/abc|title:Attention Is All You Need"
        # A same-decision-version row IS reused (#431 §0.12.3b).
        cache = _FakeCache(seed={
            ("vaswani2017", "crossref", qf): {
                "matched": True, "matched_by": "doi",
                "decision_version": cs.RESOLVER_DECISION_VERSION,
            }
        })
        result = resolve_crossref_unmatched(self._entry(), client, cache=cache)
        self.assertIs(result, False)  # matched=True → unmatched=False
        client.doi_lookup_with_title_check.assert_not_called()
        client.title_search.assert_not_called()

    def test_stale_pre_v5_row_forces_recompute(self):
        """#431 §0.12.3b (ship blocker): a pre-v5 row written under the
        author-agree logic (matched_by=title, NO decision_version) must be
        treated as a MISS so the v5 candidate loop actually runs — without this
        the pivot is a no-op for up to 90 days of cached `matched` rows. The
        stale row says matched=True; under v5 the DOI misses and the title
        fallback (non-exact) returns no match → unmatched=True, and the live
        client methods ARE called."""
        from contamination_signals import resolve_crossref_unmatched

        client = MagicMock()
        client.doi_lookup_with_title_check.return_value = None  # DOI miss
        client.title_search.return_value = None  # v5: non-exact → no match
        qf = "doi:10.5555/abc|title:Attention Is All You Need"
        cache = _FakeCache(seed={
            ("vaswani2017", "crossref", qf): {
                "matched": True, "matched_by": "title",  # stale, no version
            }
        })
        result = resolve_crossref_unmatched(self._entry(), client, cache=cache)
        self.assertIs(result, True)  # recomputed unmatched, NOT stale matched
        client.title_search.assert_called_once()  # v5 loop ran
        # The recomputed verdict is re-stored WITH the current version.
        _, _, _, response = cache.put_calls[0]
        self.assertEqual(
            response["decision_version"], cs.RESOLVER_DECISION_VERSION
        )

    def test_cache_miss_calls_network_and_populates(self):
        from contamination_signals import resolve_crossref_unmatched

        client = MagicMock()
        client.doi_lookup_with_title_check.return_value = None
        client.title_search.return_value = None  # unmatched
        cache = _FakeCache()
        result = resolve_crossref_unmatched(self._entry(), client, cache=cache)
        self.assertIs(result, True)  # unmatched
        self.assertEqual(len(cache.put_calls), 1)
        # The negative verdict is cached (so repeat runs don't re-hammer API).
        _, resolver, qf, response = cache.put_calls[0]
        self.assertEqual(resolver, "crossref")
        self.assertIs(response["matched"], False)

    def test_malformed_cache_payload_treated_as_miss(self):
        """A persistent on-disk cache row written by an older/other tool that
        lacks the 'matched' key must be treated as a MISS (force live recompute),
        not crash with KeyError for 90 days. Robustness guard."""
        from contamination_signals import resolve_crossref_unmatched

        client = MagicMock()
        client.doi_lookup_with_title_check.return_value = {"title": ["X"]}  # match
        qf = "doi:10.5555/abc|title:Attention Is All You Need"
        cache = _FakeCache(seed={
            ("vaswani2017", "crossref", qf): {"legacy": "no matched key"}
        })
        result = resolve_crossref_unmatched(self._entry(), client, cache=cache)
        # Falls through to live call (which matched) → unmatched=False.
        self.assertIs(result, False)
        client.doi_lookup_with_title_check.assert_called_once()

    def test_degradation_is_not_cached(self):
        from contamination_signals import resolve_crossref_unmatched
        from crossref_client import CrossrefUnavailable

        client = MagicMock()
        client.doi_lookup_with_title_check.side_effect = CrossrefUnavailable("down")
        cache = _FakeCache()
        with self.assertRaises(CrossrefUnavailable):
            resolve_crossref_unmatched(self._entry(), client, cache=cache)
        self.assertEqual(cache.put_calls, [])  # NEVER cache a degradation

    def test_manual_entry_does_not_touch_cache(self):
        from contamination_signals import resolve_crossref_unmatched

        client = MagicMock()
        cache = _FakeCache()
        result = resolve_crossref_unmatched(
            self._entry(obtained_via="manual"), client, cache=cache
        )
        self.assertIsNone(result)
        self.assertEqual(cache.get_calls, [])
        self.assertEqual(cache.put_calls, [])


class ResolveArxivCacheTest(unittest.TestCase):
    """Same cache contract for the arXiv resolver (ID-keyed query_form)."""

    def _entry(self, **overrides):
        base = {
            "citation_key": "vaswani2017",
            "title": "Attention Is All You Need",
            "arxiv_id": "1706.03762",
            "obtained_via": "folder-scan",
        }
        return base | overrides

    def test_cache_hit_skips_network(self):
        from contamination_signals import resolve_arxiv_unmatched

        client = MagicMock()
        qf = "arxiv:1706.03762|title:Attention Is All You Need"
        cache = _FakeCache(seed={
            ("vaswani2017", "arxiv", qf): {
                "matched": False, "matched_by": None,
                "decision_version": cs.RESOLVER_DECISION_VERSION,
            }
        })
        result = resolve_arxiv_unmatched(self._entry(), client, cache=cache)
        self.assertIs(result, True)  # matched=False → unmatched=True
        client.arxiv_id_lookup.assert_not_called()

    def test_stale_pre_v5_row_forces_recompute(self):
        """#431 §0.12.3b: a pre-v5 arXiv row with no decision_version is a MISS;
        the ID lookup runs live under v5."""
        from contamination_signals import resolve_arxiv_unmatched

        client = MagicMock()
        client.arxiv_id_lookup.return_value = None  # ID miss
        client.title_search.return_value = None  # v5: non-exact → no match
        qf = "arxiv:1706.03762|title:Attention Is All You Need"
        cache = _FakeCache(seed={
            ("vaswani2017", "arxiv", qf): {
                "matched": True, "matched_by": "title",  # stale, no version
            }
        })
        result = resolve_arxiv_unmatched(self._entry(), client, cache=cache)
        self.assertIs(result, True)  # recomputed, NOT stale matched
        client.arxiv_id_lookup.assert_called_once()

    def test_cache_miss_populates(self):
        from contamination_signals import resolve_arxiv_unmatched

        client = MagicMock()
        client.arxiv_id_lookup.return_value = {"title": "X", "year": 2017}
        cache = _FakeCache()
        result = resolve_arxiv_unmatched(self._entry(), client, cache=cache)
        self.assertIs(result, False)  # matched
        self.assertEqual(len(cache.put_calls), 1)
        _, resolver, _, response = cache.put_calls[0]
        self.assertEqual(resolver, "arxiv")
        self.assertIs(response["matched"], True)


class SemanticScholarCacheTest(unittest.TestCase):
    """S2's wrapper is compute_ss_unmatched_signal (the lone client.lookup is
    entry-keyed already). Cache integration lives at that wrapper, matching
    Option A — the resolver_name is 'semantic_scholar'. Per spec §2 Delta 2
    'the S2 lookup'."""

    def _entry(self, **overrides):
        base = {
            "citation_key": "chen2024ai",
            "title": "Test paper",
            "doi": "10.1234/xyz",
            "obtained_via": "folder-scan",
        }
        return base | overrides

    def test_cache_none_byte_equivalent(self):
        client = MagicMock()
        client.lookup.return_value = {"matched": True}
        self.assertFalse(cs.compute_ss_unmatched_signal(self._entry(), client, cache=None))
        client.lookup.assert_called_once()

    def test_cache_hit_skips_lookup(self):
        client = MagicMock()
        qf = "doi:10.1234/xyz|title:Test paper"
        cache = _FakeCache(seed={
            ("chen2024ai", "semantic_scholar", qf): {
                "matched": False, "matched_by": None,
                "decision_version": cs.RESOLVER_DECISION_VERSION,
            }
        })
        result = cs.compute_ss_unmatched_signal(self._entry(), client, cache=cache)
        self.assertTrue(result)  # matched=False → unmatched=True
        client.lookup.assert_not_called()

    def test_stale_pre_v5_row_forces_recompute(self):
        """#431 §0.12.3b (ship blocker), the exact regression the spec names: a
        stale `{matched: True, matched_by: title}` row with no decision_version
        (written under v3/v4 author-agree, e.g. a Study 1 / Study 2 same-author
        pair) MUST be a miss so client.lookup runs under v5 — not returned as a
        stale `matched`."""
        client = MagicMock()
        client.lookup.return_value = {"matched": False}  # v5 live verdict
        qf = "doi:10.1234/xyz|title:Test paper"
        cache = _FakeCache(seed={
            ("chen2024ai", "semantic_scholar", qf): {
                "matched": True, "matched_by": "title",  # stale, no version
            }
        })
        result = cs.compute_ss_unmatched_signal(self._entry(), client, cache=cache)
        self.assertTrue(result)  # recomputed unmatched=True, NOT stale matched
        client.lookup.assert_called_once()  # v5 loop ran

    def test_cache_miss_populates(self):
        client = MagicMock()
        client.lookup.return_value = {"matched": True}
        cache = _FakeCache()
        result = cs.compute_ss_unmatched_signal(self._entry(), client, cache=cache)
        self.assertFalse(result)
        self.assertEqual(len(cache.put_calls), 1)
        _, resolver, _, response = cache.put_calls[0]
        self.assertEqual(resolver, "semantic_scholar")
        self.assertIs(response["matched"], True)

    def test_manual_does_not_touch_cache(self):
        client = MagicMock()
        cache = _FakeCache()
        result = cs.compute_ss_unmatched_signal(
            self._entry(obtained_via="manual"), client, cache=cache
        )
        self.assertIsNone(result)
        self.assertEqual(cache.get_calls, [])
        self.assertEqual(cache.put_calls, [])

    def test_degradation_not_cached(self):
        client = MagicMock()
        client.lookup.side_effect = cs.SemanticScholarUnavailable("5xx")
        cache = _FakeCache()
        result = cs.compute_ss_unmatched_signal(self._entry(), client, cache=cache)
        self.assertIsNone(result)  # degradation → None (omit field)
        self.assertEqual(cache.put_calls, [])  # never cache degradation


# ============================================================================
# v3.11 #182 Delta 4 — queried_by retrofit (the ID-keyed-unmatched signal that
# the narrowed-false reducer C-V6(a) needs). The internal resolver-flow helpers
# return (unmatched, matched_by, queried_by) where queried_by records what the
# resolver ACTUALLY queried by, so a title-only unmatched is distinguishable
# from an ID-keyed unmatched at reduce time.
# ============================================================================


class ResolveDoiThenTitleQueriedByTest(unittest.TestCase):
    """_resolve_doi_then_title now returns (unmatched, matched_by, queried_by).
    queried_by ∈ {'id', 'title'} for unmatched; mirrors matched_by for matched."""

    def test_doi_match_queried_by_id(self):
        client = MagicMock()
        client.doi_lookup_with_title_check.return_value = {"title": ["X"]}
        unmatched, matched_by, queried_by = cs._resolve_doi_then_title(
            {"title": "X", "doi": "10.5/x"}, client
        )
        self.assertIs(unmatched, False)
        self.assertEqual(matched_by, "doi")
        self.assertEqual(queried_by, "id")

    def test_doi_present_but_unmatched_queried_by_id(self):
        """DOI present, ID lookup miss, title miss → unmatched, queried_by='id'
        (an ID lookup WAS attempted — this is ID-keyed unmatched, C-V6(a))."""
        client = MagicMock()
        client.doi_lookup_with_title_check.return_value = None
        client.title_search.return_value = None
        unmatched, matched_by, queried_by = cs._resolve_doi_then_title(
            {"title": "Ghost", "doi": "10.5/fake"}, client
        )
        self.assertIs(unmatched, True)
        self.assertIsNone(matched_by)
        self.assertEqual(queried_by, "id")

    def test_no_doi_unmatched_queried_by_title(self):
        """No DOI to key on → title-only search → unmatched, queried_by='title'
        (NOT id-keyed — coverage gap, must reduce to unresolvable not false)."""
        client = MagicMock()
        client.title_search.return_value = None
        unmatched, matched_by, queried_by = cs._resolve_doi_then_title(
            {"title": "Unindexed regional paper"}, client  # no doi
        )
        self.assertIs(unmatched, True)
        self.assertIsNone(matched_by)
        self.assertEqual(queried_by, "title")

    def test_no_doi_title_match_queried_by_title(self):
        client = MagicMock()
        client.title_search.return_value = {"title": ["X"]}
        unmatched, matched_by, queried_by = cs._resolve_doi_then_title(
            {"title": "X"}, client  # no doi
        )
        self.assertIs(unmatched, False)
        self.assertEqual(matched_by, "title")
        self.assertEqual(queried_by, "title")


class ResolveArxivQueriedByTest(unittest.TestCase):
    """_resolve_arxiv_id_then_title queried_by uses arxiv_id presence."""

    def test_arxiv_id_present_unmatched_queried_by_id(self):
        client = MagicMock()
        client.arxiv_id_lookup.return_value = None
        client.title_search.return_value = None
        unmatched, matched_by, queried_by = cs._resolve_arxiv_id_then_title(
            {"title": "Ghost", "arxiv_id": "9999.99999"}, client
        )
        self.assertIs(unmatched, True)
        self.assertEqual(queried_by, "id")

    # (#331) No test for the no-arxiv_id case here: _resolve_arxiv_id_then_title's
    # precondition is now "entry has an arxiv_id" — both callers
    # (resolve_arxiv_unmatched and verification_gate._run_arxiv) skip the resolver
    # before reaching it when arxiv_id is absent. The skip is covered by
    # ResolveArxivUnmatchedTest.test_arxiv_id_absent_skips_resolver and the
    # verification_gate skipped-status tests.

    def test_arxiv_id_match_queried_by_id(self):
        client = MagicMock()
        client.arxiv_id_lookup.return_value = {"title": "X", "year": 2017}
        unmatched, matched_by, queried_by = cs._resolve_arxiv_id_then_title(
            {"title": "X", "arxiv_id": "1706.03762"}, client
        )
        self.assertIs(unmatched, False)
        self.assertEqual(matched_by, "arxiv")
        self.assertEqual(queried_by, "id")
