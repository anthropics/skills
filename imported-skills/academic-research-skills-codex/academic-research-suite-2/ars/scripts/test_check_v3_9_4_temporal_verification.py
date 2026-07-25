"""Tests for v3.9.4 temporal verification spec lint + schema conformance.

Per docs/design/2026-05-18-ars-v3.9.4-temporal-verification-spec.md §7.
"""
from __future__ import annotations

import json
from pathlib import Path

import jsonschema
import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = REPO_ROOT / "shared/contracts/passport"


def _load_schema(name: str) -> dict:
    return json.loads((SCHEMAS / name).read_text())


def test_timeline_schema_validates_canonical_example():
    schema = _load_schema("timeline.schema.json")
    example = {
        "schema_version": "1.0",
        "sources": [
            {
                "citation_key": "handbook-2024ed",
                "type": "institutional-document",
                "published_date": {
                    "value": "2024-09-15",
                    "precision": "day",
                    "open_ended": False,
                    "provenance": {
                        "method": "crossref_lookup",
                        "raw": "2024-09-15",
                        "source_locator": "doi:10.xxxx/handbook-2024",
                        "confidence": "high",
                    },
                },
                "effective_date_range": {
                    "start": {
                        "value": "2024-10-01",
                        "precision": "day",
                        "open_ended": False,
                        "provenance": {
                            "method": "pdftotext_cover",
                            "raw": "Effective from October 1, 2024",
                            "source_locator": "file:///path/handbook-2024.pdf:p3",
                            "confidence": "high",
                        },
                    },
                    "end": {
                        "value": None,
                        "precision": "unknown",
                        "open_ended": True,
                        "provenance": {
                            "method": "user_override",
                            "confidence": "high",
                        },
                    },
                },
                "supersedes": "handbook-2020ed",
                "superseded_by": None,
                "version_family_id": "handbook-family",
                "version_catalog_completeness": "partial",
            }
        ],
        "events": [
            {
                "event_id": "programme-X-cycle-2022",
                "description": "Programme X review cycle 2022",
                "date": {
                    "value": "2022-04-01..2022-12-31",
                    "precision": "interval",
                    "open_ended": False,
                    "provenance": {
                        "method": "user_override",
                        "confidence": "high",
                    },
                },
                "governed_by": "handbook-2020ed",
            }
        ],
    }
    jsonschema.validate(example, schema)


def test_timeline_open_ended_only_on_end():
    """open_ended:true on start date should be a schema violation per spec §3.1 date shape table."""
    schema = _load_schema("timeline.schema.json")
    bad = {
        "schema_version": "1.0",
        "sources": [
            {
                "citation_key": "x",
                "type": "doc",
                "effective_date_range": {
                    "start": {
                        "value": None,
                        "precision": "unknown",
                        "open_ended": True,
                        "provenance": {"method": "unknown", "confidence": "unverified"},
                    },
                    "end": {
                        "value": "2024-12-31",
                        "precision": "day",
                        "open_ended": False,
                        "provenance": {"method": "crossref_lookup", "confidence": "high"},
                    },
                },
            }
        ],
    }
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, schema)


def test_citation_provenance_schema_validates_canonical_example():
    schema = _load_schema("citation_provenance.schema.json")
    example = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "entries": [
            {
                "citation_key": "handbook-2024ed",
                "crossref_issued": {
                    "value": "2024-09-15",
                    "precision": "day",
                    "verified_at": "2026-05-18T12:34:56Z",
                    "api_endpoint": "https://api.crossref.org/works/10.xxxx/handbook-2024",
                },
                "pdftotext_cover_first_line": {
                    "line": "Quality Assurance Handbook, 2024 Edition",
                    "published_date_candidate": {
                        "value": "2024",
                        "precision": "year",
                    },
                    "verified_at": "2026-05-18T12:34:56Z",
                    "pdf_path": "/path/handbook-2024.pdf",
                },
                "verification_method": "crossref_and_pdftotext",
                "confidence": "high",
                "notes": None,
            }
        ],
    }
    jsonschema.validate(example, schema)


def test_citation_provenance_high_requires_both_sources():
    """confidence:high MUST have both crossref_issued and pdftotext_cover_first_line populated (per spec §3.4 agreement table row 1)."""
    schema = _load_schema("citation_provenance.schema.json")
    bad = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "entries": [
            {
                "citation_key": "x",
                "crossref_issued": None,
                "pdftotext_cover_first_line": None,
                "verification_method": "crossref_and_pdftotext",
                "confidence": "high",
                "notes": None,
            }
        ],
    }
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, schema)


def test_citation_provenance_high_rejects_absent_sources():
    """v3.9.4.1 hotfix: confidence:high MUST also reject entries that OMIT crossref_issued
    and pdftotext_cover_first_line entirely. The v3.9.4 allOf used `then.properties` only,
    which does not fire when the property is absent — so an entry with confidence:high and
    no source fields silently passed validation. v3.9.4.1 adds `then.required` to enforce presence."""
    schema = _load_schema("citation_provenance.schema.json")
    bad = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "entries": [
            {
                "citation_key": "x",
                # Both crossref_issued AND pdftotext_cover_first_line absent.
                "verification_method": "crossref_and_pdftotext",
                "confidence": "high",
                "notes": None,
            }
        ],
    }
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, schema)


@pytest.mark.parametrize("finding_kind,mode,severity,bound_refs,bound_event,bound_dates,matched_span", [
    ("TEMPORAL-ARITHMETIC-IMPOSSIBLE", 1, "HIGH", [], None,
     {"left": {"role": "anchor", "value": "2025-03", "source": "draft_capture", "ref_slug": None},
      "right": {"role": "event", "value": "2025-06", "source": "draft_capture", "ref_slug": None}},
     None),
    ("TEMPORAL-ANACHRONISTIC-CITATION", 2, "HIGH",
     [{"ref_slug": "h2026", "timeline_entry": "h2026"}],
     {"event_id": "e2022", "date": "2022-04-01..2022-12-31"}, None, None),
    ("TEMPORAL-COMPARATOR-UNMATERIALIZED", 3, "MEDIUM",
     [{"ref_slug": "s2020", "timeline_entry": "s2020"}], None, None,
     {"text": "1998 edition", "char_start": 100, "char_end": 112}),
    ("TEMPORAL-CAUSAL-INVERSION", 4, "MEDIUM",
     [{"ref_slug": "a", "timeline_entry": "a"}, {"ref_slug": "b", "timeline_entry": "b"}],
     None,
     {"left": {"role": "left_arg", "value": "2026-03-01", "source": "timeline_ref", "ref_slug": "a"},
      "right": {"role": "right_arg", "value": "2020-05-15", "source": "timeline_ref", "ref_slug": "b"}},
     {"text": "A enabled B", "char_start": 0, "char_end": 11}),
    ("TEMPORAL-DEICTIC", 5, "LOW", [], None, None,
     {"text": "currently", "char_start": 0, "char_end": 9}),
    ("TEMPORAL-METADATA-MISSING", None, "LOW", [], None, None, None),
])
def test_temporal_audit_schema_accepts_6_finding_kinds(finding_kind, mode, severity, bound_refs, bound_event, bound_dates, matched_span):
    schema = _load_schema("temporal_audit_results.schema.json")
    example = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18",
        "findings": [
            {
                "finding_id": "TF-001",
                "finding_kind": finding_kind,
                "severity": severity,
                "mode": mode,
                "block_eligible": False,
                "draft_locator": {"file": "phase4_composition/draft.md", "line": 1, "sentence": "x"},
                "matched_span": matched_span,
                "bound_refs": bound_refs,
                "bound_event": bound_event,
                "bound_dates": bound_dates,
                "rationale": "r",
                "suggested_fix": None,
            }
        ],
    }
    jsonschema.validate(example, schema)


def test_temporal_audit_p2_requires_bound_event():
    """P2 anachronism MUST have bound_event non-null per spec §3.2 per-kind map."""
    schema = _load_schema("temporal_audit_results.schema.json")
    bad = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18",
        "findings": [
            {
                "finding_id": "TF-001",
                "finding_kind": "TEMPORAL-ANACHRONISTIC-CITATION",
                "severity": "HIGH",
                "mode": 2,
                "block_eligible": True,
                "draft_locator": {"file": "x", "line": 1, "sentence": "x"},
                "matched_span": None,
                "bound_refs": [{"ref_slug": "x", "timeline_entry": "x"}],
                "bound_event": None,  # invalid for P2
                "bound_dates": None,
                "rationale": "r",
                "suggested_fix": None,
            }
        ],
    }
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, schema)


def test_temporal_audit_p1_requires_bound_dates():
    """P1 arithmetic MUST have bound_dates non-null."""
    schema = _load_schema("temporal_audit_results.schema.json")
    bad = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18",
        "findings": [
            {
                "finding_id": "TF-001",
                "finding_kind": "TEMPORAL-ARITHMETIC-IMPOSSIBLE",
                "severity": "HIGH",
                "mode": 1,
                "block_eligible": True,
                "draft_locator": {"file": "x", "line": 1, "sentence": "x"},
                "matched_span": None,
                "bound_refs": [],
                "bound_event": None,
                "bound_dates": None,  # invalid for P1
                "rationale": "r",
                "suggested_fix": None,
            }
        ],
    }
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(bad, schema)


import subprocess
import sys as _sys

SCRIPT = REPO_ROOT / "scripts/check_v3_9_4_temporal_verification.py"


def test_lint_exits_zero_on_clean_fixture(tmp_path):
    """Lint should exit 0 when validating valid sample fixtures."""
    timeline = tmp_path / "timeline.yaml"
    timeline.write_text(yaml.safe_dump({
        "schema_version": "1.0",
        "sources": [],
        "events": [],
    }))
    provenance = tmp_path / "citation_provenance.yaml"
    provenance.write_text(yaml.safe_dump({
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "entries": [],
    }))
    audit = tmp_path / "temporal_audit_results.yaml"
    audit.write_text(yaml.safe_dump({
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18",
        "findings": [],
    }))

    result = subprocess.run(
        [_sys.executable, str(SCRIPT),
         "--timeline", str(timeline),
         "--citation-provenance", str(provenance),
         "--temporal-audit", str(audit)],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"stdout={result.stdout!r} stderr={result.stderr!r}"


def test_lint_detects_supersession_cycle(tmp_path):
    """Invariant 2 — supersession chain must have no cycles."""
    timeline = tmp_path / "timeline.yaml"
    timeline.write_text(yaml.safe_dump({
        "schema_version": "1.0",
        "sources": [
            {"citation_key": "a", "type": "doc", "supersedes": "b", "superseded_by": None},
            {"citation_key": "b", "type": "doc", "supersedes": "a", "superseded_by": None},
        ],
        "events": [],
    }))
    provenance = tmp_path / "citation_provenance.yaml"
    provenance.write_text(yaml.safe_dump({
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "entries": [],
    }))
    audit = tmp_path / "temporal_audit_results.yaml"
    audit.write_text(yaml.safe_dump({
        "schema_version": "1.0",
        "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18",
        "findings": [],
    }))

    result = subprocess.run(
        [_sys.executable, str(SCRIPT),
         "--timeline", str(timeline),
         "--citation-provenance", str(provenance),
         "--temporal-audit", str(audit)],
        capture_output=True, text=True,
    )
    assert result.returncode == 1, f"expected exit 1 for cycle, got {result.returncode}; stderr={result.stderr!r}"
    assert "cycle" in result.stderr.lower(), f"expected 'cycle' in stderr, got: {result.stderr!r}"


def test_lint_bibliography_agent_unchanged(tmp_path):
    """F2 invariant: bibliography_agent.md unmodified passes the lint."""
    timeline = tmp_path / "timeline.yaml"
    timeline.write_text(yaml.safe_dump({"schema_version": "1.0", "sources": [], "events": []}))
    provenance = tmp_path / "citation_provenance.yaml"
    provenance.write_text(yaml.safe_dump({
        "schema_version": "1.0", "audit_run_id": "2026-05-18T12:34:56Z-a1b2", "entries": []
    }))
    audit = tmp_path / "temporal_audit_results.yaml"
    audit.write_text(yaml.safe_dump({
        "schema_version": "1.0", "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18", "findings": []
    }))

    result = subprocess.run(
        [_sys.executable, str(SCRIPT),
         "--timeline", str(timeline),
         "--citation-provenance", str(provenance),
         "--temporal-audit", str(audit)],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"baseline mismatch — bibliography_agent.md was modified? stderr={result.stderr}"


def test_lint_bibliography_agent_modified_fails(tmp_path, monkeypatch):
    """F2 invariant: modified bibliography_agent.md fails the lint.

    Uses monkeypatch to point BIBLIOGRAPHY_AGENT_SHA256 at a wrong value, then runs the
    lint as a function (not subprocess) so we can override the module constant.
    """
    timeline = tmp_path / "timeline.yaml"
    timeline.write_text(yaml.safe_dump({"schema_version": "1.0", "sources": [], "events": []}))
    provenance = tmp_path / "citation_provenance.yaml"
    provenance.write_text(yaml.safe_dump({
        "schema_version": "1.0", "audit_run_id": "2026-05-18T12:34:56Z-a1b2", "entries": []
    }))
    audit = tmp_path / "temporal_audit_results.yaml"
    audit.write_text(yaml.safe_dump({
        "schema_version": "1.0", "audit_run_id": "2026-05-18T12:34:56Z-a1b2",
        "report_reference_date": "2026-05-18", "findings": []
    }))

    # Import the lint module and monkeypatch the expected sha256 to a bogus value
    import importlib.util
    spec_loader = importlib.util.spec_from_file_location("v3_9_4_lint", SCRIPT)
    lint_mod = importlib.util.module_from_spec(spec_loader)
    spec_loader.loader.exec_module(lint_mod)
    monkeypatch.setattr(lint_mod, "BIBLIOGRAPHY_AGENT_SHA256", "0" * 64)

    exit_code = lint_mod.main([
        "--timeline", str(timeline),
        "--citation-provenance", str(provenance),
        "--temporal-audit", str(audit),
    ])
    assert exit_code == 1, "expected exit 1 when sha256 baseline mismatches"


def test_timeline_extraction_agent_has_phase_boundary_block():
    agent_path = REPO_ROOT / "deep-research/agents/timeline_extraction_agent.md"
    assert agent_path.exists(), "timeline_extraction_agent.md not created"
    content = agent_path.read_text()
    # 4 load-bearing keywords from canonical v3.9.4 boundary block
    assert "## Phase Boundary (v3.9.4)" in content
    assert "MUST NOT" in content
    assert "MAY READ" in content
    assert "Enforcement (v3.9.4)" in content
    # M6 Citation Provenance Protocol section
    assert "## Citation Provenance Protocol (v3.9.4)" in content


def test_timeline_extraction_agent_lists_sidecar_deliverables():
    agent_path = REPO_ROOT / "deep-research/agents/timeline_extraction_agent.md"
    content = agent_path.read_text()
    assert "timeline.yaml" in content
    assert "citation_provenance.yaml" in content
    assert "version_records.yaml" in content


M3_IRON_RULE_MARKER = "## Temporal Integrity Iron Rule (v3.9.4)"
M3_KEY_PHRASES = [
    "Temporal claims are arithmetic, not stylistic.",
    "Identify the date or date range of every entity",
    "verify the cited document existed BEFORE the event",
]


def test_m3_iron_rule_present_in_report_compiler():
    path = REPO_ROOT / "deep-research/agents/report_compiler_agent.md"
    content = path.read_text()
    assert M3_IRON_RULE_MARKER in content
    for phrase in M3_KEY_PHRASES:
        assert phrase in content, f"missing phrase: {phrase}"


def test_m3_iron_rule_present_in_draft_writer():
    path = REPO_ROOT / "academic-paper/agents/draft_writer_agent.md"
    content = path.read_text()
    assert M3_IRON_RULE_MARKER in content
    for phrase in M3_KEY_PHRASES:
        assert phrase in content
