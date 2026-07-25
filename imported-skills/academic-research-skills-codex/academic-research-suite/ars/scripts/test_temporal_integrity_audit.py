"""Tests for v3.9.4 temporal_integrity_audit.py 5-pass verifier."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts/temporal_integrity_audit.py"


def _run_audit(tmp_path: Path, draft: str, timeline: dict, citation_provenance: dict | None = None,
               report_reference_date: str = "2026-05-18") -> dict:
    """Helper: write inputs, run audit, return parsed output."""
    (tmp_path / "draft.md").write_text(draft)
    (tmp_path / "timeline.yaml").write_text(yaml.safe_dump(timeline))
    (tmp_path / "citation_provenance.yaml").write_text(yaml.safe_dump(
        citation_provenance or {"schema_version": "1.0", "audit_run_id": "2026-05-18T12:34:56Z-a1b2", "entries": []}
    ))
    out = tmp_path / "temporal_audit_results.yaml"
    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--draft", str(tmp_path / "draft.md"),
         "--timeline", str(tmp_path / "timeline.yaml"),
         "--citation-provenance", str(tmp_path / "citation_provenance.yaml"),
         "--output", str(out),
         "--report-reference-date", report_reference_date,
         "--audit-run-id", "2026-05-18T12:34:56Z-a1b2"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"audit failed: stderr={result.stderr!r}"
    return yaml.safe_load(out.read_text())


def test_audit_scaffold_returns_empty_findings_on_empty_draft(tmp_path):
    """Scaffold sanity: empty draft → 0 findings, valid output shape."""
    result = _run_audit(tmp_path, draft="", timeline={"schema_version": "1.0", "sources": [], "events": []})
    assert result["schema_version"] == "1.0"
    assert result["audit_run_id"] == "2026-05-18T12:34:56Z-a1b2"
    assert result["report_reference_date"] == "2026-05-18"
    assert result["findings"] == []


def test_p5_currently_emits_deictic_finding(tmp_path):
    """Mode 5 time-bomb: 'currently' triggers TEMPORAL-DEICTIC."""
    result = _run_audit(
        tmp_path,
        draft="Currently, the most recent edition prescribes annual review.\n",
        timeline={"schema_version": "1.0", "sources": [], "events": []},
    )
    deictic = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-DEICTIC"]
    assert len(deictic) >= 1, f"expected >=1 TEMPORAL-DEICTIC, got: {result['findings']}"
    first = deictic[0]
    assert first["mode"] == 5
    assert first["severity"] == "LOW"
    assert first["matched_span"] is not None
    assert "currently" in first["matched_span"]["text"].lower()


def test_p5_anchored_phrase_no_finding(tmp_path):
    """Mode 5 legitimate: 'As of 2026-05-18, the 2024 edition prescribes' must NOT trigger."""
    result = _run_audit(
        tmp_path,
        draft="As of 2026-05-18, the 2024 edition prescribes annual review.\n",
        timeline={"schema_version": "1.0", "sources": [], "events": []},
    )
    deictic = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-DEICTIC"]
    assert deictic == [], f"unexpected deictic findings: {deictic}"


def test_p1_future_as_past_emits_arithmetic_impossible(tmp_path):
    """Mode 1: 'As of March 2025, ... had already completed June 2025 deliverables' is physically impossible."""
    result = _run_audit(
        tmp_path,
        draft="As of March 2025, the report noted that the system had already completed June 2025 deliverables.\n",
        timeline={"schema_version": "1.0", "sources": [], "events": []},
    )
    arith = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-ARITHMETIC-IMPOSSIBLE"]
    assert len(arith) == 1, f"expected 1 TEMPORAL-ARITHMETIC-IMPOSSIBLE, got: {result['findings']}"
    first = arith[0]
    assert first["mode"] == 1
    assert first["severity"] == "HIGH"
    assert first["bound_dates"] is not None
    # anchor=March 2025, event=June 2025; event > anchor
    assert first["bound_dates"]["left"]["role"] == "anchor"
    assert "2025-03" in first["bound_dates"]["left"]["value"]
    assert first["bound_dates"]["right"]["role"] == "event"
    assert "2025-06" in first["bound_dates"]["right"]["value"]


def test_p1_prospective_already_past(tmp_path):
    """Mode 1 Pattern B: forthcoming event but anchor is later than event date."""
    result = _run_audit(
        tmp_path,
        draft="The June 2025 delivery to be completed by the project team, as of December 2025 the project is unfinished.\n",
        timeline={"schema_version": "1.0", "sources": [], "events": []},
    )
    arith = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-ARITHMETIC-IMPOSSIBLE"]
    assert len(arith) >= 1


def test_p2_2026_handbook_governing_2022_event(tmp_path):
    """Mode 2: 2026 handbook cited for 2022 review cycle → anachronism."""
    result = _run_audit(
        tmp_path,
        draft="The 2026 Handbook governed the 2022 review cycle.<!--ref:handbook-2026ed-->\n",
        timeline={
            "schema_version": "1.0",
            "sources": [{
                "citation_key": "handbook-2026ed",
                "type": "institutional-document",
                "published_date": {
                    "value": "2026-09-15", "precision": "day", "open_ended": False,
                    "provenance": {"method": "crossref_lookup", "confidence": "high"},
                },
                "effective_date_range": {
                    "start": {
                        "value": "2026-09-15", "precision": "day", "open_ended": False,
                        "provenance": {"method": "crossref_lookup", "confidence": "high"},
                    },
                    "end": {
                        "value": None, "precision": "unknown", "open_ended": True,
                        "provenance": {"method": "user_override", "confidence": "high"},
                    },
                },
            }],
            "events": [],
        },
    )
    anachronism = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-ANACHRONISTIC-CITATION"]
    assert len(anachronism) == 1, f"expected 1 anachronism, got: {result['findings']}"
    f0 = anachronism[0]
    assert f0["mode"] == 2
    assert f0["bound_event"] is not None
    assert f0["bound_refs"][0]["ref_slug"] == "handbook-2026ed"


def test_p3_unmaterialized_comparator(tmp_path):
    """Mode 3: prose mentions '1998 edition' but timeline only has 2020 edition."""
    result = _run_audit(
        tmp_path,
        draft="This differs from the 1998 edition of the standard.<!--ref:standard-2020ed-->\n",
        timeline={
            "schema_version": "1.0",
            "sources": [{
                "citation_key": "standard-2020ed",
                "type": "standard",
                "version_family_id": "standard-family",
                "published_date": {
                    "value": "2020-01-01", "precision": "year", "open_ended": False,
                    "provenance": {"method": "user_override", "confidence": "high"},
                },
            }],
            "events": [],
        },
    )
    comparator = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-COMPARATOR-UNMATERIALIZED"]
    assert len(comparator) == 1, f"expected 1 comparator finding, got: {result['findings']}"
    assert comparator[0]["matched_span"] is not None
    assert "1998" in comparator[0]["matched_span"]["text"]


def test_p4_causal_inversion(tmp_path):
    """Mode 4: 'Policy A enabled Policy B' but timeline has A AFTER B."""
    result = _run_audit(
        tmp_path,
        draft="Policy A<!--ref:policy-a--> enabled Policy B<!--ref:policy-b-->.\n",
        timeline={
            "schema_version": "1.0",
            "sources": [
                {"citation_key": "policy-a", "type": "policy",
                 "published_date": {"value": "2026-03-01", "precision": "day", "open_ended": False,
                                    "provenance": {"method": "user_override", "confidence": "high"}}},
                {"citation_key": "policy-b", "type": "policy",
                 "published_date": {"value": "2020-05-15", "precision": "day", "open_ended": False,
                                    "provenance": {"method": "user_override", "confidence": "high"}}},
            ],
            "events": [],
        },
    )
    causal = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-CAUSAL-INVERSION"]
    assert len(causal) == 1, f"expected 1 causal finding, got: {result['findings']}"
    f0 = causal[0]
    assert f0["bound_dates"] is not None
    assert f0["bound_dates"]["left"]["ref_slug"] == "policy-a"
    assert f0["bound_dates"]["right"]["ref_slug"] == "policy-b"


FIXTURE_ROOT = REPO_ROOT / "tests/fixtures/v3.9.4-temporal"


@pytest.mark.parametrize("fixture_name", [
    "mode_1_future_as_past",
    "mode_2_version_as_evidence_past",
    "mode_3_comparator_unmaterialized",
    "mode_4_causal_inversion",
    "mode_5_time_bomb",
])
def test_positive_fixture_golden(tmp_path, fixture_name):
    fixture_dir = FIXTURE_ROOT / fixture_name
    out = tmp_path / "temporal_audit_results.yaml"
    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--draft", str(fixture_dir / "draft.md"),
         "--timeline", str(fixture_dir / "timeline.yaml"),
         "--citation-provenance", str(fixture_dir / "citation_provenance.yaml"),
         "--output", str(out),
         "--report-reference-date", "2026-05-18",
         "--audit-run-id", "2026-05-18T12:34:56Z-a1b2"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    actual = yaml.safe_load(out.read_text())
    expected = yaml.safe_load((fixture_dir / "expected_temporal_audit_results.yaml").read_text())
    assert actual == expected, f"diff for {fixture_name}:\nactual={actual}\nexpected={expected}"


@pytest.mark.parametrize("fixture_name", [
    "mode_1_legitimate",
    "mode_2_legitimate",
    "mode_3_legitimate",
    "mode_4_legitimate",
    "mode_5_legitimate",
])
def test_negative_fixture_golden(tmp_path, fixture_name):
    """Legitimate prose fixtures: verifier output matches captured baseline (typically zero violation findings)."""
    fixture_dir = FIXTURE_ROOT / fixture_name
    out = tmp_path / "temporal_audit_results.yaml"
    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--draft", str(fixture_dir / "draft.md"),
         "--timeline", str(fixture_dir / "timeline.yaml"),
         "--citation-provenance", str(fixture_dir / "citation_provenance.yaml"),
         "--output", str(out),
         "--report-reference-date", "2026-05-18",
         "--audit-run-id", "2026-05-18T12:34:56Z-a1b2"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"audit failed: stderr={result.stderr!r}"
    actual = yaml.safe_load(out.read_text())
    expected = yaml.safe_load((fixture_dir / "expected_temporal_audit_results.yaml").read_text())
    assert actual == expected, f"diff for {fixture_name}: actual={actual}\nexpected={expected}"
    # Optional: assert no Mode N findings for the matching mode
    mode_n = int(fixture_name.split("_")[1])
    mode_findings = [f for f in actual["findings"]
                     if f.get("mode") == mode_n
                     and f["finding_kind"] != "TEMPORAL-METADATA-MISSING"]
    assert mode_findings == [], f"unexpected mode-{mode_n} violation: {mode_findings}"


def test_audit_writes_markdown_report(tmp_path):
    """Audit must write phase4_composition/temporal_audit.md alongside the YAML."""
    (tmp_path / "draft.md").write_text("Currently, the framework is under review.\n")
    (tmp_path / "timeline.yaml").write_text(yaml.safe_dump(
        {"schema_version": "1.0", "sources": [], "events": []}))
    (tmp_path / "citation_provenance.yaml").write_text(yaml.safe_dump(
        {"schema_version": "1.0", "audit_run_id": "2026-05-18T12:34:56Z-a1b2", "entries": []}))
    out_yaml = tmp_path / "temporal_audit_results.yaml"
    out_md = tmp_path / "temporal_audit.md"

    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--draft", str(tmp_path / "draft.md"),
         "--timeline", str(tmp_path / "timeline.yaml"),
         "--citation-provenance", str(tmp_path / "citation_provenance.yaml"),
         "--output", str(out_yaml),
         "--markdown-output", str(out_md),
         "--report-reference-date", "2026-05-18",
         "--audit-run-id", "2026-05-18T12:34:56Z-a1b2"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    assert out_yaml.exists()
    assert out_md.exists()
    md = out_md.read_text()
    assert "# Temporal Audit Results" in md
    assert "TEMPORAL-DEICTIC" in md


def test_metadata_missing_fixture(tmp_path):
    """METADATA-MISSING fires when ref's timeline source lacks effective_date_range."""
    fixture_dir = FIXTURE_ROOT / "metadata_missing_p2"
    out = tmp_path / "temporal_audit_results.yaml"
    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--draft", str(fixture_dir / "draft.md"),
         "--timeline", str(fixture_dir / "timeline.yaml"),
         "--citation-provenance", str(fixture_dir / "citation_provenance.yaml"),
         "--output", str(out),
         "--report-reference-date", "2026-05-18",
         "--audit-run-id", "2026-05-18T12:34:56Z-a1b2"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0
    actual = yaml.safe_load(out.read_text())
    expected = yaml.safe_load((fixture_dir / "expected_temporal_audit_results.yaml").read_text())
    assert actual == expected
    # Spec contract: METADATA-MISSING for the ref
    metadata_missing = [f for f in actual["findings"] if f["finding_kind"] == "TEMPORAL-METADATA-MISSING"]
    assert len(metadata_missing) == 1
    assert metadata_missing[0]["bound_refs"][0]["ref_slug"] == "handbook-2024ed"


def test_freeze_regression_byte_identical_across_dates(tmp_path):
    """CC6: report_reference_date is frozen — output must be byte-identical regardless of wall-clock today.

    This test does NOT depend on time.time() or datetime.now() behavior, because the verifier itself
    uses the --report-reference-date arg. The regression asserts the SAME --report-reference-date
    produces byte-identical output across two independent runs.
    """
    fixture_dir = FIXTURE_ROOT / "report_reference_date_freeze"
    out1 = tmp_path / "run1.yaml"
    out2 = tmp_path / "run2.yaml"
    for out in [out1, out2]:
        result = subprocess.run(
            [sys.executable, str(SCRIPT),
             "--draft", str(fixture_dir / "draft.md"),
             "--timeline", str(fixture_dir / "timeline.yaml"),
             "--citation-provenance", str(fixture_dir / "citation_provenance.yaml"),
             "--output", str(out),
             "--report-reference-date", "2026-05-18",
             "--audit-run-id", "2026-05-18T12:34:56Z-a1b2"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0, f"stderr={result.stderr}"
    assert out1.read_bytes() == out2.read_bytes(), "byte-identical regression failed"


# v3.9.4.1 hotfix: _date_to_interval coverage for all schema-valid shapes
import importlib.util

_AUDIT_SPEC = importlib.util.spec_from_file_location(
    "temporal_integrity_audit", REPO_ROOT / "scripts/temporal_integrity_audit.py"
)
_audit_mod = importlib.util.module_from_spec(_AUDIT_SPEC)
_AUDIT_SPEC.loader.exec_module(_audit_mod)


@pytest.mark.parametrize("raw,expected", [
    # Day precision (already worked in v3.9.4)
    ("2024-09-15", ("2024-09-15", "2024-09-15")),
    # Year precision (already worked in v3.9.4)
    ("2024", ("2024-01-01", "2024-12-31")),
    # Prose month (already worked in v3.9.4)
    ("March 2025", ("2025-03-01", "2025-03-31")),
    # v3.9.4.1 hotfix: month precision YYYY-MM
    ("2024-09", ("2024-09-01", "2024-09-30")),
    ("2024-02", ("2024-02-01", "2024-02-28")),
    ("2024-12", ("2024-12-01", "2024-12-31")),
    # v3.9.4.1 hotfix: interval precision YYYY-MM-DD..YYYY-MM-DD
    ("2022-04-01..2022-12-31", ("2022-04-01", "2022-12-31")),
    ("2020-10-01..2024-09-30", ("2020-10-01", "2024-09-30")),
])
def test_date_to_interval_parses_all_schema_valid_shapes(raw, expected):
    """v3.9.4.1 hotfix: verifier handles all 5 v3.9.4 schema date shapes.

    v3.9.4 only parsed day/year/prose-month — schema-valid month (YYYY-MM)
    and interval (YYYY-MM-DD..YYYY-MM-DD) shapes raised ValueError, causing
    P2/P4 to silently skip checks. Real-world Crossref returns month precision;
    real-world effective_date_range uses interval. This test locks the fix."""
    assert _audit_mod._date_to_interval(raw) == expected


def test_date_to_interval_rejects_invalid_month():
    """Defensive: YYYY-13 (month > 12) should raise, not produce garbage."""
    with pytest.raises(ValueError):
        _audit_mod._date_to_interval("2024-13")


def test_p2_provenance_low_emits_metadata_missing_skips_anachronism(tmp_path):
    """v3.9.4.1 fix #1: P2 must consult citation_provenance and emit METADATA-MISSING
    (not ANACHRONISTIC-CITATION) when confidence is low — spec §3.4 first-party safety check."""
    # Even though timeline says handbook-2026ed is way in the future, citation_provenance
    # confidence:low must downgrade to METADATA-MISSING instead of anachronism finding.
    timeline = {
        "schema_version": "1.0",
        "sources": [{
            "citation_key": "handbook-2026ed",
            "type": "institutional-document",
            "effective_date_range": {
                "start": {"value": "2026-09-15", "precision": "day", "open_ended": False,
                          "provenance": {"method": "crossref_lookup", "confidence": "high"}},
                "end": {"value": None, "precision": "unknown", "open_ended": True,
                        "provenance": {"method": "user_override", "confidence": "high"}},
            },
        }],
        "events": [],
    }
    citation_provenance = {
        "schema_version": "1.0",
        "audit_run_id": "2026-05-19T00:00:00Z-test",
        "entries": [{
            "citation_key": "handbook-2026ed",
            "crossref_issued": None,
            "pdftotext_cover_first_line": None,
            "verification_method": "none",
            "confidence": "low",
            "notes": None,
        }],
    }
    result = _run_audit(
        tmp_path,
        draft="The 2026 Handbook governed the 2022 review cycle.<!--ref:handbook-2026ed-->\n",
        timeline=timeline,
        citation_provenance=citation_provenance,
    )
    # No anachronism findings (the v3.9.4 silent-bypass bug would have emitted one).
    anachronism = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-ANACHRONISTIC-CITATION"]
    assert anachronism == [], f"v3.9.4.1 fix #1 broken — anachronism emitted despite confidence:low: {anachronism}"
    # Exactly one METADATA-MISSING citing the provenance reason.
    metadata_missing = [f for f in result["findings"]
                        if f["finding_kind"] == "TEMPORAL-METADATA-MISSING"
                        and "confidence=low" in f.get("rationale", "")]
    assert len(metadata_missing) == 1, f"expected 1 METADATA-MISSING with provenance reason; got {result['findings']}"


def test_p4_direct_date_causal_inversion_no_refs(tmp_path):
    """v3.9.4.1 fix #3: P4 must bind to direct date captures when ref markers absent
    (spec §3.2 P4: each side may bind to ref marker OR direct date capture)."""
    # No ref markers; both sides are bare dates. "enabled" requires left.date < right.date.
    # Here left=2026 right=2020 → violation.
    result = _run_audit(
        tmp_path,
        draft="The 2026 policy enabled the 2020 rollout.\n",
        timeline={"schema_version": "1.0", "sources": [], "events": []},
    )
    causal = [f for f in result["findings"] if f["finding_kind"] == "TEMPORAL-CAUSAL-INVERSION"]
    assert len(causal) == 1, f"expected 1 causal inversion via direct date binding; got {result['findings']}"
    f0 = causal[0]
    assert f0["bound_dates"] is not None
    assert f0["bound_dates"]["left"]["source"] == "draft_capture"
    assert f0["bound_dates"]["right"]["source"] == "draft_capture"
    # bound_refs should be empty (no slugs bound).
    assert f0["bound_refs"] == []
