#!/usr/bin/env python3
"""Tests for company-research v2 data collector."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from python_implementation import company_research

REQUIRED_TOP = {
    "meta",
    "identity",
    "financials",
    "pipeline",
    "regulatory",
    "foundation",
    "sources",
    "data_gaps",
}
REQUIRED_META = {"company", "timestamp", "is_public", "version"}


def _run(company: str) -> dict:
    """Run collector and return parsed JSON."""
    with tempfile.TemporaryDirectory() as tmp:
        path = company_research(company, output_dir=tmp)
        assert Path(path).exists(), f"Output not created: {path}"
        assert path.endswith(".json"), f"Expected JSON: {path}"
        return json.loads(Path(path).read_text())


def _check_schema(data: dict) -> None:
    """Validate top-level JSON schema."""
    missing = REQUIRED_TOP - data.keys()
    assert not missing, f"Missing keys: {missing}"
    assert REQUIRED_META.issubset(data["meta"].keys())
    assert data["meta"]["version"] == "2.0"
    assert isinstance(data["identity"], dict)
    assert isinstance(data["financials"], dict)
    assert isinstance(data["pipeline"], dict)
    assert isinstance(data["regulatory"], dict)
    assert isinstance(data["foundation"], dict)
    assert isinstance(data["sources"], list)
    assert isinstance(data["data_gaps"], list)
    for src in data["sources"]:
        assert {"tool", "query", "items", "tier"}.issubset(src.keys()), (
            f"Bad source: {src}"
        )


def test_moderna() -> None:
    """Public biotech — rich data across all phases."""
    data = _run("Moderna")
    _check_schema(data)
    assert data["meta"]["is_public"] is True
    assert data["identity"].get("ticker")
    assert data["identity"].get("cik")
    assert len(data["sources"]) >= 5
    print(f"PASS: Moderna ({len(data['sources'])} sources)")


def test_anthropic() -> None:
    """Private company — should produce valid JSON regardless."""
    data = _run("Anthropic")
    _check_schema(data)
    # Anthropic may match SEC filings for unrelated entities;
    # key test is that the skill completes without crashing.
    print(
        f"PASS: Anthropic (public={data['meta']['is_public']}, {len(data['sources'])} sources)"
    )


def test_myriad() -> None:
    """Diagnostics company — trials + devices."""
    data = _run("Myriad Genetics")
    _check_schema(data)
    assert data["meta"]["is_public"] is True
    tools = [s["tool"] for s in data["sources"]]
    assert "ClinicalTrials_search_studies" in tools
    print(f"PASS: Myriad ({len(data['sources'])} sources)")


def test_nonsense() -> None:
    """Nonsense input — no crash, valid JSON."""
    data = _run("XYZNONEXISTENT99999")
    _check_schema(data)
    assert data["identity"]["name"] == "XYZNONEXISTENT99999"
    print("PASS: Nonsense input handled")


def test_schema_offline() -> None:
    """Quick schema validation without API calls."""
    artifact = {
        "meta": {
            "company": "Test",
            "timestamp": "now",
            "is_public": False,
            "version": "2.0",
        },
        "identity": {"name": "Test", "is_public": False},
        "financials": {},
        "pipeline": {},
        "regulatory": {},
        "foundation": {},
        "sources": [],
        "data_gaps": [],
    }
    _check_schema(artifact)
    print("PASS: Offline schema validation")


def main() -> int:
    tests = [
        ("Schema (offline)", test_schema_offline),
        ("Moderna (public)", test_moderna),
        ("Anthropic (private)", test_anthropic),
        ("Myriad (diagnostics)", test_myriad),
        ("Nonsense input", test_nonsense),
    ]
    passed = 0
    for label, fn in tests:
        try:
            fn()
            passed += 1
        except Exception as e:
            print(f"FAIL: {label}: {e}")
    print(f"\n{passed}/{len(tests)} passed")
    return 0 if passed == len(tests) else 1


if __name__ == "__main__":
    sys.exit(main())
