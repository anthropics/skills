"""Tests for bootstrap_timeline_yaml.py (opt-in Crossref + pdftotext)."""
from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts/bootstrap_timeline_yaml.py"


def _load_script_module():
    spec = importlib.util.spec_from_file_location("bootstrap_timeline_yaml", SCRIPT)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_bootstrap_dry_run_emits_skeleton(tmp_path):
    """Dry-run produces a timeline.yaml skeleton without calling Crossref/pdftotext."""
    corpus = tmp_path / "corpus.yaml"
    corpus.write_text(yaml.safe_dump({
        "literature_corpus": [
            {"citation_key": "alpha", "title": "Alpha", "authors": [{"family": "Smith"}],
             "year": 2024, "source_pointer": "doi:10.1/alpha", "doi": "10.1/alpha"},
        ]
    }))
    out = tmp_path / "timeline.yaml"
    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--corpus", str(corpus),
         "--output", str(out),
         "--dry-run"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"stderr={result.stderr}"
    assert out.exists()
    data = yaml.safe_load(out.read_text())
    assert data["schema_version"] == "1.0"
    sources = data["sources"]
    assert len(sources) == 1
    assert sources[0]["citation_key"] == "alpha"
    # Dry run: published_date.method should NOT be crossref_lookup (no API call)
    # Acceptable: either falls back to corpus year (method: adapter_metadata) OR absent
    pd = sources[0].get("published_date")
    if pd is not None:
        assert pd.get("provenance", {}).get("method") != "crossref_lookup"


def test_bootstrap_validates_against_timeline_schema(tmp_path):
    """Generated timeline.yaml must validate against timeline.schema.json."""
    import jsonschema
    corpus = tmp_path / "corpus.yaml"
    corpus.write_text(yaml.safe_dump({
        "literature_corpus": [
            {"citation_key": "alpha", "title": "Alpha", "authors": [{"family": "Smith"}],
             "year": 2024, "source_pointer": "doi:10.1/alpha", "doi": "10.1/alpha"},
        ]
    }))
    out = tmp_path / "timeline.yaml"
    result = subprocess.run(
        [sys.executable, str(SCRIPT),
         "--corpus", str(corpus),
         "--output", str(out),
         "--dry-run"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0
    data = yaml.safe_load(out.read_text())
    schema = json.loads((REPO_ROOT / "shared/contracts/passport/timeline.schema.json").read_text())
    jsonschema.validate(data, schema)  # should not raise


def test_crossref_lookup_quotes_doi_path(monkeypatch):
    module = _load_script_module()
    captured = []

    class FakeResponse:
        status_code = 200

        def json(self):
            return {"message": {"title": ["ok"]}}

    class FakeRequests:
        @staticmethod
        def get(url, timeout):
            captured.append((url, timeout))
            return FakeResponse()

    monkeypatch.setattr(module, "requests", FakeRequests)

    result = module._crossref_lookup("10.1000/foo?bar=baz", dry_run=False)

    assert result == {"title": ["ok"]}
    assert captured == [
        ("https://api.crossref.org/works/10.1000%2Ffoo%3Fbar%3Dbaz", 10)
    ]


def test_bootstrap_entry_locator_matches_queried_url(monkeypatch):
    # Codex follow-up to #310: the lookup encodes the DOI, so the recorded
    # source_locator must point at the same encoded URL — not the raw DOI —
    # or provenance references a resource that was never queried.
    module = _load_script_module()

    monkeypatch.setattr(
        module,
        "_crossref_lookup",
        lambda doi, dry_run: {"issued": {"date-parts": [[2024, 3]]}},
    )

    out = module._bootstrap_entry(
        {"citation_key": "foo2024", "doi": "10.1000/foo?bar=baz"},
        dry_run=False,
    )

    assert out["published_date"]["provenance"]["source_locator"] == (
        "https://api.crossref.org/works/10.1000%2Ffoo%3Fbar%3Dbaz"
    )


def test_pdftotext_uses_resolved_executable(monkeypatch, tmp_path):
    module = _load_script_module()
    pdf = tmp_path / "paper.pdf"
    pdf.touch()
    calls = []

    class FakeCompleted:
        returncode = 0
        stdout = "\nFirst line\nSecond line\n"

    monkeypatch.setattr(module.shutil, "which", lambda name: "/usr/local/bin/pdftotext")
    monkeypatch.setattr(
        module.subprocess,
        "run",
        lambda args, **kwargs: calls.append((args, kwargs)) or FakeCompleted(),
    )

    result = module._pdftotext_first_line(pdf, dry_run=False)

    assert result == "First line"
    assert calls[0][0][0] == "/usr/local/bin/pdftotext"
