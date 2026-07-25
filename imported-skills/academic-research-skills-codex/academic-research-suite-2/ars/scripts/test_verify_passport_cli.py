#!/usr/bin/env python3
"""Tests for the verify_passport CLI (Delta 5 ad-hoc entry point).

Spec: docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md §2 Delta 5
(`python -m scripts.verify_passport <passport.yaml>`).

The CLI is a thin wrapper: it loads a passport YAML and prints the
verification summary as JSON. Network resolvers are real by default; tests
inject a no-network clients factory via the public `run` seam.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest
import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))


def _no_network_clients():
    def default():
        m = MagicMock()
        m.doi_lookup_with_title_check.return_value = None
        m.title_search.return_value = None
        m.arxiv_id_lookup.return_value = None
        m.lookup.return_value = {"matched": False}
        return m
    return {n: default() for n in
            ("crossref", "openalex", "semantic_scholar", "arxiv")}


def _entry(**overrides):
    # Schema-valid corpus entry: all five required corpus fields, NO ref_slug
    # (literature_corpus_entry.schema is additionalProperties:False — the ref_slug
    # lives in writer prose, not the corpus).
    base = {
        "citation_key": "a", "title": "T",
        "authors": [{"family": "Doe", "given": "J"}], "year": 2020,
        "source_pointer": "kb://refs/a",
        "doi": "10.5555/x", "obtained_via": "folder-scan",
    }
    base.update(overrides)
    return base


def _write_passport(tmp_path, corpus):
    p = tmp_path / "passport.yaml"
    p.write_text(yaml.safe_dump({"literature_corpus": corpus}), encoding="utf-8")
    return p


def test_cli_fixture_is_schema_valid():
    """Guard the guard: the _entry fixture must validate against
    literature_corpus_entry.schema.json, so the CLI tests exercise the real
    production shape (the #332 masking bug was a fixture carrying a forbidden
    ref_slug field)."""
    import json
    from jsonschema import Draft202012Validator
    schema = json.loads((
        REPO_ROOT / "shared" / "contracts" / "passport"
        / "literature_corpus_entry.schema.json"
    ).read_text(encoding="utf-8"))
    errors = list(Draft202012Validator(schema).iter_errors(_entry()))
    assert errors == [], f"_entry fixture must be a valid corpus entry: {errors}"


def test_cli_refuses_without_prose_join(tmp_path, capsys):
    """Default behavior: a passport-only CLI cannot honestly emit a
    citation_verification_summary, because the summary contract requires the
    prose-sourced ref_slug join that a passport alone does not carry. The CLI
    refuses (nonzero) with a clear error rather than fabricating ref_slug (#332)."""
    from verify_passport import run
    passport = _write_passport(tmp_path, [_entry()])
    rc = run([str(passport)], clients_factory=_no_network_clients)
    assert rc != 0
    err = capsys.readouterr().err
    assert "ref_slug" in err or "prose" in err  # explains why it refused


def test_cli_synthetic_ref_slug_uses_citation_key(tmp_path, capsys):
    """Explicit escape hatch: --synthetic-ref-slug citation_key synthesizes
    ref_slug from citation_key so the ad-hoc tool can still produce output. It
    warns on stderr that the result is diagnostic (not prose-join-safe) so no
    downstream consumer mistakes it for a real prose join (#332)."""
    from verify_passport import run
    passport = _write_passport(tmp_path, [_entry(citation_key="a")])
    rc = run([str(passport), "--synthetic-ref-slug", "citation_key"],
             clients_factory=_no_network_clients)
    assert rc == 0
    captured = capsys.readouterr()
    out = json.loads(captured.out)
    assert len(out) == 1
    assert out[0]["citation_key"] == "a"
    assert out[0]["ref_slug"] == "a"  # synthesized from citation_key
    assert out[0]["lookup_verified"] == "false"  # id-keyed unmatched
    assert out[0]["anchor_present"] is False  # no prose anchor available
    # the synthetic mode must say so on stderr (diagnostic, not prose-join-safe)
    assert "synthetic" in captured.err.lower() or "diagnostic" in captured.err.lower()


def test_cli_missing_file_errors(tmp_path):
    from verify_passport import run
    rc = run([str(tmp_path / "nope.yaml")], clients_factory=_no_network_clients)
    assert rc != 0


def test_cli_requires_path_arg():
    from verify_passport import run
    with pytest.raises(SystemExit):
        run([], clients_factory=_no_network_clients)
