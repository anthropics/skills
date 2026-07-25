"""Tests for the CI lint that validates passport/rejection-log examples
against their schemas and enforces citation_key uniqueness."""
from pathlib import Path
import subprocess
import sys
import yaml
import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "scripts/check_literature_corpus_schema.py"


def _write_yaml(tmp_path, name, data):
    p = tmp_path / name
    with p.open("w", encoding="utf-8") as f:
        yaml.safe_dump(data, f, sort_keys=True)
    return p


def _run(args, cwd=None):
    return subprocess.run(
        [sys.executable, str(SCRIPT)] + args,
        capture_output=True,
        text=True,
        cwd=cwd or REPO_ROOT,
    )


def test_script_exists():
    assert SCRIPT.exists()


def test_passes_on_valid_passport(tmp_path):
    passport = {
        "literature_corpus": [
            {
                "citation_key": "chen2024",
                "title": "T",
                "authors": [{"family": "Chen"}],
                "year": 2024,
                "source_pointer": "file:///x.pdf",
            }
        ]
    }
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode == 0, r.stderr


def test_fails_on_schema_violation(tmp_path):
    passport = {
        "literature_corpus": [
            {
                "citation_key": "chen2024",
                "title": "T",
                "authors": [{}],  # invalid author
                "year": 2024,
                "source_pointer": "file:///x.pdf",
            }
        ]
    }
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode != 0
    assert "schema" in r.stderr.lower() or "validation" in r.stderr.lower()


def test_fails_on_duplicate_citation_key(tmp_path):
    passport = {
        "literature_corpus": [
            {
                "citation_key": "dup",
                "title": "A",
                "authors": [{"family": "X"}],
                "year": 2024,
                "source_pointer": "file:///a.pdf",
            },
            {
                "citation_key": "dup",
                "title": "B",
                "authors": [{"family": "Y"}],
                "year": 2024,
                "source_pointer": "file:///b.pdf",
            },
        ]
    }
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode != 0
    assert "duplicate" in r.stderr.lower() or "unique" in r.stderr.lower()


def test_passes_on_valid_rejection_log(tmp_path):
    log = {
        "adapter_name": "zotero.py",
        "adapter_version": "1.0.0",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [],
    }
    _write_yaml(tmp_path, "rejection_log.yaml", log)
    r = _run(["--rejection-log", str(tmp_path / "rejection_log.yaml")])
    assert r.returncode == 0, r.stderr


def test_default_mode_scans_repo_examples():
    """With no args, script scans scripts/adapters/examples/** for
    expected_passport.yaml and expected_rejection_log.yaml and validates
    each. This is the CI-invoked mode. At this point the examples don't
    exist yet (T7-T9 will populate them), so 0 (no files) is acceptable."""
    r = _run([])
    assert r.returncode in (0, 1)


# --- T4 reminder (codex T3-review P2): FORMAT_CHECKER must be wired ---
# Otherwise format=date-time is silently ignored on generated_at and obtained_at.

def test_passport_with_invalid_obtained_at_format_fails(tmp_path):
    passport = {
        "literature_corpus": [
            {
                "citation_key": "chen2024",
                "title": "T",
                "authors": [{"family": "Chen"}],
                "year": 2024,
                "source_pointer": "file:///x.pdf",
                "obtained_at": "definitely-not-a-date",
            }
        ]
    }
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode != 0, (
        "format=date-time on obtained_at must be enforced. "
        "If this passes, validate_passport built Draft202012Validator "
        "without format_checker — see codex T3-review P2."
    )


def test_rejection_log_with_invalid_generated_at_format_fails(tmp_path):
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "definitely-not-a-date",
        "rejected": [],
    }
    _write_yaml(tmp_path, "rejection_log.yaml", log)
    r = _run(["--rejection-log", str(tmp_path / "rejection_log.yaml")])
    assert r.returncode != 0, (
        "format=date-time on generated_at must be enforced. "
        "If this passes, validate_rejection_log built Draft202012Validator "
        "without format_checker — see codex T3-review P2."
    )


# --- additional integration coverage ---

def test_help_flag_runs_clean():
    r = _run(["--help"])
    assert r.returncode == 0
    assert "passport" in r.stdout.lower()


def test_passport_other_obtained_via_without_adapter_name_fails(tmp_path):
    """T2 patch contract: obtained_via='other' requires adapter_name.
    Lint must propagate the schema's allOf if/then conditional."""
    passport = {
        "literature_corpus": [
            {
                "citation_key": "chen2024",
                "title": "T",
                "authors": [{"family": "Chen"}],
                "year": 2024,
                "source_pointer": "file:///x.pdf",
                "obtained_via": "other",
                # adapter_name missing
            }
        ]
    }
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode != 0


def test_rejection_log_other_reason_with_empty_detail_fails(tmp_path):
    """T3 patch contract: detail.minLength=1 must be enforced."""
    log = {
        "adapter_name": "x",
        "adapter_version": "1",
        "generated_at": "2026-04-23T00:00:00Z",
        "rejected": [{"source": "s", "reason": "other", "detail": ""}],
    }
    _write_yaml(tmp_path, "rejection_log.yaml", log)
    r = _run(["--rejection-log", str(tmp_path / "rejection_log.yaml")])
    assert r.returncode != 0


# --- T4-T6 patch (codex 2026-04-25) ---

def test_passport_missing_literature_corpus_key_fails(tmp_path):
    """[P1] A passport YAML without literature_corpus must fail lint.
    Previously `data.get('literature_corpus', [])` defaulted to empty
    list and silently passed."""
    passport = {"some_other_field": "value"}
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode != 0
    assert "literature_corpus" in r.stderr.lower()


def test_passport_empty_dict_fails(tmp_path):
    """[P1] {} must fail too — same root cause."""
    passport = {}
    _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(tmp_path / "passport.yaml")])
    assert r.returncode != 0


def test_passport_top_level_list_fails_cleanly(tmp_path):
    """[P2] Top-level list YAML must produce a controlled lint error,
    not crash with AttributeError on .get()."""
    p = tmp_path / "passport.yaml"
    p.write_text("- a\n- b\n- c\n", encoding="utf-8")
    r = _run(["--passport", str(p)])
    assert r.returncode != 0
    # Crash would surface a Python traceback. Controlled error path emits
    # something readable on stderr.
    assert "Traceback" not in r.stderr
    assert "AttributeError" not in r.stderr


def test_passport_malformed_yaml_fails_cleanly(tmp_path):
    """[P2] Malformed YAML must not surface yaml.ParserError to stderr;
    the lint should report it as a per-file failure."""
    p = tmp_path / "passport.yaml"
    p.write_text("a: [\n", encoding="utf-8")  # unterminated flow seq
    r = _run(["--passport", str(p)])
    assert r.returncode != 0
    assert "Traceback" not in r.stderr


def test_rejection_log_top_level_list_fails_cleanly(tmp_path):
    """[P2] Same crash protection on the rejection-log path."""
    p = tmp_path / "rejection_log.yaml"
    p.write_text("- a\n- b\n", encoding="utf-8")
    r = _run(["--rejection-log", str(p)])
    assert r.returncode != 0
    assert "Traceback" not in r.stderr


def test_rejection_log_malformed_yaml_fails_cleanly(tmp_path):
    p = tmp_path / "rejection_log.yaml"
    p.write_text("a: [\n", encoding="utf-8")
    r = _run(["--rejection-log", str(p)])
    assert r.returncode != 0
    assert "Traceback" not in r.stderr


def test_default_mode_catches_bad_examples_fixture(tmp_path):
    """[P2] Tighten the default-scan test. Drop a known-bad
    expected_passport.yaml under a fake examples root and verify the
    lint exits non-zero. We do this by setting EXAMPLES_ROOT via env
    override (not currently supported), so we instead invoke the
    script with cwd pointing at a synthesized repo layout. Simpler:
    create the bad fixture under the real repo's examples_root in a
    new sub-dir, run, then clean up."""
    # Synthesize a fake adapter dir under the real repo so the
    # script's EXAMPLES_ROOT glob finds it.
    fake_dir = REPO_ROOT / "scripts/adapters/examples/_codex_negative_test"
    fake_dir.mkdir(parents=True, exist_ok=True)
    bad = fake_dir / "expected_passport.yaml"
    bad.write_text(
        "literature_corpus:\n  - citation_key: bad2024\n    "
        "title: T\n    authors:\n      - {}\n    year: 2024\n    "
        "source_pointer: file:///x.pdf\n",
        encoding="utf-8",
    )
    try:
        r = _run([])  # default mode = scan examples
        assert r.returncode != 0
        assert "_codex_negative_test" in r.stderr or "validation" in r.stderr.lower()
    finally:
        bad.unlink(missing_ok=True)
        fake_dir.rmdir()


# --- v3.9.0 contamination_signals (openalex_unmatched + crossref_unmatched) ---

def test_v3_9_0_passes_on_non_manual_with_openalex_and_crossref(tmp_path):
    """v3.9.0 — lint accepts a non-manual entry with all three lookup fields."""
    passport = {
        "literature_corpus": [
            {
                "citation_key": "chen2024",
                "title": "Real Paper",
                "authors": [{"family": "Chen"}],
                "year": 2024,
                "source_pointer": "file:///x.pdf",
                "obtained_via": "folder-scan",
                "contamination_signals": {
                    "preprint_post_llm_inflection": False,
                    "semantic_scholar_unmatched": False,
                    "openalex_unmatched": True,
                    "crossref_unmatched": True,
                },
            }
        ]
    }
    path = _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(path)])
    assert r.returncode == 0, f"stdout={r.stdout}\nstderr={r.stderr}"


def test_v3_9_0_rejects_manual_entry_with_openalex_unmatched(tmp_path):
    """v3.9.0 — lint rejects a manual entry carrying openalex_unmatched (extended not-rule)."""
    passport = {
        "literature_corpus": [
            {
                "citation_key": "manual1",
                "title": "User curated",
                "authors": [{"family": "User"}],
                "year": 2024,
                "source_pointer": "manual:1",
                "obtained_via": "manual",
                "contamination_signals": {
                    "openalex_unmatched": False,
                },
            }
        ]
    }
    path = _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(path)])
    assert r.returncode != 0, (
        f"Expected validation failure for manual entry with openalex_unmatched. "
        f"stdout={r.stdout}\nstderr={r.stderr}"
    )


def _laundering_entry(venue_type_source):
    return {
        "citation_key": "launder2024",
        "title": "Real Paper",
        "authors": [{"family": "Chen"}],
        "year": 2024,
        "source_pointer": "file:///x.pdf",
        "obtained_via": "folder-scan",
        "venue_type": "journal-article",
        "venue_type_provenance": "trusted_source_declared",
        "venue_type_source": venue_type_source,
    }


def test_v3_10_rejects_laundered_venue_type_source(tmp_path):
    """#329: the laundering guard (R2-P1) must run over REAL passport entries, not
    just fixtures. An entry whose venue_type_provenance is trusted_source_declared
    but whose venue_type_source names a lookup index (OpenAlex) is laundering a
    k=3-unmatched signal into a declared-trust signal. The schema only types the
    field as a non-empty string, so this MUST be caught by the wired lint."""
    passport = {"literature_corpus": [_laundering_entry("OpenAlex")]}
    path = _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(path)])
    assert r.returncode != 0, (
        f"Expected validation failure for laundered venue_type_source=OpenAlex. "
        f"stdout={r.stdout}\nstderr={r.stderr}"
    )
    assert "launder" in (r.stdout + r.stderr).lower() or "lookup index" in (r.stdout + r.stderr).lower()


def test_v3_10_accepts_legitimate_declared_venue_type_source(tmp_path):
    """#329 negative control: a trusted_source_declared entry whose venue_type_source
    names a legitimate publisher/registry feed (NOT one of the three lookup indexes)
    passes. Guards against the wired lint over-rejecting every declared source."""
    passport = {"literature_corpus": [_laundering_entry("Springer-publisher-feed")]}
    path = _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(path)])
    assert r.returncode == 0, (
        f"Expected a legitimate declared venue_type_source to pass. "
        f"stdout={r.stdout}\nstderr={r.stderr}"
    )


def test_v3_10_non_string_venue_type_source_reports_schema_error_not_crash(tmp_path):
    """#329 (codex P2): a non-string venue_type_source (123) is a schema-type
    violation. The wired laundering guard calls .strip(), which would crash on a
    non-str. The validator must report the schema error cleanly, NOT traceback —
    the guard is only run on string fields."""
    entry = _laundering_entry("placeholder")
    entry["venue_type_source"] = 123  # schema-invalid: must be a string
    passport = {"literature_corpus": [entry]}
    path = _write_yaml(tmp_path, "passport.yaml", passport)
    r = _run(["--passport", str(path)])
    assert r.returncode != 0
    combined = r.stdout + r.stderr
    assert "Traceback" not in combined and "AttributeError" not in combined, (
        f"validator crashed instead of reporting a schema error: {combined}"
    )
    assert "schema" in combined.lower() or "validation" in combined.lower()
