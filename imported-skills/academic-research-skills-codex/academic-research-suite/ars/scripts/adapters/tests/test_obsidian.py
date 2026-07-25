"""Tests for scripts/adapters/obsidian.py."""
from pathlib import Path
import subprocess
import sys
import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
ADAPTER = REPO_ROOT / "scripts/adapters/obsidian.py"
VAULT = REPO_ROOT / "scripts/adapters/examples/obsidian/input_fixture/vault"
EXPECTED_PASSPORT = REPO_ROOT / "scripts/adapters/examples/obsidian/expected_passport.yaml"
EXPECTED_REJECTION = REPO_ROOT / "scripts/adapters/examples/obsidian/expected_rejection_log.yaml"


def _run(*args):
    return subprocess.run(
        [sys.executable, str(ADAPTER)] + list(args),
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )


def test_adapter_exists():
    assert ADAPTER.exists()


def test_happy_path(tmp_path, load_yaml, clean_timestamps):
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(VAULT), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0, res.stderr
    assert clean_timestamps(load_yaml(p)) == clean_timestamps(load_yaml(EXPECTED_PASSPORT))
    assert clean_timestamps(load_yaml(r)) == clean_timestamps(load_yaml(EXPECTED_REJECTION))


def test_missing_vault_fails_loud(tmp_path):
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(tmp_path / "nope"), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 1


def test_templates_dir_skipped(tmp_path, load_yaml):
    vault = tmp_path / "v"
    (vault / "_templates").mkdir(parents=True)
    (vault / "_templates/tmpl.md").write_text(
        "---\ncitekey: tmpl2024\ntitle: T\nauthors:\n  - family: X\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    (vault / "note.md").write_text(
        "---\ncitekey: note2024\ntitle: Real\nauthors:\n  - family: Y\nyear: 2024\n---\nbody\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    doc = load_yaml(p)
    keys = [e["citation_key"] for e in doc["literature_corpus"]]
    assert "tmpl2024" not in keys
    assert "note2024" in keys


def test_obsidian_dir_skipped(tmp_path, load_yaml):
    vault = tmp_path / "v"
    (vault / ".obsidian").mkdir(parents=True)
    (vault / ".obsidian/ignored.md").write_text(
        "---\ncitekey: skip2024\ntitle: T\nauthors:\n  - family: X\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    (vault / "real.md").write_text(
        "---\ncitekey: real2024\ntitle: R\nauthors:\n  - family: Y\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    doc = load_yaml(p)
    keys = [e["citation_key"] for e in doc["literature_corpus"]]
    assert "skip2024" not in keys
    assert "real2024" in keys


def test_convention_a_source_pointer_is_obsidian_uri(tmp_path, load_yaml):
    """source_pointer for Convention A must be an obsidian:// URI (deterministic, not file://)."""
    vault = tmp_path / "myvault"
    vault.mkdir()
    (vault / "paper.md").write_text(
        "---\ncitekey: smith2024\ntitle: A Study\nauthors:\n  - family: Smith\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0, res.stderr
    doc = load_yaml(p)
    entry = doc["literature_corpus"][0]
    assert entry["source_pointer"].startswith("obsidian://open?vault=")
    assert "myvault" in entry["source_pointer"]
    assert "paper" in entry["source_pointer"]


def test_convention_b_source_pointer_is_obsidian_uri(tmp_path, load_yaml):
    """source_pointer for Convention B (Karpathy-style) must also be obsidian:// URI."""
    vault = tmp_path / "mybvault"
    vault.mkdir()
    (vault / "jones2022review.md").write_text(
        "---\nsource: https://doi.org/10.999/abc\n---\n\n# Review of methods\n\n**Authors**: Jones, A.\n**Year**: 2022\n\nContent.\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0, res.stderr
    doc = load_yaml(p)
    entry = doc["literature_corpus"][0]
    assert entry["source_pointer"].startswith("obsidian://open?vault=")
    assert "mybvault" in entry["source_pointer"]


def test_deterministic_output(tmp_path, load_yaml, clean_timestamps):
    p1 = tmp_path / "p1.yaml"
    r1 = tmp_path / "r1.yaml"
    p2 = tmp_path / "p2.yaml"
    r2 = tmp_path / "r2.yaml"
    _run("--input", str(VAULT), "--passport", str(p1), "--rejection-log", str(r1))
    _run("--input", str(VAULT), "--passport", str(p2), "--rejection-log", str(r2))
    assert clean_timestamps(load_yaml(p1)) == clean_timestamps(load_yaml(p2))
    assert clean_timestamps(load_yaml(r1)) == clean_timestamps(load_yaml(r2))


# ---------------------------------------------------------------------------
# P1 — year coercion + authors type validation
# ---------------------------------------------------------------------------

def test_year_leading_4_digit_string_accepted(tmp_path, load_yaml):
    """Convention A: year='2024-01' (leading-year string) is accepted; year extracted as 2024."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "leading_year.md").write_text(
        "---\ncitekey: leading2024\ntitle: T\nauthors:\n  - family: Smith\nyear: '2024-01'\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert len(passport["literature_corpus"]) == 1
    assert passport["literature_corpus"][0]["year"] == 2024


def test_year_unparseable_is_rejected(tmp_path, load_yaml):
    """Convention A: year='not-a-year' (non-numeric string) must be rejected with year_unparseable."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "bad_year.md").write_text(
        "---\ncitekey: bad2024\ntitle: T\nauthors:\n  - family: Smith\nyear: 'unknown'\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert passport["literature_corpus"] == []
    rejection = load_yaml(r)
    assert len(rejection["rejected"]) == 1
    assert rejection["rejected"][0]["reason"] == "year_unparseable"
    assert rejection["rejected"][0]["source"] == "bad_year.md"


def test_authors_string_parsed_via_semicolon(tmp_path, load_yaml):
    """Convention A: authors as a bare string 'Smith, J; Lee, K' must be parsed into CSL list."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "str_authors.md").write_text(
        "---\ncitekey: smith2024\ntitle: A Study\nauthors: 'Smith, J; Lee, K'\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert len(passport["literature_corpus"]) == 1
    authors = passport["literature_corpus"][0]["authors"]
    assert isinstance(authors, list)
    assert authors[0]["family"] == "Smith"
    assert authors[1]["family"] == "Lee"


def test_authors_wrong_type_is_rejected(tmp_path, load_yaml):
    """Convention A: authors=42 (invalid type) must be rejected with authors_unparseable."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "bad_authors.md").write_text(
        "---\ncitekey: bad2024\ntitle: T\nauthors: 42\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert passport["literature_corpus"] == []
    rejection = load_yaml(r)
    assert len(rejection["rejected"]) == 1
    assert rejection["rejected"][0]["reason"] == "authors_unparseable"


# ---------------------------------------------------------------------------
# P2-A — duplicate citekey disambiguation
# ---------------------------------------------------------------------------

def test_duplicate_citekey_convention_a_disambiguated(tmp_path, load_yaml):
    """Two Convention A notes with identical citekeys must both be accepted with suffix disambiguation."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "note1.md").write_text(
        "---\ncitekey: smith2024\ntitle: First Paper\nauthors:\n  - family: Smith\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    (vault / "note2.md").write_text(
        "---\ncitekey: smith2024\ntitle: Second Paper\nauthors:\n  - family: Smith\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert len(passport["literature_corpus"]) == 2
    keys = {e["citation_key"] for e in passport["literature_corpus"]}
    assert "smith2024" in keys
    assert "smith2024a" in keys


# ---------------------------------------------------------------------------
# P2-B — malformed YAML frontmatter
# ---------------------------------------------------------------------------

def test_malformed_yaml_frontmatter_rejected(tmp_path, load_yaml):
    """File starting with '---' but containing invalid YAML must be rejected, not fall through to Convention B."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "malformed.md").write_text(
        "---\nbad: [unclosed\n---\nbody content here\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert passport["literature_corpus"] == []
    rejection = load_yaml(r)
    assert len(rejection["rejected"]) == 1
    rej = rejection["rejected"][0]
    assert rej["reason"] in ("invalid_field_format", "adapter_error")
    assert rej["source"] == "malformed.md"


# ---------------------------------------------------------------------------
# P3 — additional coverage
# ---------------------------------------------------------------------------

def test_empty_file_rejected(tmp_path, load_yaml):
    """Empty .md file must be rejected (no frontmatter, no body, no title/authors/year)."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "empty.md").write_text("", encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert passport["literature_corpus"] == []
    rejection = load_yaml(r)
    assert len(rejection["rejected"]) == 1


def test_empty_frontmatter_only_rejected(tmp_path, load_yaml):
    """File with only '---\\n---\\n' (empty frontmatter, no body) must be rejected."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "empty_fm.md").write_text("---\n---\n", encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert passport["literature_corpus"] == []


def test_source_pointer_url_encoding_for_spaces(tmp_path, load_yaml):
    """Vault name and filename with spaces must produce valid percent-encoded obsidian:// URI."""
    vault = tmp_path / "My KB"
    vault.mkdir()
    (vault / "Chen 2024.md").write_text(
        "---\ncitekey: chen2024\ntitle: A Study\nauthors:\n  - family: Chen\nyear: 2024\n---\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    entry = passport["literature_corpus"][0]
    assert "My%20KB" in entry["source_pointer"]
    assert "Chen%202024" in entry["source_pointer"]
    assert " " not in entry["source_pointer"]


def test_all_rejected_corpus_produces_empty_passport(tmp_path, load_yaml):
    """All-rejected corpus: passport has empty literature_corpus, rejection_log is populated."""
    vault = tmp_path / "v"
    vault.mkdir()
    (vault / "only_invalid.md").write_text(
        "This file has no frontmatter and no parseable structure.\n",
        encoding="utf-8",
    )
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(vault), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    passport = load_yaml(p)
    assert passport["literature_corpus"] == []
    rejection = load_yaml(r)
    assert len(rejection["rejected"]) >= 1
    assert rejection["summary"]["total_rejected"] >= 1


# --- v3.10 venue_type frontmatter declaration (spec §3 PR-B item 13) ---

def _import_obsidian():
    import importlib.util
    spec = importlib.util.spec_from_file_location("obsidian_adapter", ADAPTER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_obsidian_declare_venue_type_valid_frontmatter():
    o = _import_obsidian()
    assert o.declare_venue_type({"venue_type": "journal-article"}) == ("journal-article", "user_declared")
    assert o.declare_venue_type({"venue_type": "dissertation"}) == ("dissertation", "user_declared")


def test_obsidian_declare_venue_type_invalid_or_absent():
    o = _import_obsidian()
    # Invalid enum value → unknown/unknown (never guessed).
    assert o.declare_venue_type({"venue_type": "not-a-real-type"}) == ("unknown", "unknown")
    # Absent → unknown/unknown.
    assert o.declare_venue_type({}) == ("unknown", "unknown")
    assert o.declare_venue_type(None) == ("unknown", "unknown")
    # Explicit unknown → unknown/unknown (provenance unknown, not user_declared).
    assert o.declare_venue_type({"venue_type": "unknown"}) == ("unknown", "unknown")
