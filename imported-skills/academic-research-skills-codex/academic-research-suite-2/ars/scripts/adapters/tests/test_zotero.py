"""Tests for scripts/adapters/zotero.py."""
from pathlib import Path
import subprocess
import sys
import json

REPO_ROOT = Path(__file__).resolve().parents[3]
ADAPTER = REPO_ROOT / "scripts/adapters/zotero.py"
FIXTURE_INPUT = REPO_ROOT / "scripts/adapters/examples/zotero/input_fixture/export.json"
EXPECTED_PASSPORT = REPO_ROOT / "scripts/adapters/examples/zotero/expected_passport.yaml"
EXPECTED_REJECTION = REPO_ROOT / "scripts/adapters/examples/zotero/expected_rejection_log.yaml"


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
    res = _run("--input", str(FIXTURE_INPUT), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0, res.stderr
    assert clean_timestamps(load_yaml(p)) == clean_timestamps(load_yaml(EXPECTED_PASSPORT))
    assert clean_timestamps(load_yaml(r)) == clean_timestamps(load_yaml(EXPECTED_REJECTION))


def test_malformed_json_fails_loud(tmp_path):
    bad = tmp_path / "bad.json"
    bad.write_text("{not json", encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(bad), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 1
    assert "json" in res.stderr.lower() or "parse" in res.stderr.lower()


def test_empty_array_emits_empty_passport(tmp_path, load_yaml):
    empty = tmp_path / "empty.json"
    empty.write_text("[]", encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(empty), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    doc = load_yaml(p)
    assert doc == {"literature_corpus": []}


def test_institution_author_preserved(tmp_path, load_yaml):
    data = [
        {
            "citationKey": "who2024",
            "itemType": "report",
            "title": "World report",
            "creators": [{"creatorType": "author", "name": "World Health Organization"}],
            "date": "2024",
            "itemID": "AAAA1111",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    doc = load_yaml(p)
    assert doc["literature_corpus"][0]["authors"] == [{"literal": "World Health Organization"}]


def test_no_authors_rejected(tmp_path, load_yaml):
    data = [
        {
            "citationKey": "anon2024",
            "itemType": "journalArticle",
            "title": "Untitled",
            "creators": [{"creatorType": "editor", "firstName": "A", "lastName": "B"}],
            "date": "2024",
            "itemID": "BBBB1111",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == []
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "authors_unparseable"


def test_unparseable_date_rejected(tmp_path, load_yaml):
    data = [
        {
            "citationKey": "fwd2024",
            "itemType": "journalArticle",
            "title": "Forthcoming",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "forthcoming",
            "itemID": "CCCC1111",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    rr = load_yaml(r)
    assert rr["rejected"][0]["reason"] == "year_unparseable"


# ---------------------------------------------------------------------------
# P1 — schema-violating empty values
# ---------------------------------------------------------------------------

def test_blank_corporate_author_rejected(tmp_path, load_yaml):
    """Blank literal author (name='') must be rejected, not emit literal: ''."""
    data = [
        {
            "citationKey": "blank_corp2024",
            "itemType": "report",
            "title": "Some report",
            "creators": [{"creatorType": "author", "name": "   "}],
            "date": "2024",
            "itemID": "ZZZZ0001",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == [], "blank corporate author must not reach passport"
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "missing_required_field"
    assert "authors" in rr["rejected"][0]["missing_fields"]


def test_missing_title_rejected(tmp_path, load_yaml):
    """Item without a title must be rejected with missing_required_field."""
    data = [
        {
            "citationKey": "notitle2024",
            "itemType": "journalArticle",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "2024",
            "itemID": "ZZZZ0002",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == [], "missing title must not reach passport"
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "missing_required_field"
    assert "title" in rr["rejected"][0]["missing_fields"]


def test_missing_citation_key_rejected(tmp_path, load_yaml):
    """Item without citationKey and without key must be rejected."""
    data = [
        {
            "itemType": "journalArticle",
            "title": "No citekey paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "2024",
            "itemID": "ZZZZ0003",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == [], "missing citationKey must not reach passport"
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "missing_required_field"
    assert "citation_key" in rr["rejected"][0]["missing_fields"]


# ---------------------------------------------------------------------------
# P2-A — duplicate citekey handling
# ---------------------------------------------------------------------------

def test_duplicate_citekey_disambiguated(tmp_path, load_yaml):
    """Two items with the same citationKey must both be accepted with suffixed keys."""
    data = [
        {
            "citationKey": "smith2024",
            "itemType": "journalArticle",
            "title": "First paper",
            "creators": [{"creatorType": "author", "firstName": "Alice", "lastName": "Smith"}],
            "date": "2024",
            "itemID": "DUP10001",
        },
        {
            "citationKey": "smith2024",
            "itemType": "journalArticle",
            "title": "Second paper",
            "creators": [{"creatorType": "author", "firstName": "Alice", "lastName": "Smith"}],
            "date": "2024",
            "itemID": "DUP10002",
        },
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    entries = pp["literature_corpus"]
    assert len(entries) == 2, "both items must be accepted"
    keys = {e["citation_key"] for e in entries}
    assert len(keys) == 2, f"citation keys must be unique, got: {keys}"
    # first item keeps original key, second gets a suffix
    assert "smith2024" in keys
    assert any(k.startswith("smith2024") and k != "smith2024" for k in keys)


# ---------------------------------------------------------------------------
# P2-B — issued fallback + seasonal date rejection + source_pointer contract
# ---------------------------------------------------------------------------

def test_issued_fallback_no_date_field(tmp_path, load_yaml):
    """Item with only `issued` (no `date`) must resolve year from issued."""
    data = [
        {
            "citationKey": "issued2023",
            "itemType": "journalArticle",
            "title": "Issued-only paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "issued": {"date-parts": [[2023]]},
            "itemID": "ISS10001",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    entries = pp["literature_corpus"]
    assert len(entries) == 1
    assert entries[0]["year"] == 2023


def test_issued_as_string_fallback(tmp_path, load_yaml):
    """Item with `issued` as string (no `date`) must resolve year from issued string."""
    data = [
        {
            "citationKey": "issued2022",
            "itemType": "journalArticle",
            "title": "Issued string paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "issued": "2022-06-15",
            "itemID": "ISS10002",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    entries = pp["literature_corpus"]
    assert len(entries) == 1
    assert entries[0]["year"] == 2022


def test_seasonal_date_rejected(tmp_path, load_yaml):
    """'Spring 2024' must be rejected — seasonal strings are not valid dates."""
    data = [
        {
            "citationKey": "spring2024",
            "itemType": "journalArticle",
            "title": "Spring paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "Spring 2024",
            "itemID": "SEA10001",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == [], "seasonal date must not reach passport"
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "year_unparseable"


def test_nd_date_rejected(tmp_path, load_yaml):
    """'n.d.' (no date) must be rejected."""
    data = [
        {
            "citationKey": "nodate2024",
            "itemType": "journalArticle",
            "title": "No date paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "n.d.",
            "itemID": "ND100001",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == [], "n.d. date must not reach passport"
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "year_unparseable"


def test_missing_source_pointer_rejected(tmp_path, load_yaml):
    """Item with neither itemID nor key must be rejected (no valid source_pointer)."""
    data = [
        {
            "citationKey": "noptr2024",
            "itemType": "journalArticle",
            "title": "No pointer paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "2024",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == [], "item without source_pointer must not reach passport"
    assert len(rr["rejected"]) == 1
    assert rr["rejected"][0]["reason"] == "missing_required_field"
    assert "source_pointer" in rr["rejected"][0]["missing_fields"]


def test_zotero_key_used_as_source_pointer(tmp_path, load_yaml):
    """Item with Zotero `key` (8-char) but no itemID uses key as source_pointer."""
    data = [
        {
            "citationKey": "keyonly2024",
            "itemType": "journalArticle",
            "title": "Key-only paper",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "2024",
            "key": "ABCD1234",
        }
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    entries = pp["literature_corpus"]
    assert len(entries) == 1
    # source_pointer must use the Zotero key, not @citekey
    assert entries[0]["source_pointer"] == "zotero://select/items/ABCD1234"
    assert "@" not in entries[0]["source_pointer"]


# ---------------------------------------------------------------------------
# P3 — all-rejected corpus
# ---------------------------------------------------------------------------

def test_all_rejected_corpus(tmp_path, load_yaml):
    """When every item is rejected, passport must be empty and rejection_log populated."""
    data = [
        {
            "citationKey": "noauth2024",
            "itemType": "journalArticle",
            "title": "No author",
            "creators": [],
            "date": "2024",
            "itemID": "AR100001",
        },
        {
            "citationKey": "noyr2024",
            "itemType": "journalArticle",
            "title": "No year",
            "creators": [{"creatorType": "author", "firstName": "A", "lastName": "B"}],
            "date": "forthcoming",
            "itemID": "AR100002",
        },
    ]
    infile = tmp_path / "i.json"
    infile.write_text(json.dumps(data), encoding="utf-8")
    p = tmp_path / "p.yaml"
    r = tmp_path / "r.yaml"
    res = _run("--input", str(infile), "--passport", str(p), "--rejection-log", str(r))
    assert res.returncode == 0
    pp = load_yaml(p)
    rr = load_yaml(r)
    assert pp["literature_corpus"] == []
    assert rr["summary"]["total_rejected"] == 2


# --- v3.10 venue_type mapping (spec §3 PR-B item 13) ---

def _import_zotero():
    import importlib.util
    spec = importlib.util.spec_from_file_location("zotero_adapter", ADAPTER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_zotero_map_venue_type_known_types():
    z = _import_zotero()
    assert z.map_venue_type("journalArticle") == ("journal-article", "adapter_declared")
    assert z.map_venue_type("conferencePaper") == ("conference-paper", "adapter_declared")
    assert z.map_venue_type("book") == ("book", "adapter_declared")
    assert z.map_venue_type("thesis") == ("dissertation", "adapter_declared")


def test_zotero_map_venue_type_unknown_and_absent():
    z = _import_zotero()
    # Unknown item type → unknown/unknown (honors pair invariant; never guessed).
    assert z.map_venue_type("blogPost") == ("unknown", "unknown")
    assert z.map_venue_type(None) == ("unknown", "unknown")
    assert z.map_venue_type("") == ("unknown", "unknown")
