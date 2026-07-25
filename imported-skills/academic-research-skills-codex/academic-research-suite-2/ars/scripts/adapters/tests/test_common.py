"""Tests for the shared helpers used by every reference adapter."""
from pathlib import Path
import yaml

from scripts.adapters._common import (
    sanitize_citation_key,
    make_citation_key,
    ensure_unique_citekey,
    parse_csl_name,
    parse_semicolon_names,
    dump_yaml_stable,
    now_iso,
    path_to_file_uri,
    write_passport,
    write_rejection_log,
    ADAPTER_SPEC_VERSION,
)


# --- sanitize_citation_key ---

def test_sanitize_strips_non_alnum():
    assert sanitize_citation_key("Chen, 2024!") == "Chen2024"


def test_sanitize_does_not_lowercase():
    assert sanitize_citation_key("CHEN2024") == "CHEN2024"


def test_sanitize_rejects_empty():
    assert sanitize_citation_key("!!!") == ""


# --- make_citation_key ---

def test_make_citation_key_simple():
    existing: set[str] = set()
    key = make_citation_key(
        family="Chen", year=2024, title_hint="AI assessment", existing=existing
    )
    assert key == "chen2024ai"
    assert "chen2024ai" in existing


def test_make_citation_key_collision_suffix():
    existing: set[str] = {"chen2024ai"}
    key = make_citation_key(
        family="Chen", year=2024, title_hint="AI analysis", existing=existing
    )
    assert key == "chen2024aia"


def test_make_citation_key_multiple_collisions():
    existing: set[str] = {"chen2024", "chen2024a", "chen2024b"}
    key = make_citation_key(
        family="Chen", year=2024, title_hint=None, existing=existing
    )
    assert key == "chen2024c"


def test_make_citation_key_empty_family_falls_back_to_ref():
    """family="" + year=0 + no title → sanitized base is "0".
    Codex T4-review P2: this exercises the digit-start branch
    (base[0] is '0' which is not alpha), not the empty-base branch."""
    existing: set[str] = set()
    key = make_citation_key(family="", year=0, title_hint=None, existing=existing)
    assert key == "ref"
    # second call collides → ref + suffix 'a'
    key2 = make_citation_key(family="", year=0, title_hint=None, existing=existing)
    assert key2 == "refa"


def test_make_citation_key_digit_start_falls_back_to_ref():
    """Pure digit base (e.g. family="" + year=2024) violates schema
    citation_key pattern ^[A-Za-z]... — must fall back to 'ref'.
    This is the explicit case the T5 deviation was designed for."""
    existing: set[str] = set()
    key = make_citation_key(family="", year=2024, title_hint=None, existing=existing)
    assert key == "ref"
    # Confirm the fallback respects collision tracking too.
    existing2: set[str] = {"ref"}
    key2 = make_citation_key(
        family="", year=2024, title_hint=None, existing=existing2
    )
    assert key2 == "refa"


def test_make_citation_key_digit_start_with_title_recovers():
    """If a title_hint provides a leading-alpha word, no fallback needed."""
    existing: set[str] = set()
    key = make_citation_key(
        family="", year=2024, title_hint="formative feedback", existing=existing
    )
    # base = "" + "2024" + "formative" → "2024formative" → still digit-start
    # because title is appended after the year, so fallback fires.
    assert key == "ref"


def test_make_citation_key_skips_stopwords_in_title():
    existing: set[str] = set()
    key = make_citation_key(
        family="Chen", year=2024, title_hint="The role of AI", existing=existing
    )
    # 'The' is a stopword, first non-stopword is 'role'
    assert key == "chen2024role"


# --- parse_csl_name ---

def test_parse_csl_name_family_given():
    assert parse_csl_name("Chen, Cindy") == {"family": "Chen", "given": "Cindy"}


def test_parse_csl_name_family_initial():
    assert parse_csl_name("Chen, C.") == {"family": "Chen", "given": "C."}


def test_parse_csl_name_institution_with_braces():
    assert parse_csl_name("{World Health Organization}") == {
        "literal": "World Health Organization"
    }


def test_parse_csl_name_bare_single_token_is_family():
    assert parse_csl_name("Einstein") == {"family": "Einstein"}


def test_parse_csl_name_strips_whitespace():
    assert parse_csl_name("  Chen ,  Cindy  ") == {"family": "Chen", "given": "Cindy"}


# --- parse_semicolon_names ---

def test_parse_semicolon_names():
    names = parse_semicolon_names("Chen, C.; Wang, J.")
    assert names == [
        {"family": "Chen", "given": "C."},
        {"family": "Wang", "given": "J."},
    ]


def test_parse_semicolon_names_empty_returns_empty_list():
    assert parse_semicolon_names("") == []
    assert parse_semicolon_names("   ") == []


def test_parse_semicolon_names_skips_empty_segments():
    """Trailing or duplicate semicolons should not produce empty name dicts."""
    names = parse_semicolon_names("Chen, C.;;Wang, J.;")
    assert names == [
        {"family": "Chen", "given": "C."},
        {"family": "Wang", "given": "J."},
    ]


# --- dump_yaml_stable / now_iso ---

def test_dump_yaml_stable_is_sorted():
    data = {"b": 2, "a": 1}
    out = dump_yaml_stable(data)
    assert out.index("a:") < out.index("b:")


def test_dump_yaml_stable_is_deterministic():
    data = {"b": [3, 1, 2], "a": {"y": 2, "x": 1}}
    a = dump_yaml_stable(data)
    b = dump_yaml_stable(data)
    assert a == b


def test_now_iso_is_rfc3339_z():
    ts = now_iso()
    assert ts.endswith("Z")
    assert "T" in ts
    # round-trip through datetime
    import datetime
    parsed = datetime.datetime.strptime(ts, "%Y-%m-%dT%H:%M:%SZ")
    assert parsed is not None


def test_adapter_spec_version_is_string():
    assert isinstance(ADAPTER_SPEC_VERSION, str)
    assert ADAPTER_SPEC_VERSION


# --- write_passport ---

def test_write_passport_sorts_by_citation_key(tmp_path: Path):
    entries = [
        {"citation_key": "wang2024", "title": "W", "authors": [{"family": "Wang"}],
         "year": 2024, "source_pointer": "file:///w.pdf"},
        {"citation_key": "chen2024", "title": "C", "authors": [{"family": "Chen"}],
         "year": 2024, "source_pointer": "file:///c.pdf"},
    ]
    p = tmp_path / "passport.yaml"
    write_passport(p, entries)
    loaded = yaml.safe_load(p.read_text())
    keys = [e["citation_key"] for e in loaded["literature_corpus"]]
    assert keys == ["chen2024", "wang2024"]


def test_write_passport_empty_list(tmp_path: Path):
    p = tmp_path / "passport.yaml"
    write_passport(p, [])
    loaded = yaml.safe_load(p.read_text())
    assert loaded == {"literature_corpus": []}


# --- write_rejection_log ---

def test_write_rejection_log_minimal(tmp_path: Path):
    p = tmp_path / "rejection_log.yaml"
    write_rejection_log(
        p,
        adapter_name="folder_scan.py",
        adapter_version="1.0.0",
        rejected=[],
    )
    loaded = yaml.safe_load(p.read_text())
    assert loaded["adapter_name"] == "folder_scan.py"
    assert loaded["adapter_version"] == "1.0.0"
    assert loaded["rejected"] == []
    assert loaded["generated_at"].endswith("Z")
    assert loaded["summary"]["total_rejected"] == 0


def test_write_rejection_log_sorts_by_source(tmp_path: Path):
    p = tmp_path / "rejection_log.yaml"
    write_rejection_log(
        p,
        adapter_name="x",
        adapter_version="1",
        rejected=[
            {"source": "z.pdf", "reason": "authors_unparseable"},
            {"source": "a.pdf", "reason": "year_unparseable"},
        ],
    )
    loaded = yaml.safe_load(p.read_text())
    sources = [r["source"] for r in loaded["rejected"]]
    assert sources == ["a.pdf", "z.pdf"]


def test_write_rejection_log_passes_validation(tmp_path: Path):
    """Output must validate against rejection_log.schema.json — i.e. the
    helper produces a doc that is contract-compliant by construction."""
    import json
    from jsonschema import Draft202012Validator
    schema_path = (
        Path(__file__).resolve().parents[3]
        / "shared/contracts/passport/rejection_log.schema.json"
    )
    schema = json.loads(schema_path.read_text())
    validator = Draft202012Validator(
        schema, format_checker=Draft202012Validator.FORMAT_CHECKER
    )
    p = tmp_path / "rejection_log.yaml"
    write_rejection_log(
        p,
        adapter_name="zotero.py",
        adapter_version="1.0.0",
        rejected=[{"source": "ABCD1234", "reason": "missing_required_field",
                   "missing_fields": ["authors"]}],
        input_source="/path/to/lib",
    )
    doc = yaml.safe_load(p.read_text())
    errors = list(validator.iter_errors(doc))
    assert errors == [], f"helper output failed schema: {[e.message for e in errors]}"


def test_write_rejection_log_with_input_source(tmp_path: Path):
    p = tmp_path / "rejection_log.yaml"
    write_rejection_log(
        p,
        adapter_name="x",
        adapter_version="1",
        rejected=[],
        input_source="/path/to/refs",
    )
    loaded = yaml.safe_load(p.read_text())
    assert loaded["input_source"] == "/path/to/refs"


def test_write_rejection_log_with_summary_totals(tmp_path: Path):
    """When the caller knows accept/input counts, helper should propagate
    them into summary so it tells the full story."""
    p = tmp_path / "rejection_log.yaml"
    write_rejection_log(
        p,
        adapter_name="x",
        adapter_version="1",
        rejected=[
            {"source": "a", "reason": "year_unparseable"},
            {"source": "b", "reason": "authors_unparseable"},
        ],
        total_input=10,
        total_accepted=8,
    )
    loaded = yaml.safe_load(p.read_text())
    assert loaded["summary"] == {
        "total_input": 10,
        "total_accepted": 8,
        "total_rejected": 2,
    }


# --- path_to_file_uri ---

def test_path_to_file_uri_encodes_spaces(tmp_path: Path):
    p = tmp_path / "Lee 2024 paper.pdf"
    p.touch()
    uri = path_to_file_uri(p)
    assert uri.startswith("file://")
    assert " " not in uri
    assert "%20" in uri


def test_path_to_file_uri_resolves_relative(tmp_path: Path, monkeypatch):
    p = tmp_path / "Smith2024.pdf"
    p.touch()
    monkeypatch.chdir(tmp_path)
    uri = path_to_file_uri("Smith2024.pdf")
    assert uri.endswith("Smith2024.pdf")
    assert uri.startswith("file://")
    # absolute, not relative
    assert "://./" not in uri


def test_path_to_file_uri_accepts_string():
    # The helper accepts both Path and str inputs.
    p = Path(__file__)
    assert path_to_file_uri(str(p)) == path_to_file_uri(p)


# --- ensure_unique_citekey ---

def test_ensure_unique_citekey_passes_through_unique():
    existing: set[str] = set()
    assert ensure_unique_citekey("smith2024", existing) == "smith2024"
    assert "smith2024" in existing


def test_ensure_unique_citekey_disambiguates_duplicates():
    existing = {"smith2024"}
    out = ensure_unique_citekey("smith2024", existing)
    assert out == "smith2024a"
    assert out in existing
    # second collision keeps incrementing
    assert ensure_unique_citekey("smith2024", existing) == "smith2024b"


def test_ensure_unique_citekey_normalizes_invalid_base():
    # Schema requires ^[A-Za-z]; bases that don't satisfy it (empty,
    # leading digit, leading punctuation) must be sanitized + prefixed
    # so the returned key always passes the citation_key pattern.
    assert ensure_unique_citekey("", set()) == "ref"
    assert ensure_unique_citekey("2024paper", set()).startswith("ref")
    assert ensure_unique_citekey("@key2024", set())[0].isalpha()


def test_ensure_unique_citekey_strips_disallowed_chars():
    # Schema pattern: ^[A-Za-z][A-Za-z0-9_:-]*$. Spaces and other punct
    # are stripped so the result satisfies the pattern.
    out = ensure_unique_citekey("Smith Jones 2024!", set())
    assert all(c.isalnum() or c in "_:-" for c in out)
    assert out[0].isalpha()
