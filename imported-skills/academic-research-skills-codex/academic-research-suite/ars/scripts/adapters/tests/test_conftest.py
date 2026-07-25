"""Self-tests for the shared adapter test fixtures.

T7-T9 will use clean_timestamps and load_yaml extensively, so verify
their behavior here before downstream tests depend on them.
"""
from pathlib import Path


def test_repo_root_points_to_ars_repo(repo_root):
    """Sanity: the fixture must resolve to a directory that contains the
    canonical ARS markers (CHANGELOG.md and shared/ live at root)."""
    assert (repo_root / "CHANGELOG.md").exists()
    assert (repo_root / "shared").is_dir()


def test_adapters_dir_resolves(adapters_dir, repo_root):
    assert adapters_dir == repo_root / "scripts/adapters"
    assert adapters_dir.is_dir()


def test_examples_dir_resolves(examples_dir, repo_root):
    assert examples_dir == repo_root / "scripts/adapters/examples"
    assert examples_dir.is_dir()


# --- clean_timestamps ---

def test_clean_timestamps_blanks_top_level_field(clean_timestamps):
    doc = {"generated_at": "2026-04-25T10:00:00Z", "x": 1}
    out = clean_timestamps(doc)
    assert out == {"generated_at": "<TIMESTAMP>", "x": 1}


def test_clean_timestamps_blanks_nested_obtained_at(clean_timestamps):
    doc = {
        "literature_corpus": [
            {"citation_key": "k1", "obtained_at": "2026-04-25T10:00:00Z"},
            {"citation_key": "k2", "obtained_at": "2026-04-25T10:01:00Z"},
        ]
    }
    out = clean_timestamps(doc)
    assert out["literature_corpus"][0]["obtained_at"] == "<TIMESTAMP>"
    assert out["literature_corpus"][1]["obtained_at"] == "<TIMESTAMP>"


def test_clean_timestamps_does_not_mutate_input(clean_timestamps):
    """Deep-copy contract: caller's dict must remain unchanged after the
    cleaner runs. T7-T9 will call this on freshly-loaded YAML and expect
    to inspect the original timestamps afterward."""
    original = {"generated_at": "2026-04-25T10:00:00Z", "x": 1}
    snapshot = {**original}
    _ = clean_timestamps(original)
    assert original == snapshot


def test_clean_timestamps_leaves_unrelated_fields_alone(clean_timestamps):
    doc = {"generated_at": "X", "summary": {"total_rejected": 5}}
    out = clean_timestamps(doc)
    assert out["summary"] == {"total_rejected": 5}


def test_clean_timestamps_handles_lists_of_scalars(clean_timestamps):
    """Recursion guard: hitting a list of non-dicts must not crash."""
    doc = {"tags": ["a", "b", "c"], "obtained_at": "X"}
    out = clean_timestamps(doc)
    assert out == {"tags": ["a", "b", "c"], "obtained_at": "<TIMESTAMP>"}


def test_clean_timestamps_handles_no_match(clean_timestamps):
    """Doc with no timestamp keys must round-trip unchanged in value
    (deep copy still happens)."""
    doc = {"x": 1, "y": [1, 2, 3]}
    out = clean_timestamps(doc)
    assert out == doc
    assert out is not doc


def test_clean_timestamps_extra_blank_widens_set(clean_timestamps):
    """folder_scan-style adapters whose source_pointer is a machine-
    dependent absolute path must opt in to widen the blanking set; T8/T9
    keep the default narrow behavior so broken URIs fail loudly."""
    doc = {"obtained_at": "X", "source_pointer": "/abs/path", "year": 2024}
    narrow = clean_timestamps(doc)
    assert narrow["source_pointer"] == "/abs/path"  # not blanked by default
    wide = clean_timestamps(doc, {"source_pointer"})
    assert wide["source_pointer"] == "<TIMESTAMP>"
    # narrow output unaffected by the wide call (no shared-state surprises)
    assert narrow["source_pointer"] == "/abs/path"


# --- load_yaml ---

def test_load_yaml_round_trips(load_yaml, tmp_path: Path):
    p = tmp_path / "x.yaml"
    p.write_text("a: 1\nb:\n  - 2\n  - 3\n", encoding="utf-8")
    assert load_yaml(p) == {"a": 1, "b": [2, 3]}
