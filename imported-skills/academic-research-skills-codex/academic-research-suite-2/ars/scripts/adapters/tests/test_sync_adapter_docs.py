"""Tests for sync_adapter_docs.py: schema → overview.md drift detector."""
from pathlib import Path
import subprocess
import sys

REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "scripts/sync_adapter_docs.py"
OVERVIEW = REPO_ROOT / "academic-pipeline/references/adapters/overview.md"


def _run(*args):
    return subprocess.run(
        [sys.executable, str(SCRIPT)] + list(args),
        capture_output=True,
        text=True,
        cwd=REPO_ROOT,
    )


def test_script_exists():
    assert SCRIPT.exists()


def test_regenerate_is_idempotent(tmp_path):
    # First, run without --check to regenerate in place
    r1 = _run()
    assert r1.returncode == 0, r1.stderr
    # Running --check after regeneration must succeed (no drift)
    r2 = _run("--check")
    assert r2.returncode == 0, r2.stderr


def test_check_detects_drift(tmp_path):
    # Save current overview content, deliberately corrupt a generated section,
    # verify --check exits non-zero, then restore.
    original = OVERVIEW.read_text(encoding="utf-8")
    try:
        marker_start = "<!-- GENERATED:LITERATURE_CORPUS_REQUIRED:START -->"
        marker_end = "<!-- GENERATED:LITERATURE_CORPUS_REQUIRED:END -->"
        i = original.index(marker_start)
        j = original.index(marker_end) + len(marker_end)
        corrupted = (
            original[:i]
            + marker_start
            + "\nDELIBERATELY OUT-OF-DATE\n"
            + marker_end
            + original[j:]
        )
        OVERVIEW.write_text(corrupted, encoding="utf-8")
        r = _run("--check")
        assert r.returncode == 1
    finally:
        OVERVIEW.write_text(original, encoding="utf-8")


def test_no_markers_no_op(tmp_path):
    # A file with no markers is a no-op; script exits 0.
    alt = tmp_path / "alt.md"
    alt.write_text("# no markers here\n", encoding="utf-8")
    r = _run("--target", str(alt))
    assert r.returncode == 0


def test_missing_target_fails_loud(tmp_path):
    # A nonexistent target must exit non-zero with a clear message.
    bogus = tmp_path / "does-not-exist.md"
    r = _run("--target", str(bogus))
    assert r.returncode != 0
    assert "missing" in (r.stderr + r.stdout).lower() or "not" in (r.stderr + r.stdout).lower()


def test_required_table_contains_all_required_fields():
    # The regenerated overview must mention every schema-required field
    # in its REQUIRED table. This protects against a regex bug that
    # silently drops fields.
    import json
    schema = json.loads(
        (REPO_ROOT / "shared/contracts/passport/literature_corpus_entry.schema.json")
        .read_text(encoding="utf-8")
    )
    _run()  # ensure overview is current
    content = OVERVIEW.read_text(encoding="utf-8")
    start = "<!-- GENERATED:LITERATURE_CORPUS_REQUIRED:START -->"
    end = "<!-- GENERATED:LITERATURE_CORPUS_REQUIRED:END -->"
    section = content[content.index(start) + len(start) : content.index(end)]
    for field in schema["required"]:
        assert f"`{field}`" in section, (
            f"required field {field!r} missing from REQUIRED table"
        )
