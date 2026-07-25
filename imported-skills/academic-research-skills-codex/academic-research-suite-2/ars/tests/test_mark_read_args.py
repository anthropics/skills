"""Integration test for scripts/ars_mark_read.py CLI dispatch (#197).

Verifies that citation keys reach the script through the canonical
bash dispatch pattern. Uses a real fixture passport + read-log to
assert the side effect on disk (the script writes to the read-log
file; it does not write to stdout on success).
"""

import subprocess
import yaml
import pytest
from pathlib import Path


@pytest.fixture
def passport_with_corpus(tmp_path: Path) -> Path:
    """Synthetic passport with a literature_corpus carrying test citation keys.

    The script reads ``literature_corpus[].citation_key`` to validate
    incoming keys against the active corpus. The fixture writes a
    minimal YAML passport that satisfies this contract.
    """
    passport_path = tmp_path / "test_passport.yaml"
    passport_path.write_text(
        yaml.safe_dump(
            {
                "literature_corpus": [
                    {"citation_key": "smith2024-data"},
                    {"citation_key": "wang2023"},
                    {"citation_key": "wang:2023"},
                ]
            }
        ),
        encoding="utf-8",
    )
    return passport_path


def test_ars_mark_read_writes_read_log(passport_with_corpus: Path) -> None:
    """Mark two citation keys; assert the read-log records both entries.

    Mirrors the bash block ``python3 scripts/ars_mark_read.py
    $ARGUMENTS --passport-path "<path>"`` with multiple positional
    citation keys, including one with a hyphen.
    """
    script_path = Path("scripts/ars_mark_read.py")
    test_keys = ["smith2024-data", "wang2023"]

    result = subprocess.run(
        ["python3", str(script_path), *test_keys, "--passport-path", str(passport_with_corpus)],
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 0, (
        f"Script failed (exit={result.returncode}): {result.stderr}"
    )

    log_path = passport_with_corpus.parent / f"{passport_with_corpus.stem}_human_read_log.yaml"
    assert log_path.exists(), f"read-log not created at {log_path}"

    log = yaml.safe_load(log_path.read_text(encoding="utf-8")) or {}
    human_read = log.get("human_read", [])
    logged_keys = {entry.get("citation_key") for entry in human_read}
    assert "smith2024-data" in logged_keys
    assert "wang2023" in logged_keys


def test_ars_mark_read_rejects_zero_keys(passport_with_corpus: Path) -> None:
    """Calling with no citation keys should fail-fast via argparse nargs=+."""
    script_path = Path("scripts/ars_mark_read.py")

    result = subprocess.run(
        ["python3", str(script_path), "--passport-path", str(passport_with_corpus)],
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0, "Script should fail with zero citation keys"
    assert "citation_keys" in result.stderr


def test_ars_mark_read_rejects_unknown_key(passport_with_corpus: Path) -> None:
    """A key absent from literature_corpus[] hard-fails per §3.6 firm rule 2."""
    script_path = Path("scripts/ars_mark_read.py")

    result = subprocess.run(
        ["python3", str(script_path), "not-in-corpus", "--passport-path", str(passport_with_corpus)],
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode != 0, "Script should reject unknown citation key"
    assert "ARS-MARK-READ ERROR" in result.stderr
    assert "not-in-corpus" in result.stderr


def test_ars_mark_read_argument_parsing(passport_with_corpus: Path) -> None:
    """Verify citation keys with schema-valid punctuation are parsed correctly."""
    script_path = Path("scripts/ars_mark_read.py")
    test_keys = ["smith2024-data", "wang:2023"]

    result = subprocess.run(
        ["python3", str(script_path), *test_keys, "--passport-path", str(passport_with_corpus)],
        capture_output=True,
        text=True,
        check=False,
    )

    assert result.returncode == 0, (
        f"Script failed (exit={result.returncode}): {result.stderr}"
    )

    log_path = passport_with_corpus.parent / f"{passport_with_corpus.stem}_human_read_log.yaml"
    assert log_path.exists(), f"read-log not created at {log_path}"

    log = yaml.safe_load(log_path.read_text(encoding="utf-8")) or {}
    human_read = log.get("human_read", [])
    logged_keys = {entry.get("citation_key") for entry in human_read}
    assert "smith2024-data" in logged_keys
    assert "wang:2023" in logged_keys
