"""Unit tests for scripts/run_ci_pytest_manifest.py (issue #156).

The runner reads scripts/_ci_pytest_manifest.toml and invokes pytest for each
entry. Behavior contract:

- runs `python -m pytest <path> <args...> -v` per entry
- wraps each invocation in `::group::<id>` / `::endgroup::` annotations
- runs ALL entries even when some fail (accumulate-failures, not fail-fast)
  so CI surfaces every broken suite in one PR
- supports `--id <id>` to run a single named entry (local debug)
- supports `--manifest <path>` and `--root <dir>` overrides for tests
"""
from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path

import pytest


SCRIPT = Path(__file__).resolve().parent / "run_ci_pytest_manifest.py"


def _run(
    manifest_path: Path,
    *,
    root: Path | None = None,
    only_id: str | None = None,
) -> subprocess.CompletedProcess[str]:
    cmd = [sys.executable, str(SCRIPT), "--manifest", str(manifest_path)]
    if root is not None:
        cmd.extend(["--root", str(root)])
    if only_id is not None:
        cmd.extend(["--id", only_id])
    return subprocess.run(cmd, capture_output=True, text=True)


def _write(path: Path, content: str) -> None:
    path.write_text(textwrap.dedent(content).lstrip(), encoding="utf-8")


@pytest.fixture
def workdir(tmp_path: Path) -> Path:
    (tmp_path / "scripts").mkdir()
    # Two passing test files, one failing test file.
    _write(tmp_path / "scripts" / "test_pass_a.py", """
    def test_alpha(): assert True
    """)
    _write(tmp_path / "scripts" / "test_pass_b.py", """
    def test_beta(): assert 1 + 1 == 2
    """)
    _write(tmp_path / "scripts" / "test_fail.py", """
    def test_should_fail(): assert False, "boom"
    """)
    _write(tmp_path / "scripts" / "test_marked.py", """
    def test_unit_one(): assert True
    def test_unit_two(): assert True
    def test_integration_alpha(): assert True
    """)
    return tmp_path


def test_runs_all_passing_entries(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "pass-a"
    path = "scripts/test_pass_a.py"

    [[pytest]]
    id = "pass-b"
    path = "scripts/test_pass_b.py"
    """)

    result = _run(manifest, root=workdir)

    assert result.returncode == 0, result.stdout + result.stderr
    combined = result.stdout + result.stderr
    assert "::group::pass-a" in combined
    assert "::endgroup::" in combined
    assert "::group::pass-b" in combined


def test_fails_when_any_entry_fails(workdir: Path) -> None:
    """Runner accumulates failures: every entry runs even if an earlier one
    failed, then the aggregate exit code reports the failure."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "pass-a"
    path = "scripts/test_pass_a.py"

    [[pytest]]
    id = "fail"
    path = "scripts/test_fail.py"

    [[pytest]]
    id = "pass-b"
    path = "scripts/test_pass_b.py"
    """)

    result = _run(manifest, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "::group::pass-a" in combined
    assert "::group::fail" in combined
    # The runner must NOT stop at the first failure. `pass-b` runs after
    # `fail` in the manifest; this assertion pins the accumulate-failures
    # contract so a future refactor to fail-fast would fail this test.
    assert "::group::pass-b" in combined


def test_args_passed_through_to_pytest(workdir: Path) -> None:
    """Args like `-k <expr>` must reach pytest verbatim."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "unit-only"
    path = "scripts/test_marked.py"
    args = ["-k", "unit"]
    """)

    result = _run(manifest, root=workdir)

    assert result.returncode == 0, result.stdout + result.stderr
    combined = result.stdout + result.stderr
    # Two `test_unit_*` ran, the `test_integration_alpha` was excluded by -k.
    assert "test_unit_one" in combined
    assert "test_unit_two" in combined
    assert "test_integration_alpha" not in combined


def test_id_filter_runs_only_named_entry(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "pass-a"
    path = "scripts/test_pass_a.py"

    [[pytest]]
    id = "fail"
    path = "scripts/test_fail.py"
    """)

    # Explicitly run only pass-a — even though the manifest contains a failing
    # entry, --id filter should isolate the run.
    result = _run(manifest, root=workdir, only_id="pass-a")

    assert result.returncode == 0, result.stdout + result.stderr
    combined = result.stdout + result.stderr
    assert "::group::pass-a" in combined
    # The fail entry should NOT have been invoked.
    assert "::group::fail" not in combined


def test_unknown_id_filter_fails(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "pass-a"
    path = "scripts/test_pass_a.py"
    """)

    result = _run(manifest, root=workdir, only_id="nope")

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "nope" in combined


def test_missing_manifest_fails(workdir: Path) -> None:
    result = _run(workdir / "scripts" / "missing.toml", root=workdir)
    assert result.returncode != 0


def test_empty_manifest_passes(workdir: Path) -> None:
    """A manifest with zero entries should exit 0 (degenerate but not an error)."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    manifest.write_text("# empty manifest\n", encoding="utf-8")

    result = _run(manifest, root=workdir)

    assert result.returncode == 0, result.stdout + result.stderr
