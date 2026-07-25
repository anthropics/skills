"""Unit tests for scripts/check_ci_pytest_manifest.py (issue #156).

Lint guards 6 failure modes on the unified pytest manifest:
1. manifest entry path does not exist on disk
2. duplicate `id` across entries
3. duplicate exact (path, args) invocation across entries (unless an explicit
   allowlist marker is present)
4. malformed `args` (not a list, or list elements not strings)
5. unknown keys in a manifest entry (catches typos like `arg` for `args`)
6. `.github/workflows/spec-consistency.yml` contains a direct
   `pytest scripts/test_*.py` invocation outside the runner — including
   bypass variants with flags, quotes, `./` prefix, `python -m pytest`,
   `py.test`, and backslash line continuations

The lint reads the manifest at scripts/_ci_pytest_manifest.toml by default and
the workflow at .github/workflows/spec-consistency.yml.
"""
from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path

import pytest


SCRIPT = Path(__file__).resolve().parent / "check_ci_pytest_manifest.py"


def _run(
    manifest_path: Path,
    workflow_path: Path,
    *,
    root: Path | None = None,
    extra_args: list[str] | None = None,
) -> subprocess.CompletedProcess[str]:
    cmd = [
        sys.executable,
        str(SCRIPT),
        "--manifest",
        str(manifest_path),
        "--workflow",
        str(workflow_path),
    ]
    if root is not None:
        cmd.extend(["--root", str(root)])
    if extra_args:
        cmd.extend(extra_args)
    return subprocess.run(cmd, capture_output=True, text=True)


def _write(path: Path, content: str) -> None:
    path.write_text(textwrap.dedent(content).lstrip(), encoding="utf-8")


@pytest.fixture
def workdir(tmp_path: Path) -> Path:
    (tmp_path / "scripts").mkdir()
    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    # Plant two real test files referenced by happy-path manifest entries.
    (tmp_path / "scripts" / "test_real_a.py").write_text("def test_a(): assert True\n")
    (tmp_path / "scripts" / "test_real_b.py").write_text("def test_b(): assert True\n")
    return tmp_path


def test_clean_manifest_passes(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"

    [[pytest]]
    id = "real-b"
    path = "scripts/test_real_b.py"
    args = ["-k", "fast"]
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    name: Spec Consistency
    on: [pull_request]
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode == 0, result.stderr + result.stdout
    assert "ok" in result.stdout.lower() or result.stdout.strip() != ""


def test_missing_path_fails(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "ghost"
    path = "scripts/test_does_not_exist.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "ghost" in combined
    assert "test_does_not_exist.py" in combined


def test_duplicate_id_fails(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"

    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_b.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, "jobs: {}\n")

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "duplicate" in combined.lower() and "real-a" in combined


def test_duplicate_invocation_fails(workdir: Path) -> None:
    """Two distinct ids pointing at the same (path, args) is bypass-prone."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a-1"
    path = "scripts/test_real_a.py"

    [[pytest]]
    id = "real-a-2"
    path = "scripts/test_real_a.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, "jobs: {}\n")

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "duplicate" in combined.lower()
    assert "test_real_a.py" in combined


def test_duplicate_invocation_with_distinct_args_passes(workdir: Path) -> None:
    """Same path with DIFFERENT -k filters is the legitimate use case."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a-unit"
    path = "scripts/test_real_a.py"
    args = ["-k", "micro"]

    [[pytest]]
    id = "real-a-integration"
    path = "scripts/test_real_a.py"
    args = ["-k", "integration"]
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode == 0, result.stdout + result.stderr


def test_malformed_args_fails(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    args = "this should be a list, not a string"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, "jobs: {}\n")

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "args" in combined.lower()


def test_direct_pytest_invocation_in_workflow_fails(workdir: Path) -> None:
    """Drift guard: spec-consistency.yml must NOT have `pytest scripts/test_*.py` outside runner."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    name: Spec Consistency
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
          - run: pytest scripts/test_real_a.py -v
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "pytest" in combined.lower()
    assert "scripts/test_real_a.py" in combined


def test_unittest_invocations_in_workflow_pass(workdir: Path) -> None:
    """`python3 -m unittest scripts.test_X` is out of scope for #156 — should NOT trigger drift guard."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
          - run: python3 -m unittest scripts.test_real_b -v
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode == 0, result.stdout + result.stderr


def test_missing_manifest_fails(workdir: Path) -> None:
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, "jobs: {}\n")
    result = _run(workdir / "scripts" / "missing_manifest.toml", workflow, root=workdir)
    assert result.returncode != 0


def test_missing_workflow_fails(workdir: Path) -> None:
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    """)
    result = _run(manifest, workdir / ".github" / "workflows" / "missing.yml", root=workdir)
    assert result.returncode != 0


def test_unknown_entry_key_fails(workdir: Path) -> None:
    """A typo'd key (e.g., `arg` instead of `args`) must NOT silently pass —
    otherwise the runner would skip the intended -k filter and run the full
    test set."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    arg = ["-k", "this-should-be-args"]
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "arg" in combined.lower()


@pytest.mark.parametrize(
    "bypass_invocation",
    [
        # intermediate flags
        "          - run: pytest -v scripts/test_real_a.py",
        "          - run: pytest --tb=short scripts/test_real_a.py",
        "          - run: pytest -xvs --tb=short scripts/test_real_a.py",
        # quoted paths
        '          - run: pytest "scripts/test_real_a.py"',
        "          - run: pytest 'scripts/test_real_a.py'",
        # explicit relative prefix
        "          - run: pytest ./scripts/test_real_a.py",
        # alternative invocations
        "          - run: python -m pytest scripts/test_real_a.py",
        "          - run: python3 -m pytest scripts/test_real_a.py",
        "          - run: python -m pytest -q scripts/test_real_a.py",
        "          - run: py.test scripts/test_real_a.py",
        "          - run: uv run pytest scripts/test_real_a.py",
        # quoted + flag combo
        '          - run: pytest -v "scripts/test_real_a.py"',
    ],
    ids=[
        "flag-first-short",
        "flag-first-long",
        "multiple-flags",
        "double-quoted-path",
        "single-quoted-path",
        "relative-path-prefix",
        "python-m-pytest",
        "python3-m-pytest",
        "python-m-pytest-with-flag",
        "py.test-shorthand",
        "uv-run-pytest",
        "flag-and-quote-combo",
    ],
)
def test_direct_pytest_bypass_variants_fail(workdir: Path, bypass_invocation: str) -> None:
    """Drift-guard regex must catch every common bypass pattern: flags
    between `pytest` and the path, quoted paths, `./` prefix, `python -m
    pytest`, `py.test`, `uv run pytest`. (Dual-track review: gemini P1.1-P1.2
    + codex empirical probe.)"""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    workflow_body = (
        "jobs:\n"
        "  spec:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: python scripts/run_ci_pytest_manifest.py\n"
        f"{bypass_invocation}\n"
    )
    workflow.write_text(workflow_body, encoding="utf-8")

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0, (
        f"bypass variant should have failed lint but did not: "
        f"{bypass_invocation!r}\nstdout={result.stdout!r} stderr={result.stderr!r}"
    )
    combined = result.stdout + result.stderr
    assert "test_real_a.py" in combined


def test_line_continuation_bypass_fails(workdir: Path) -> None:
    """Backslash-newline line continuations must be normalized so the regex
    sees one logical command. (Dual-track review: gemini P1.3.)"""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    workflow.write_text(
        "jobs:\n"
        "  spec:\n"
        "    runs-on: ubuntu-latest\n"
        "    steps:\n"
        "      - run: python scripts/run_ci_pytest_manifest.py\n"
        "      - run: |\n"
        "          pytest \\\n"
        "            scripts/test_real_a.py\n",
        encoding="utf-8",
    )

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode != 0
    combined = result.stdout + result.stderr
    assert "test_real_a.py" in combined


def test_pytest_path_substring_in_comment_does_not_match(workdir: Path) -> None:
    """The drift guard strips YAML comments before scanning, so an example
    inside a `#` comment must NOT trip the lint. This test pins that
    behavior so the comment-strip can't be regressed accidentally."""
    manifest = workdir / "scripts" / "_ci_pytest_manifest.toml"
    _write(manifest, """
    [[pytest]]
    id = "real-a"
    path = "scripts/test_real_a.py"
    """)
    workflow = workdir / ".github" / "workflows" / "spec-consistency.yml"
    _write(workflow, """
    # The drift guard rejects direct `pytest scripts/test_real_a.py` calls
    # outside the runner — this comment must not trip it.
    jobs:
      spec:
        runs-on: ubuntu-latest
        steps:
          - run: python scripts/run_ci_pytest_manifest.py
    """)

    result = _run(manifest, workflow, root=workdir)

    assert result.returncode == 0, result.stdout + result.stderr
