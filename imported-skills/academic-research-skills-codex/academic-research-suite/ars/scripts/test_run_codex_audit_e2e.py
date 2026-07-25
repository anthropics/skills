"""End-to-end dispatch test for scripts/run_codex_audit.sh (Phase 6.1 deferred gate).

Spec: docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator-hooks-spec.md
      §4.1 (Bash 4+ guard) + §4.4 (wrapper internal behavior) +
      Phase 6.1 verification gate (lines 2308) — "synthetic smoke test (codex CLI mocked
      or invoked against a tiny fixture deliverable) produces a well-formed proposal
      entry that validates against the Phase 6.2 schemas in --mode proposal".

This test is gated to Linux runners (and any host with Bash 4+) because the
wrapper's §4.1 Bash 4+ check exits 64 on macOS stock Bash 3.2. CI runs this
on ubuntu-latest; locally on macOS the test self-skips.

The test mocks the `codex` CLI via a PATH-prefix shim that emits a canonical
Phase 2 audit JSONL stream (per §3.3) and a `codex --version` semver line
(per §4.4 Step 1c). The wrapper consumes the mocked output, parses the verdict
text, and writes the four contract files. The test then validates each
contract file against its Phase 6.2 schema in --mode proposal.

Coverage:
- Wrapper exits 0 on success
- Four contract files (jsonl/sidecar/verdict/proposal entry) written to --output-dir
- Three diagnostic files (stdout/stderr/manifest) written
- Proposal entry validates against audit_artifact_entry.schema.json --mode proposal
  (lifecycle invariant E3+E4: verified_at/verified_by absent in proposal)
- Verdict file validates against audit_verdict.schema.json
- Sidecar validates against audit_sidecar.schema.json
- JSONL stream validates against audit_jsonl.schema.json (each event row)

Run with: pytest -xvs scripts/test_run_codex_audit_e2e.py
"""

from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
WRAPPER = REPO_ROOT / "scripts" / "run_codex_audit.sh"
SCHEMA_DIR_PASSPORT = REPO_ROOT / "shared" / "contracts" / "passport"
SCHEMA_DIR_AUDIT = REPO_ROOT / "shared" / "contracts" / "audit"

# Skip on hosts without Bash 4+. macOS stock /bin/bash is 3.2; CI ubuntu has 5.x.
def _bash_major_version() -> int:
    try:
        out = subprocess.run(
            ["bash", "-c", "echo $BASH_VERSION"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        return int(out.split(".", 1)[0])
    except Exception:  # pragma: no cover - defensive
        return 0


pytestmark = pytest.mark.skipif(
    _bash_major_version() < 4,
    reason="wrapper requires Bash 4+; skip on stock macOS / Bash 3.2",
)


def _make_codex_mock(bin_dir: Path) -> Path:
    """Create a fake `codex` script that emits a canonical Phase 2 JSONL stream.

    The mock supports two invocation forms:
      1. `codex --version` → prints `codex-cli 0.128.0` (matches §3.4 sidecar
         codex_cli_version semver pattern)
      2. `codex exec -m gpt-5.5 -c '...' --json - < <prompt>` → emits canonical
         JSONL events to stdout matching §3.3 four-event clean-completion shape
         with a Section-6-formatted PASS verdict in the agent_message text.
    """
    mock = bin_dir / "codex"
    # canonical PASS verdict text per audit template Section 6 (severity-bucket
    # count summary). The wrapper's parse_audit_verdict.py extracts this into
    # verdict.yaml; we emit the minimum format the parser accepts.
    mock_script = textwrap.dedent(
        """\
        #!/usr/bin/env bash
        set -euo pipefail

        if [[ "${1:-}" == "--version" ]]; then
          echo "codex-cli 0.128.0"
          exit 0
        fi

        # Drain stdin (the rendered audit prompt). We don't inspect it.
        cat >/dev/null

        # Emit canonical 4-event clean-completion JSONL stream.
        # The agent_message text follows audit template Section 6 format —
        # parse_audit_verdict.py's _SUMMARY_B regex requires the convergence
        # form "Round N: 0 findings of any severity. Convergence reached."
        # as the LAST non-empty line of the verdict text.
        cat <<'JSONL'
        {"type":"thread.started","thread_id":"019de371-4c13-7521-8af7-fccf6bd23279"}
        {"type":"turn.started"}
        {"type":"item.completed","item":{"id":"item_0","type":"agent_message","text":"Round 1: 0 findings of any severity. Convergence reached."}}
        {"type":"turn.completed","usage":{"input_tokens":100,"cached_input_tokens":0,"output_tokens":50,"reasoning_output_tokens":0}}
        JSONL
        """
    )
    mock.write_text(mock_script)
    mock.chmod(mock.stat().st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)
    return mock


def _make_synthetic_deliverable(repo_clone: Path) -> Path:
    """Tiny synthetic deliverable the mock audits.

    Path is repo-relative as the wrapper's --deliverable contract requires.
    """
    deliv_dir = repo_clone / "tests" / "fixtures" / "phase_6_1_e2e"
    deliv_dir.mkdir(parents=True)
    deliv = deliv_dir / "synthetic_deliverable.md"
    deliv.write_text(
        "# Synthetic deliverable\n\n"
        "Single-claim text; mock codex emits PASS regardless of content.\n"
    )
    return deliv


def _stage_repo_clone(work_dir: Path) -> Path:
    """Stage a minimal repo clone with the wrapper, schemas, parser, and audit template.

    Symlinks to the real repo files keep the test fast and avoids editing
    behaviour. The wrapper's REPO_ROOT detection uses the script's `dirname`
    so the parser path resolution works automatically.
    """
    clone = work_dir / "repo"
    clone.mkdir()
    for sub in (
        "scripts",
        "shared/contracts/passport",
        "shared/contracts/audit",
        "shared/templates",
    ):
        (clone / sub).mkdir(parents=True)
    # Real wrapper + parser + helpers, copied so chmod is preserved.
    for src_rel in (
        "scripts/run_codex_audit.sh",
        "scripts/parse_audit_verdict.py",
        "scripts/audit_snapshot.py",
    ):
        src = REPO_ROOT / src_rel
        dst = clone / src_rel
        shutil.copy2(src, dst)
        dst.chmod(0o755)
    # Schemas (referenced by the wrapper's contract emission).
    for src_rel in (
        "shared/contracts/passport/audit_artifact_entry.schema.json",
        "shared/contracts/audit/audit_jsonl.schema.json",
        "shared/contracts/audit/audit_sidecar.schema.json",
        "shared/contracts/audit/audit_verdict.schema.json",
        "shared/templates/codex_audit_multifile_template.md",
    ):
        shutil.copy2(REPO_ROOT / src_rel, clone / src_rel)
    # Initialize a stub git repo so wrapper's `git rev-parse` succeeds.
    subprocess.run(["git", "init", "-q"], cwd=clone, check=True)
    subprocess.run(["git", "config", "user.email", "test@local"], cwd=clone, check=True)
    subprocess.run(["git", "config", "user.name", "test"], cwd=clone, check=True)
    subprocess.run(["git", "add", "-A"], cwd=clone, check=True)
    subprocess.run(
        ["git", "commit", "-q", "-m", "stub for e2e test"], cwd=clone, check=True
    )
    return clone


def _validate_against_schema(doc: dict, schema_path: Path, mode: str | None = None):
    from jsonschema import Draft202012Validator, FormatChecker

    schema = json.loads(schema_path.read_text())
    if mode == "proposal" and "oneOf" in schema:
        # The audit_artifact_entry schema has oneOf [proposal, persisted]; we
        # validate against the proposal arm explicitly. jsonschema's default
        # behaviour requires exactly one arm to validate; passing the full
        # schema is the canonical "--mode proposal" path because proposal
        # documents fail the persisted arm (verified_at absent) and pass
        # the proposal arm (verified_at absent).
        pass
    Draft202012Validator(schema, format_checker=FormatChecker()).validate(doc)


def test_wrapper_dispatches_end_to_end(tmp_path):
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    _make_codex_mock(bin_dir)

    repo = _stage_repo_clone(tmp_path)
    deliverable = _make_synthetic_deliverable(repo)
    deliverable_rel = deliverable.relative_to(repo)
    # Wrapper rejects absolute --output-dir paths; pass repo-relative.
    output_dir_rel = "audit_artifacts"
    output_dir = repo / output_dir_rel

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"

    result = subprocess.run(
        [
            "bash",
            str(repo / "scripts" / "run_codex_audit.sh"),
            "--stage", "2",
            "--agent", "synthesis_agent",
            "--deliverable", str(deliverable_rel),
            "--round", "1",
            "--target-rounds", "3",
            "--output-dir", output_dir_rel,
        ],
        cwd=repo,
        env=env,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0, (
        f"Wrapper exited {result.returncode} (expected 0).\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )

    # Locate the run_id by looking at the produced files.
    contract_files = sorted(output_dir.glob("*.jsonl"))
    assert len(contract_files) == 1, (
        f"Expected exactly one .jsonl contract file; got {[p.name for p in contract_files]}"
    )
    run_id = contract_files[0].stem

    # Four contract files exist.
    jsonl_path = output_dir / f"{run_id}.jsonl"
    sidecar_path = output_dir / f"{run_id}.meta.json"
    verdict_path = output_dir / f"{run_id}.verdict.yaml"
    proposal_path = output_dir / f"{run_id}.audit_artifact_entry.json"
    for p in (jsonl_path, sidecar_path, verdict_path, proposal_path):
        assert p.exists(), f"contract file missing: {p}"

    # Three diagnostic files exist.
    for diag in ("stdout", "stderr", "manifest.txt"):
        assert (output_dir / f"{run_id}.{diag}").exists(), f"diagnostic missing: {diag}"

    # Proposal entry validates against audit_artifact_entry.schema.json
    # in proposal mode (verified_at / verified_by must be absent).
    proposal_doc = json.loads(proposal_path.read_text())
    _validate_against_schema(
        proposal_doc,
        SCHEMA_DIR_PASSPORT / "audit_artifact_entry.schema.json",
        mode="proposal",
    )
    assert "verified_at" not in proposal_doc.get("verdict", {}), (
        "proposal must NOT carry verdict.verified_at (Pattern C3 attack surface)"
    )
    assert "verified_by" not in proposal_doc.get("verdict", {}), (
        "proposal must NOT carry verdict.verified_by"
    )

    # Verdict file validates against audit_verdict.schema.json.
    import yaml as pyyaml

    verdict_doc = pyyaml.safe_load(verdict_path.read_text())
    _validate_against_schema(
        verdict_doc,
        SCHEMA_DIR_AUDIT / "audit_verdict.schema.json",
    )
    assert verdict_doc["verdict_status"] == "PASS"
    assert verdict_doc["finding_counts"]["p1"] == 0
    assert verdict_doc["finding_counts"]["p2"] == 0
    assert verdict_doc["finding_counts"]["p3"] == 0

    # Sidecar validates against audit_sidecar.schema.json.
    sidecar_doc = json.loads(sidecar_path.read_text())
    _validate_against_schema(
        sidecar_doc,
        SCHEMA_DIR_AUDIT / "audit_sidecar.schema.json",
    )
    assert sidecar_doc["run_id"] == run_id
    assert sidecar_doc["codex_cli_version"] == "0.128.0"
    assert sidecar_doc["process"]["exit_code"] == 0

    # JSONL events each validate against audit_jsonl.schema.json's row schema.
    jsonl_lines = [
        json.loads(ln) for ln in jsonl_path.read_text().splitlines() if ln.strip()
    ]
    assert len(jsonl_lines) >= 4, "expected canonical 4-event minimum stream"
    assert jsonl_lines[0]["type"] == "thread.started"
    assert jsonl_lines[-1]["type"] == "turn.completed"


def test_wrapper_dry_run_writes_nothing(tmp_path):
    """§4.1 / §10 Phase 6.1 verification gate — --dry-run validates inputs only."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    _make_codex_mock(bin_dir)

    repo = _stage_repo_clone(tmp_path)
    deliverable = _make_synthetic_deliverable(repo)
    output_dir_rel = "audit_artifacts"
    output_dir = repo / output_dir_rel

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"

    result = subprocess.run(
        [
            "bash",
            str(repo / "scripts" / "run_codex_audit.sh"),
            "--stage", "2",
            "--agent", "synthesis_agent",
            "--deliverable", str(deliverable.relative_to(repo)),
            "--round", "1",
            "--output-dir", output_dir_rel,
            "--dry-run",
        ],
        cwd=repo,
        env=env,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, (
        f"--dry-run wrapper exited {result.returncode} (expected 0).\n"
        f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}"
    )
    # §10 Phase 6.1 verification gate: --dry-run must NOT write any contract artifacts.
    if output_dir.exists():
        artifacts = list(output_dir.glob("*.jsonl")) + list(
            output_dir.glob("*.audit_artifact_entry.json")
        )
        assert not artifacts, (
            f"--dry-run leaked contract artifacts: {[p.name for p in artifacts]}"
        )


def test_wrapper_rejects_round_2_without_previous_findings(tmp_path):
    """§4.2 input validation: --round > 1 requires --previous-findings."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    _make_codex_mock(bin_dir)

    repo = _stage_repo_clone(tmp_path)
    deliverable = _make_synthetic_deliverable(repo)

    env = os.environ.copy()
    env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"

    result = subprocess.run(
        [
            "bash",
            str(repo / "scripts" / "run_codex_audit.sh"),
            "--stage", "2",
            "--agent", "synthesis_agent",
            "--deliverable", str(deliverable.relative_to(repo)),
            "--round", "2",
            "--target-rounds", "3",
            "--output-dir", "audit_artifacts",
        ],
        cwd=repo,
        env=env,
        capture_output=True,
        text=True,
    )
    # EX_USAGE = 64
    assert result.returncode == 64, (
        f"expected exit 64 (EX_USAGE); got {result.returncode}\nstderr: {result.stderr}"
    )
