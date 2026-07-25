"""Unit tests for check_392_citation_verification_intake.py (#392 lint)."""
from __future__ import annotations

import subprocess
import textwrap
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script

SCRIPT = (
    Path(__file__).resolve().parent / "check_392_citation_verification_intake.py"
)
REPO_ROOT = SCRIPT.parent.parent

GOOD_INTAKE = textwrap.dedent(
    """\
    # Intake Agent — Paper Configuration Interview

    ### When No Handoff Materials Are Detected

    Execute the original Phase 0 full interview flow (Step 1-11), then Step 12
    (Domain Evidence Profile) per its own gating in that step, then Step 13
    (Citation Verification Level).

    ## Interview Protocol

    ### Step 13: Citation Verification Level (v3.12, #392)

    Ask the scholar to choose mark only / strict.

    - Answer `strict` → ensure the Material Passport carries
      `terminal_policies.citation_existence: strict`.
    - Answer `mark only`, or no answer → **write nothing to the passport**.

    ## Output Format

    | Parameter | Value |
    |-----------|-------|
    | **Citation Verification** | [strict / advisory (mark only, default)] |
    """
)


def _run(root: Path) -> subprocess.CompletedProcess:
    return run_script(SCRIPT, "--root", str(root))


def _write(root: Path, content: str) -> None:
    path = root / "academic-paper" / "agents" / "intake_agent.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


class TestCitationVerificationIntakeLint(unittest.TestCase):
    def test_good_tree_passes(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write(root, GOOD_INTAKE)
            result = _run(root)
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_orphaned_step_13_fails_i2(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write(
                root,
                GOOD_INTAKE.replace(
                    ", then Step 13\n(Citation Verification Level)", ""
                ),
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("I2", result.stderr)

    def test_missing_pcr_row_fails_i3(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write(
                root,
                "\n".join(
                    l
                    for l in GOOD_INTAKE.splitlines()
                    if "**Citation Verification**" not in l
                ),
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("I3", result.stderr)

    def test_lost_write_nothing_rule_fails_i4(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write(
                root,
                GOOD_INTAKE.replace(
                    "**write nothing to the passport**",
                    "write the advisory key to the passport",
                ),
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("write-nothing", result.stderr)

    def test_lost_strict_seed_target_fails_i4(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write(
                root,
                GOOD_INTAKE.replace(
                    "`terminal_policies.citation_existence: strict`",
                    "the strict policy",
                ),
            )
            result = _run(root)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("strict seeding target", result.stderr)

    def test_renamed_heading_is_parse_error(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _write(
                root,
                GOOD_INTAKE.replace(
                    "### Step 13: Citation Verification Level (v3.12, #392)",
                    "### Step 13: Verification Preferences",
                ),
            )
            result = _run(root)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_missing_file_is_parse_error(self) -> None:
        with TemporaryDirectory() as tmp:
            result = _run(Path(tmp))
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)

    def test_real_repo_passes(self) -> None:
        result = _run(REPO_ROOT)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
