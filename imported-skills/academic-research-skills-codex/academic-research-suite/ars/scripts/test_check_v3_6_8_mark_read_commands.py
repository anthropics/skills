"""Unit tests for check_v3_6_8_mark_read_commands.py.

Per v3.6.8 spec §3.6 Step 7 acceptance criteria. The lint asserts that the
2 commands (mark-read, unmark-read) exist, carry the validation rule, and
reference the peer-file write target — NOT the entry frontmatter.
"""
from __future__ import annotations

import shutil
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.test_helpers import run_script


LINT = Path(__file__).parent / "check_v3_6_8_mark_read_commands.py"
REPO_ROOT = Path(__file__).parent.parent


def _copy_repo_skeleton(dest: Path) -> None:
    """Copy the minimal repo surface the lint reads: commands/."""
    (dest / "commands").mkdir()
    src_cmds = REPO_ROOT / "commands"
    for f in src_cmds.glob("ars-*.md"):
        shutil.copy(f, dest / "commands" / f.name)


class TestMarkReadCommandsLint(unittest.TestCase):
    def test_real_repo_passes(self) -> None:
        """The real repo (which ships both commands) must lint cleanly."""
        result = run_script(LINT, cwd=REPO_ROOT)
        self.assertEqual(
            result.returncode, 0, msg=f"stderr: {result.stderr}\nstdout: {result.stdout}"
        )

    def test_missing_mark_read_command_fails(self) -> None:
        """Spec §3.6 Step 7 acceptance: 2 commands MUST exist."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_repo_skeleton(root)
            (root / "commands" / "ars-mark-read.md").unlink()

            result = run_script(LINT, cwd=root)

            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "ars-mark-read.md", result.stdout + result.stderr
            )

    def test_missing_unmark_read_command_fails(self) -> None:
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_repo_skeleton(root)
            (root / "commands" / "ars-unmark-read.md").unlink()

            result = run_script(LINT, cwd=root)

            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "ars-unmark-read.md", result.stdout + result.stderr
            )

    def test_missing_validation_rule_token_fails(self) -> None:
        """Spec §3.6 firm rule 2 + Step 7 acceptance: the command body
        must reference the validation rule (citation_key against
        literature_corpus[]). Drifting away from this wording removes
        the user-visible contract."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_repo_skeleton(root)
            cmd = root / "commands" / "ars-mark-read.md"
            text = cmd.read_text(encoding="utf-8")
            mutated = text.replace("literature_corpus[]", "the corpus")
            cmd.write_text(mutated, encoding="utf-8")

            result = run_script(LINT, cwd=root)

            self.assertNotEqual(result.returncode, 0)
            self.assertIn(
                "literature_corpus", result.stdout + result.stderr
            )

    def test_missing_peer_file_token_fails(self) -> None:
        """Spec §3.6 firm rule 1 + §3.1 firm rule 3: the command MUST
        write to the peer file `<passport-stem>_human_read_log.yaml`,
        NOT to entry frontmatter. The peer-file token must appear in
        the body so future readers see the contract."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_repo_skeleton(root)
            cmd = root / "commands" / "ars-mark-read.md"
            text = cmd.read_text(encoding="utf-8")
            mutated = text.replace("human_read_log.yaml", "session_state.json")
            cmd.write_text(mutated, encoding="utf-8")

            result = run_script(LINT, cwd=root)

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("human_read_log", result.stdout + result.stderr)

    def test_missing_sonnet_model_routing_fails(self) -> None:
        """Spec §3.6 Step 7 + feedback_no_haiku.md: command frontmatter
        MUST declare model: sonnet (NOT haiku, NOT missing)."""
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            _copy_repo_skeleton(root)
            cmd = root / "commands" / "ars-mark-read.md"
            text = cmd.read_text(encoding="utf-8")
            mutated = text.replace("model: sonnet", "model: haiku")
            cmd.write_text(mutated, encoding="utf-8")

            result = run_script(LINT, cwd=root)

            self.assertNotEqual(result.returncode, 0)
            self.assertIn("sonnet", result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
