import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.run_eval import (
    command_clone_prefix,
    is_command_clone_reference,
    remove_stale_command_clones,
)


class CommandCloneTests(unittest.TestCase):
    def test_prefix_matches_any_worker_clone(self):
        # Parallel workers only differ by the trailing hash; any clone is a hit.
        self.assertEqual(command_clone_prefix("demo"), "demo-skill-")
        self.assertTrue(is_command_clone_reference("demo-skill-a1b2c3d4", "demo"))
        self.assertTrue(is_command_clone_reference("demo-skill-deadbeef", "demo"))
        self.assertTrue(
            is_command_clone_reference(
                '/tmp/.claude/commands/demo-skill-cafebabe.md', "demo"
            )
        )
        self.assertFalse(is_command_clone_reference("other-skill-deadbeef", "demo"))
        self.assertFalse(is_command_clone_reference("demo", "demo"))

    def test_stale_sweep_only_removes_generated_clones(self):
        with tempfile.TemporaryDirectory() as root:
            commands = Path(root) / ".claude" / "commands"
            commands.mkdir(parents=True)
            stale = commands / "demo-skill-deadbeef.md"
            current = commands / "demo-skill-cafebabe.md"
            unrelated = commands / "README.md"
            user_cmd = commands / "my-helper.md"
            for path in (stale, current, unrelated, user_cmd):
                path.write_text("placeholder")

            self.assertEqual(remove_stale_command_clones(Path(root), "demo"), 2)
            self.assertFalse(stale.exists())
            self.assertFalse(current.exists())
            self.assertTrue(unrelated.exists())
            self.assertTrue(user_cmd.exists())

    def test_stale_sweep_noop_without_commands_dir(self):
        with tempfile.TemporaryDirectory() as root:
            self.assertEqual(remove_stale_command_clones(Path(root), "demo"), 0)


if __name__ == "__main__":
    unittest.main()
