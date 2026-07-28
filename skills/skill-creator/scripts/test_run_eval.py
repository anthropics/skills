import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.run_eval import command_clone_prefix, is_command_clone_reference, remove_stale_command_clones


class CommandCloneTests(unittest.TestCase):
    def test_prefix_matches_any_worker_clone(self):
        self.assertTrue(is_command_clone_reference("demo-skill-a1b2c3d4", "demo"))
        self.assertTrue(is_command_clone_reference("demo-skill-deadbeef", "demo"))
        self.assertFalse(is_command_clone_reference("other-skill-deadbeef", "demo"))

    def test_stale_sweep_only_removes_generated_clones(self):
        with tempfile.TemporaryDirectory() as root:
            commands = Path(root) / ".claude" / "commands"
            commands.mkdir(parents=True)
            stale = commands / "demo-skill-deadbeef.md"
            current = commands / "demo-skill-cafebabe.md"
            unrelated = commands / "README.md"
            for path in (stale, current, unrelated):
                path.write_text("placeholder")

            self.assertEqual(remove_stale_command_clones(Path(root), "demo"), 2)
            self.assertFalse(stale.exists())
            self.assertFalse(current.exists())
            self.assertTrue(unrelated.exists())


if __name__ == "__main__":
    unittest.main()
