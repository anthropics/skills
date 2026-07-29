import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.run_eval import (
    command_clone_prefix,
    is_command_clone_reference,
    process_stream_event,
    shadow_installed_skill,
)


class TriggerDetectionTests(unittest.TestCase):
    def test_batch_token_matches_only_current_worker_clones(self):
        token = command_clone_prefix("demo", "batch1234")
        self.assertTrue(
            is_command_clone_reference("demo-skill-batch1234-deadbeef", "demo", "batch1234")
        )
        self.assertFalse(
            is_command_clone_reference("demo-skill-oldbatch-deadbeef", "demo", "batch1234")
        )
        self.assertIn("batch1234", token)

    def test_unrelated_tool_does_not_end_evaluation(self):
        state = process_stream_event(
            {
                "type": "stream_event",
                "event": {
                    "type": "content_block_start",
                    "content_block": {"type": "tool_use", "name": "Grep"},
                },
            },
            "demo-skill-batch1234-",
        )
        self.assertFalse(state[0])
        self.assertIsNone(state[1])
        self.assertFalse(state[3])

    def test_later_skill_invocation_is_detected_after_unrelated_tool(self):
        state = (False, None, "")
        events = [
            {
                "type": "stream_event",
                "event": {
                    "type": "content_block_start",
                    "content_block": {"type": "tool_use", "name": "Grep"},
                },
            },
            {
                "type": "stream_event",
                "event": {
                    "type": "content_block_start",
                    "content_block": {"type": "tool_use", "name": "Skill"},
                },
            },
            {
                "type": "stream_event",
                "event": {
                    "type": "content_block_delta",
                    "delta": {
                        "type": "input_json_delta",
                        "partial_json": '{"skill":"demo-skill-batch1234-',
                    },
                },
            },
            {
                "type": "stream_event",
                "event": {
                    "type": "content_block_stop",
                },
            },
            {"type": "result"},
        ]
        for event in events:
            state = process_stream_event(event, "demo-skill-batch1234-", *state)[:3]
        self.assertTrue(state[0])

    def test_assistant_fallback_checks_all_tool_blocks(self):
        state = process_stream_event(
            {
                "type": "assistant",
                "message": {
                    "content": [
                        {"type": "tool_use", "name": "Grep", "input": {}},
                        {
                            "type": "tool_use",
                            "name": "Read",
                            "input": {
                                "file_path": ".claude/commands/demo-skill-batch1234-deadbeef.md"
                            },
                        },
                    ]
                },
            },
            "demo-skill-batch1234-",
        )
        self.assertTrue(state[0])
        self.assertFalse(state[3])


class InstalledSkillShadowTests(unittest.TestCase):
    def test_project_skill_is_restored_after_batch(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir) / "project"
            home = Path(temp_dir) / "home"
            installed = root / ".claude" / "skills" / "demo"
            user_installed = home / ".claude" / "skills" / "demo"
            installed.mkdir(parents=True)
            user_installed.mkdir(parents=True)
            (installed / "SKILL.md").write_text("original")
            (user_installed / "SKILL.md").write_text("user original")

            with shadow_installed_skill("demo", root, home):
                self.assertFalse(installed.exists())
                self.assertFalse(user_installed.exists())
                shadowed = list((root / ".claude").glob("demo.eval-shadow-*"))
                self.assertEqual(len(shadowed), 1)
                self.assertEqual((shadowed[0] / "SKILL.md").read_text(), "original")
                user_shadowed = list((home / ".claude").glob("demo.eval-shadow-*"))
                self.assertEqual(len(user_shadowed), 1)
                self.assertEqual(
                    (user_shadowed[0] / "SKILL.md").read_text(), "user original"
                )

            self.assertTrue(installed.exists())
            self.assertEqual((installed / "SKILL.md").read_text(), "original")
            self.assertTrue(user_installed.exists())
            self.assertEqual((user_installed / "SKILL.md").read_text(), "user original")


if __name__ == "__main__":
    unittest.main()
