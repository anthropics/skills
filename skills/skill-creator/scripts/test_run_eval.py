import unittest
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.run_eval import process_stream_event


class RunSingleQueryStreamTests(unittest.TestCase):
    """Regression tests for the stream states that caused false negatives."""

    def test_unrelated_tool_does_not_finish_the_evaluation(self):
        triggered, pending, payload, finished = process_stream_event(
            {"type": "stream_event", "event": {
                "type": "content_block_start",
                "content_block": {"type": "tool_use", "name": "Grep"},
            }},
            "demo-skill",
        )
        self.assertFalse(triggered)
        self.assertIsNone(pending)
        self.assertEqual(payload, "")
        self.assertFalse(finished)

    def test_later_skill_invocation_is_detected_after_message_boundary(self):
        state = (False, None, "")
        events = [
            {"type": "stream_event", "event": {"type": "message_stop"}},
            {"type": "stream_event", "event": {"type": "content_block_start", "content_block": {"type": "tool_use", "name": "Skill"}}},
            {"type": "stream_event", "event": {"type": "content_block_delta", "delta": {"type": "input_json_delta", "partial_json": '{"skill":"demo-'}}},
            {"type": "stream_event", "event": {"type": "content_block_delta", "delta": {"type": "input_json_delta", "partial_json": 'skill"}'}}},
            {"type": "stream_event", "event": {"type": "content_block_stop"}},
            {"type": "result"},
        ]
        for event in events:
            state = process_stream_event(event, "demo-skill", *state)[:3]
        self.assertTrue(state[0])

    def test_assistant_fallback_checks_all_tools(self):
        state = process_stream_event(
            {"type": "assistant", "message": {"content": [
                {"type": "tool_use", "name": "Grep", "input": {}},
                {"type": "tool_use", "name": "Read", "input": {"file_path": ".claude/commands/demo-skill.md"}},
            ]}},
            "demo-skill",
        )
        self.assertTrue(state[0])
        self.assertFalse(state[3])


if __name__ == "__main__":
    unittest.main()
