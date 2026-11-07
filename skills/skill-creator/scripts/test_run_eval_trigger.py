"""Tests for the trigger-detection state machine in run_eval.py.

Covers the bugs from anthropics/skills#1721 ("skill-creator: trigger
detection reports 0% recall for every skill"):

1. Seeing a non-Skill/Read tool_use (e.g. Bash, Glob, Grep) used to inspect
   files before the skill must NOT immediately end detection with False.
2. `content_block_stop` / `message_stop` must not prematurely finalize the
   result when a *later* content block or message still invokes the skill.
3. The fallback "assistant" message handler must scan every content item in
   the message, not bail out after the first tool_use it finds.
4. Only a `result` event (or end of stream) with no skill tool_use seen so
   far should produce a final `False`.

Run with:
    cd skills/skill-creator && python3 -m unittest scripts.test_run_eval_trigger
    cd skills/skill-creator && python3 -m pytest scripts/test_run_eval_trigger.py
"""

import unittest

try:
    from scripts.run_eval import TriggerDetector
except ImportError:
    from run_eval import TriggerDetector

CLEAN_NAME = "my-skill-skill-abc12345"


def stream_event(se_type: str, **kwargs) -> dict:
    return {"type": "stream_event", "event": {"type": se_type, **kwargs}}


def tool_use_start(name: str) -> dict:
    return stream_event(
        "content_block_start",
        content_block={"type": "tool_use", "name": name},
    )


def input_delta(partial_json: str) -> dict:
    return stream_event(
        "content_block_delta",
        delta={"type": "input_json_delta", "partial_json": partial_json},
    )


def block_stop() -> dict:
    return stream_event("content_block_stop")


def message_stop() -> dict:
    return stream_event("message_stop")


def result_event(triggered: bool = False) -> dict:
    return {"type": "result"}


def assistant_message(*content) -> dict:
    return {"type": "assistant", "message": {"content": list(content)}}


def tool_use_block(name: str, **input_fields) -> dict:
    return {"type": "tool_use", "name": name, "input": input_fields}


class TriggerDetectorStreamEventTests(unittest.TestCase):
    """Bug #1 & #2: non-skill tools and block/message stops shouldn't kill detection."""

    def feed(self, detector: TriggerDetector, events: list[dict]):
        outcome = None
        for event in events:
            outcome = detector.process_event(event)
            if outcome is not None:
                return outcome
        return outcome

    def test_bash_then_skill_triggers(self):
        """Model inspects files with Bash/Glob/Grep, then calls Skill: must be True."""
        detector = TriggerDetector(CLEAN_NAME)
        events = [
            tool_use_start("Bash"),
            input_delta('{"command": "ls"}'),
            block_stop(),
            tool_use_start("Glob"),
            input_delta('{"pattern": "*.py"}'),
            block_stop(),
            tool_use_start("Skill"),
            input_delta('{"skill": "' + CLEAN_NAME),
            input_delta('"}'),
        ]
        outcome = self.feed(detector, events)
        self.assertTrue(outcome)
        self.assertTrue(detector.triggered)

    def test_bash_only_no_skill_returns_false_at_result(self):
        """Non-skill tool used, no Skill call ever happens -> False only at result."""
        detector = TriggerDetector(CLEAN_NAME)
        events = [
            tool_use_start("Bash"),
            input_delta('{"command": "ls"}'),
            block_stop(),
        ]
        # Still undetermined mid-stream -- must NOT be False yet.
        outcome = self.feed(detector, events)
        self.assertIsNone(outcome)

        outcome = detector.process_event(result_event())
        self.assertFalse(outcome)

    def test_single_non_skill_tool_start_does_not_return_false(self):
        """Regression for the literal `else: return False` bug: seeing one
        non-Skill/Read tool_use content_block_start must not itself resolve
        the detector to False."""
        detector = TriggerDetector(CLEAN_NAME)
        outcome = detector.process_event(tool_use_start("Bash"))
        self.assertIsNone(outcome)

    def test_message_stop_does_not_finalize_false(self):
        """A message_stop with no skill seen yet must not finalize to False;
        only `result` (or end of stream) is conclusive."""
        detector = TriggerDetector(CLEAN_NAME)
        events = [
            tool_use_start("Bash"),
            input_delta('{"command": "ls"}'),
            block_stop(),
            message_stop(),
        ]
        outcome = self.feed(detector, events)
        self.assertIsNone(outcome)

    def test_skill_in_second_message_after_message_stop(self):
        """Skill call arrives in a second assistant message after an earlier
        message_stop for an unrelated tool -- must still be detected."""
        detector = TriggerDetector(CLEAN_NAME)
        events = [
            tool_use_start("Bash"),
            input_delta('{"command": "ls"}'),
            block_stop(),
            message_stop(),
            tool_use_start("Skill"),
            input_delta('{"skill": "' + CLEAN_NAME + '"}'),
        ]
        outcome = self.feed(detector, events)
        self.assertTrue(outcome)

    def test_content_block_stop_without_match_does_not_finalize(self):
        detector = TriggerDetector(CLEAN_NAME)
        events = [
            tool_use_start("Read"),
            input_delta('{"file_path": "/tmp/unrelated.txt"}'),
            block_stop(),
        ]
        outcome = self.feed(detector, events)
        self.assertIsNone(outcome)
        self.assertFalse(detector.triggered)

    def test_read_matching_skill_file_triggers_on_block_stop(self):
        detector = TriggerDetector(CLEAN_NAME)
        events = [
            tool_use_start("Read"),
            input_delta('{"file_path": "/proj/.claude/commands/' + CLEAN_NAME + '.md"}'),
        ]
        outcome = self.feed(detector, events)
        self.assertTrue(outcome)


class TriggerDetectorAssistantFallbackTests(unittest.TestCase):
    """Bug #3: the assistant-message fallback must scan every content item."""

    def test_scans_past_first_non_matching_tool_use(self):
        """Regression for `return triggered` sitting inside the for-loop:
        a Bash call followed by the Skill call in the same assistant message
        must be detected, not short-circuited on the first item."""
        detector = TriggerDetector(CLEAN_NAME)
        message = assistant_message(
            {"type": "text", "text": "Let me check the files first."},
            tool_use_block("Bash", command="ls"),
            tool_use_block("Skill", skill=CLEAN_NAME),
        )
        outcome = detector.process_event(message)
        self.assertTrue(outcome)
        self.assertTrue(detector.triggered)

    def test_scans_past_multiple_non_matching_tools(self):
        detector = TriggerDetector(CLEAN_NAME)
        message = assistant_message(
            tool_use_block("Bash", command="ls"),
            tool_use_block("Glob", pattern="*.py"),
            tool_use_block("Grep", pattern="foo"),
            tool_use_block("Read", file_path=f"/proj/.claude/commands/{CLEAN_NAME}.md"),
        )
        outcome = detector.process_event(message)
        self.assertTrue(outcome)

    def test_no_matching_tool_use_returns_none_not_false(self):
        """A message with only unrelated tool calls should leave the outcome
        undetermined (None) so the caller keeps waiting for `result`, rather
        than concluding False after just one assistant message."""
        detector = TriggerDetector(CLEAN_NAME)
        message = assistant_message(
            tool_use_block("Bash", command="ls"),
            tool_use_block("Glob", pattern="*.py"),
        )
        outcome = detector.process_event(message)
        self.assertIsNone(outcome)
        self.assertFalse(detector.triggered)

    def test_unrelated_skill_name_does_not_match_substring_false_positive(self):
        detector = TriggerDetector(CLEAN_NAME)
        message = assistant_message(
            tool_use_block("Skill", skill="some-other-skill-def99999"),
        )
        outcome = detector.process_event(message)
        self.assertIsNone(outcome)
        self.assertFalse(detector.triggered)


class TriggerDetectorResultFinalizationTests(unittest.TestCase):
    """Bug #4: only `result` (or end of stream) with nothing found should be False."""

    def test_result_with_no_tool_use_is_false(self):
        detector = TriggerDetector(CLEAN_NAME)
        outcome = detector.process_event(result_event())
        self.assertFalse(outcome)

    def test_result_after_skill_triggered_is_true(self):
        detector = TriggerDetector(CLEAN_NAME)
        detector.process_event(tool_use_start("Skill"))
        detector.process_event(input_delta('{"skill": "' + CLEAN_NAME + '"}'))
        outcome = detector.process_event(result_event())
        self.assertTrue(outcome)

    def test_end_of_stream_without_result_uses_triggered_flag(self):
        """When the process exits before a `result` event arrives (e.g. it
        hit the timeout or the CLI didn't emit one), the caller falls back to
        `detector.triggered`, which must reflect the true state."""
        detector = TriggerDetector(CLEAN_NAME)
        detector.process_event(tool_use_start("Bash"))
        detector.process_event(input_delta('{"command": "ls"}'))
        detector.process_event(block_stop())
        self.assertFalse(detector.triggered)

        detector2 = TriggerDetector(CLEAN_NAME)
        detector2.process_event(tool_use_start("Skill"))
        detector2.process_event(input_delta('{"skill": "' + CLEAN_NAME + '"}'))
        self.assertTrue(detector2.triggered)


if __name__ == "__main__":
    unittest.main()
