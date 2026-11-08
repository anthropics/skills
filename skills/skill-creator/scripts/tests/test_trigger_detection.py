"""Offline tests for the eval's trigger detection.

The 0%-recall bug (#556) hid for months because nothing pinned the metric.
These tests pin the detection logic with no `claude` subprocess and no API
cost: they feed canned stream-json events to the pure functions. Run from
the skill-creator directory:

    python -m unittest scripts.tests.test_trigger_detection
"""

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.run_eval import _detect_trigger, _shadow_user_skill, _tool_use_mentions


def _skill_start(name):
    return {"type": "stream_event", "event": {"type": "content_block_start",
            "content_block": {"type": "tool_use", "name": name}}}


def _delta(partial):
    return {"type": "stream_event", "event": {"type": "content_block_delta",
            "delta": {"type": "input_json_delta", "partial_json": partial}}}


def _stop():
    return {"type": "stream_event", "event": {"type": "content_block_stop"}}


class TestToolUseMentions(unittest.TestCase):
    def test_skill_exact_match(self):
        self.assertTrue(_tool_use_mentions("pdf", "Skill", {"skill": "pdf"}))

    def test_skill_other_name(self):
        self.assertFalse(_tool_use_mentions("pdf", "Skill", {"skill": "docx"}))

    def test_read_inside_skill_dir(self):
        self.assertTrue(_tool_use_mentions(
            "pdf", "Read", {"file_path": "/home/u/.claude/skills/pdf/SKILL.md"}))

    def test_short_name_not_matched_in_filename(self):
        # A skill named "pdf" must not count reading report.pdf as a trigger.
        self.assertFalse(_tool_use_mentions("pdf", "Read", {"file_path": "report.pdf"}))

    def test_windows_backslash_path_normalized(self):
        self.assertTrue(_tool_use_mentions(
            "pdf", "Read", {"file_path": r"C:\Users\x\.claude\skills\pdf\SKILL.md"}))

    def test_non_skill_read_tool_ignored(self):
        self.assertFalse(_tool_use_mentions("pdf", "Bash", {"command": "cat report.pdf"}))


class TestDetectTrigger(unittest.TestCase):
    def test_streamed_skill_invocation(self):
        events = [_skill_start("Skill"), _delta('{"skill": "pd'), _delta('f"}'), _stop()]
        self.assertTrue(_detect_trigger(events, "pdf"))

    def test_explore_then_trigger(self):
        # A Bash detour before the Skill call is not a miss.
        events = [
            _skill_start("Bash"), _delta('{"command": "ls"}'), _stop(),
            _skill_start("Skill"), _delta('{"skill": "pdf"}'), _stop(),
        ]
        self.assertTrue(_detect_trigger(events, "pdf"))

    def test_result_without_trigger(self):
        events = [
            {"type": "assistant", "message": {"content": [{"type": "text", "text": "done"}]}},
            {"type": "result"},
        ]
        self.assertFalse(_detect_trigger(events, "pdf"))

    def test_short_name_filename_not_a_trigger(self):
        events = [_skill_start("Read"), _delta('{"file_path": "report.pdf"}'), _stop(),
                  {"type": "result"}]
        self.assertFalse(_detect_trigger(events, "pdf"))

    def test_assistant_fallback_path(self):
        events = [{"type": "assistant", "message": {"content": [
            {"type": "tool_use", "name": "Skill", "input": {"skill": "pdf"}}]}}]
        self.assertTrue(_detect_trigger(events, "pdf"))

    def test_malformed_delta_does_not_crash(self):
        events = [_skill_start("Skill"), _delta('{"skill": "pd'), _stop(), {"type": "result"}]
        self.assertFalse(_detect_trigger(events, "pdf"))


class TestShadowUserSkill(unittest.TestCase):
    """The crux fix: an installed same-name skill (user > project) must be
    moved aside during the run and always restored, so the eval measures the
    candidate. A fake HOME keeps this off the real ~/.claude."""

    def _fake_home_with_skill(self, tmp):
        skill = Path(tmp) / ".claude" / "skills" / "pdf"
        skill.mkdir(parents=True)
        (skill / "SKILL.md").write_text("installed")
        return Path(tmp), skill

    def test_moves_aside_then_restores(self):
        with tempfile.TemporaryDirectory() as tmp:
            home, skill = self._fake_home_with_skill(tmp)
            with mock.patch("scripts.run_eval.Path.home", return_value=home):
                with _shadow_user_skill("pdf"):
                    self.assertFalse(skill.exists())
                self.assertTrue(skill.exists())
                self.assertEqual((skill / "SKILL.md").read_text(), "installed")

    def test_restores_on_exception(self):
        with tempfile.TemporaryDirectory() as tmp:
            home, skill = self._fake_home_with_skill(tmp)
            with mock.patch("scripts.run_eval.Path.home", return_value=home):
                with self.assertRaises(RuntimeError), _shadow_user_skill("pdf"):
                    raise RuntimeError("boom")
                self.assertTrue(skill.exists())

    def test_restore_replaces_recreated_dir(self):
        with tempfile.TemporaryDirectory() as tmp:
            home, skill = self._fake_home_with_skill(tmp)
            with mock.patch("scripts.run_eval.Path.home", return_value=home):
                with _shadow_user_skill("pdf"):
                    skill.mkdir(parents=True)  # something re-creates it mid-run
                    (skill / "SKILL.md").write_text("recreated")
                # the original is restored, not buried under the re-created dir
                self.assertEqual((skill / "SKILL.md").read_text(), "installed")
                self.assertFalse((skill / "pdf").exists())

    def test_noop_when_not_installed(self):
        with tempfile.TemporaryDirectory() as tmp:
            with mock.patch("scripts.run_eval.Path.home", return_value=Path(tmp)):
                with _shadow_user_skill("pdf"):
                    pass


if __name__ == "__main__":
    unittest.main()
