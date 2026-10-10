"""Regression tests for the skill-creator eval scripts.

Standard library only, so they run with `python -m unittest` from the
skill-creator directory without installing anything:

    cd skills/skill-creator && python -m unittest discover -s tests -v

Each test corresponds to a defect that made the eval harness report results
that looked valid but were not.
"""

import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SKILL_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SKILL_ROOT))

from scripts.run_eval import (  # noqa: E402
    TriggerDetector,
    detect_trigger,
    iter_process_lines,
    resolve_probe_name,
)
from scripts.utils import parse_skill_md  # noqa: E402


# A real `claude -p --output-format stream-json --include-partial-messages`
# fragment, recorded while evaluating a skill that was already installed.
# Note the Skill tool is invoked with the skill's REAL name.
RECORDED_SKILL_CALL = [
    json.dumps(e)
    for e in [
        {"type": "stream_event", "event": {"type": "content_block_start", "index": 1,
         "content_block": {"type": "tool_use", "id": "toolu_016RHCrFZW9n35pAYVv33Nrt",
                           "name": "Skill", "input": {}}}},
        {"type": "stream_event", "event": {"type": "content_block_delta", "index": 1,
         "delta": {"type": "input_json_delta", "partial_json": ""}}},
        {"type": "stream_event", "event": {"type": "content_block_delta", "index": 1,
         "delta": {"type": "input_json_delta", "partial_json": '{"skill": "git-rescue'}}},
        {"type": "stream_event", "event": {"type": "content_block_delta", "index": 1,
         "delta": {"type": "input_json_delta", "partial_json": '", "args": "three'}}},
        {"type": "stream_event", "event": {"type": "content_block_delta", "index": 1,
         "delta": {"type": "input_json_delta",
                   "partial_json": " commits landed on main, need to move them onto a branch"}}},
        {"type": "stream_event", "event": {"type": "content_block_delta", "index": 1,
         "delta": {"type": "input_json_delta", "partial_json": '"}'}}},
        {"type": "stream_event", "event": {"type": "content_block_stop", "index": 1}},
    ]
]


class TestInstalledSkillDetection(unittest.TestCase):
    """The probe name never appears when the skill under test is installed."""

    def test_probe_name_is_unique_when_skill_is_not_installed(self):
        self.assertEqual(
            resolve_probe_name("git-rescue", "abc12345", use_installed=False),
            "git-rescue-skill-abc12345",
        )

    def test_probe_name_is_the_real_name_when_skill_is_installed(self):
        self.assertEqual(
            resolve_probe_name("git-rescue", "abc12345", use_installed=True),
            "git-rescue",
        )

    def test_recorded_call_is_detected_under_the_real_skill_name(self):
        self.assertTrue(detect_trigger(RECORDED_SKILL_CALL, "git-rescue"))

    def test_recorded_call_is_missed_under_a_unique_probe_name(self):
        # This is the defect: an installed skill is invoked by its real name, so
        # matching on the generated probe name scores a genuine trigger as a miss
        # and the whole eval reports a 0.0 trigger rate.
        self.assertFalse(detect_trigger(RECORDED_SKILL_CALL, "git-rescue-skill-abc12345"))

    def test_unrelated_skill_name_does_not_match(self):
        self.assertFalse(detect_trigger(RECORDED_SKILL_CALL, "ship-pr"))

    def test_non_skill_tool_ends_detection(self):
        lines = [json.dumps(
            {"type": "stream_event", "event": {"type": "content_block_start", "index": 0,
             "content_block": {"type": "tool_use", "id": "t1", "name": "Bash", "input": {}}}}
        )]
        self.assertFalse(detect_trigger(lines, "git-rescue"))

    def test_malformed_lines_are_skipped(self):
        detector = TriggerDetector("git-rescue")
        self.assertIsNone(detector.feed("not json at all"))
        self.assertIsNone(detector.feed(""))

    def test_full_assistant_message_fallback(self):
        lines = [json.dumps({
            "type": "assistant",
            "message": {"content": [
                {"type": "tool_use", "name": "Skill", "input": {"skill": "git-rescue"}}
            ]},
        })]
        self.assertTrue(detect_trigger(lines, "git-rescue"))


class TestProcessLineStreaming(unittest.TestCase):
    """`select` cannot poll a pipe on Windows; it raises OSError there."""

    def test_lines_are_read_from_a_real_subprocess_pipe(self):
        script = (
            "import sys\n"
            "for i in range(3):\n"
            "    sys.stdout.write('{\"n\": %d}\\n' % i)\n"
            "    sys.stdout.flush()\n"
        )
        process = subprocess.Popen(
            [sys.executable, "-c", script], stdout=subprocess.PIPE
        )
        try:
            lines = [
                line
                for line in iter_process_lines(process.stdout, lambda: True)
                if line.strip()
            ]
        finally:
            if process.poll() is None:
                process.kill()
            process.wait()
            process.stdout.close()

        self.assertEqual([json.loads(line)["n"] for line in lines], [0, 1, 2])

    def test_deadline_check_stops_iteration(self):
        process = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(30)"],
            stdout=subprocess.PIPE,
        )
        try:
            lines = list(
                iter_process_lines(process.stdout, lambda: False, poll_interval=0.01)
            )
        finally:
            if process.poll() is None:
                process.kill()
            process.wait()
            process.stdout.close()
        self.assertEqual(lines, [])


class TestNonAsciiSkillFiles(unittest.TestCase):
    """Reading without an explicit encoding fails wherever the locale is not UTF-8."""

    NON_ASCII_BODY = (
        "---\n"
        "name: sample-skill\n"
        "description: Uses an em dash — plus curly quotes “like this” "
        "and an arrow → in the description.\n"
        "---\n\n"
        "# Sample\n\nBody text — more punctuation ‘here’.\n"
    )

    def test_parse_skill_md_reads_non_ascii_content(self):
        with tempfile.TemporaryDirectory() as tmp:
            skill_dir = Path(tmp) / "sample-skill"
            skill_dir.mkdir()
            (skill_dir / "SKILL.md").write_text(self.NON_ASCII_BODY, encoding="utf-8")

            name, description, content = parse_skill_md(skill_dir)

        self.assertEqual(name, "sample-skill")
        self.assertIn("—", description)
        self.assertIn("‘here’", content)

    def test_scripts_never_open_files_without_an_encoding(self):
        offenders = []
        pattern = re.compile(r"\.read_text\(\)|\.write_text\(|with open\(")
        for directory in ("scripts", "eval-viewer"):
            for path in sorted((SKILL_ROOT / directory).glob("*.py")):
                for lineno, line in enumerate(
                    path.read_text(encoding="utf-8").splitlines(), 1
                ):
                    if "encoding=" in line or '"rb"' in line or '"wb"' in line:
                        continue
                    if pattern.search(line):
                        offenders.append(
                            "%s:%d: %s" % (path.name, lineno, line.strip())
                        )

        self.assertEqual(
            offenders,
            [],
            "file IO without an explicit encoding will fail on non-UTF-8 locales:\n"
            + "\n".join(offenders),
        )


def _tool_start(name, index=0):
    return json.dumps({
        "type": "stream_event",
        "event": {"type": "content_block_start", "index": index,
                  "content_block": {"type": "tool_use", "id": "t%d" % index,
                                    "name": name, "input": {}}},
    })


def _input_delta(fragment, index=0):
    return json.dumps({
        "type": "stream_event",
        "event": {"type": "content_block_delta", "index": index,
                  "delta": {"type": "input_json_delta", "partial_json": fragment}},
    })


def _block_stop(index=0):
    return json.dumps({
        "type": "stream_event",
        "event": {"type": "content_block_stop", "index": index},
    })


def _message_stop():
    return json.dumps({
        "type": "stream_event",
        "event": {"type": "message_stop"},
    })


def _result():
    return json.dumps({"type": "result", "subtype": "success"})


# Assembled from the event shapes in RECORDED_SKILL_CALL, reordered so the Skill
# call lands after an inspection step. Every capture I took showed Claude
# invoking the skill first, so this ordering is constructed rather than recorded.
BASH_THEN_SKILL = (
    [_tool_start("Bash", 0), _input_delta('{"command": "git status"}', 0), _block_stop(0)]
    + [_message_stop()]
    + [_tool_start("Skill", 1), _input_delta('{"skill": "git-rescue"}', 1), _block_stop(1)]
    + [_result()]
)

BASH_ONLY = (
    [_tool_start("Bash", 0), _input_delta('{"command": "git status"}', 0), _block_stop(0)]
    + [_message_stop()]
    + [_tool_start("Bash", 1), _input_delta('{"command": "git log"}', 1), _block_stop(1)]
    + [_result()]
)


class TestScanFullTurn(unittest.TestCase):
    """Detection gives up at the first non-Skill tool unless scan_full_turn is set."""

    def test_default_mode_misses_a_skill_invoked_after_another_tool(self):
        self.assertFalse(detect_trigger(BASH_THEN_SKILL, "git-rescue"))

    def test_scan_full_turn_finds_a_skill_invoked_after_another_tool(self):
        self.assertTrue(
            detect_trigger(BASH_THEN_SKILL, "git-rescue", scan_full_turn=True)
        )

    def test_scan_full_turn_still_reports_a_miss_when_no_skill_fires(self):
        self.assertFalse(detect_trigger(BASH_ONLY, "git-rescue", scan_full_turn=True))

    def test_scan_full_turn_does_not_match_a_different_skill(self):
        self.assertFalse(
            detect_trigger(BASH_THEN_SKILL, "ship-pr", scan_full_turn=True)
        )

    def test_scan_full_turn_leaves_a_first_position_skill_call_detected(self):
        self.assertTrue(
            detect_trigger(RECORDED_SKILL_CALL, "git-rescue", scan_full_turn=True)
        )

    def test_default_mode_is_unchanged_on_the_recorded_transcript(self):
        self.assertTrue(detect_trigger(RECORDED_SKILL_CALL, "git-rescue"))
        self.assertFalse(detect_trigger(RECORDED_SKILL_CALL, "git-rescue-skill-abc12345"))


if __name__ == "__main__":
    unittest.main()
