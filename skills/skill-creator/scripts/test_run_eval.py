"""Tests for trigger detection in run_eval.

`run_single_query` decides whether a skill triggered by reading the `claude -p`
event stream. These tests replay recorded streams through a real OS pipe, so
select() and os.read() behave as they do against a live subprocess and only the
bytes are scripted. No API calls are made.

Run with: python -m unittest skills.skill_creator.scripts.test_run_eval
or directly: python scripts/test_run_eval.py
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scripts import run_eval


def _stream_event(event: dict) -> dict:
    return {"type": "stream_event", "event": event}


def _tool_start(name: str) -> dict:
    return _stream_event(
        {"type": "content_block_start", "content_block": {"type": "tool_use", "name": name}}
    )


def _tool_input(partial_json: str) -> dict:
    return _stream_event(
        {"type": "content_block_delta", "delta": {"type": "input_json_delta", "partial_json": partial_json}}
    )


def _block_stop() -> dict:
    return _stream_event({"type": "content_block_stop"})


class _PipeStdout:
    """A real pipe holding the scripted output, so fileno() works for select()."""

    def __init__(self, payload: bytes):
        self._read_fd, write_fd = os.pipe()
        os.write(write_fd, payload)
        os.close(write_fd)

    def fileno(self) -> int:
        return self._read_fd

    def read(self) -> bytes:
        return b""


class _PipeProcess:
    """Stands in for the `claude -p` child. EOF on the pipe ends the read loop."""

    def __init__(self, events: list):
        payload = "".join(json.dumps(e) + "\n" for e in events).encode()
        self.stdout = _PipeStdout(payload)

    def poll(self):
        return None

    def kill(self):
        pass

    def wait(self):
        pass


class TriggerDetectionTest(unittest.TestCase):
    """The skill is invoked in every case below except the last one."""

    def _run(self, build_events) -> bool:
        with tempfile.TemporaryDirectory() as project_root:
            original_popen = subprocess.Popen

            def fake_popen(cmd, **kwargs):
                commands = Path(kwargs.get("cwd", ".")) / ".claude" / "commands"
                names = [p.stem for p in commands.glob("*-skill-*.md")]
                return _PipeProcess(build_events(names[0] if names else "unknown"))

            subprocess.Popen = fake_popen
            try:
                return run_eval.run_single_query(
                    query="a representative query",
                    skill_name="demo",
                    skill_description="a description",
                    timeout=10,
                    project_root=project_root,
                    model=None,
                )
            finally:
                subprocess.Popen = original_popen

    def test_another_tool_before_the_skill_is_not_disproof(self):
        """A concrete query makes the model orient itself with Bash or Grep first."""
        triggered = self._run(lambda name: [
            _tool_start("Bash"),
            _block_stop(),
            _tool_start("Skill"),
            _tool_input('{"skill": "%s"}' % name),
            _block_stop(),
            {"type": "result"},
        ])
        self.assertTrue(triggered)

    def test_unrelated_read_before_the_skill_is_not_disproof(self):
        """The first closed block must not decide the whole query."""
        triggered = self._run(lambda name: [
            _tool_start("Read"),
            _tool_input('{"file_path": "/tmp/unrelated.md"}'),
            _block_stop(),
            _tool_start("Skill"),
            _tool_input('{"skill": "%s"}' % name),
            _block_stop(),
            {"type": "result"},
        ])
        self.assertTrue(triggered)

    def test_skill_found_beyond_the_first_tool_of_a_message(self):
        """The non-streaming fallback must walk the whole assistant message."""
        triggered = self._run(lambda name: [
            {"type": "assistant", "message": {"content": [
                {"type": "tool_use", "name": "Bash", "input": {"command": "ls"}},
                {"type": "tool_use", "name": "Skill", "input": {"skill": name}},
            ]}},
            {"type": "result"},
        ])
        self.assertTrue(triggered)

    def test_a_skill_that_never_runs_is_still_reported_as_untriggered(self):
        """The negative case the other three must not break."""
        triggered = self._run(lambda name: [
            _tool_start("Bash"),
            _block_stop(),
            _tool_start("Read"),
            _tool_input('{"file_path": "/tmp/unrelated.md"}'),
            _block_stop(),
            {"type": "result"},
        ])
        self.assertFalse(triggered)


if __name__ == "__main__":
    unittest.main()
