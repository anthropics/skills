"""Regression tests for the headless trigger stream.

These tests pin two integration details shared by the competing eval fixes:
orientation tools must not end a probe early, and the headless Claude process
must not inherit stdin.
"""

import io
import json
import subprocess
import unittest
from unittest import mock

from scripts.run_eval import run_single_query


def stream_event(event_type: str, **kwargs) -> bytes:
    return (
        json.dumps(
            {
                "type": "stream_event",
                "event": {"type": event_type, **kwargs},
            }
        )
        + "\n"
    ).encode()


class FakeProcess:
    def __init__(self, stdout: bytes, stderr: bytes = b""):
        self.stdout = io.BytesIO(stdout)
        self.stderr = io.BytesIO(stderr)
        self.returncode = None
        self.killed = False

    def poll(self):
        return self.returncode

    def kill(self):
        self.killed = True
        self.returncode = -9

    def wait(self, timeout=None):
        if self.returncode is None:
            self.returncode = 0
        return self.returncode


class StreamProbeTests(unittest.TestCase):
    def setUp(self):
        patcher = mock.patch("scripts.run_eval._stop_process_tree")
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_orientation_tool_then_skill_still_triggers_and_stdin_is_closed(self):
        output = b"".join(
            [
                stream_event(
                    "content_block_start",
                    content_block={"type": "tool_use", "name": "Bash"},
                ),
                stream_event(
                    "content_block_delta",
                    delta={
                        "type": "input_json_delta",
                        "partial_json": '{"command":"pwd"}',
                    },
                ),
                stream_event("content_block_stop"),
                stream_event(
                    "content_block_start",
                    content_block={"type": "tool_use", "name": "Skill"},
                ),
                stream_event(
                    "content_block_delta",
                    delta={
                        "type": "input_json_delta",
                        "partial_json": '{"skill":"pdf"}',
                    },
                ),
                stream_event("content_block_stop"),
            ]
        )
        process = FakeProcess(output)

        with mock.patch(
            "scripts.run_eval.subprocess.Popen", return_value=process
        ) as popen:
            triggered = run_single_query(
                query="inspect this PDF",
                eval_skill_name="pdf",
                timeout=2,
                eval_project_dir=".",
                claude_cli="/fake/claude",
            )

        self.assertTrue(triggered)
        self.assertIs(popen.call_args.kwargs["stdin"], subprocess.DEVNULL)

    def test_result_after_only_orientation_tools_is_not_triggered(self):
        output = b"".join(
            [
                stream_event(
                    "content_block_start",
                    content_block={"type": "tool_use", "name": "Glob"},
                ),
                stream_event(
                    "content_block_delta",
                    delta={
                        "type": "input_json_delta",
                        "partial_json": '{"pattern":"*.pdf"}',
                    },
                ),
                stream_event("content_block_stop"),
                (json.dumps({"type": "result"}) + "\n").encode(),
            ]
        )
        process = FakeProcess(output)

        with mock.patch("scripts.run_eval.subprocess.Popen", return_value=process):
            triggered = run_single_query(
                query="find files",
                eval_skill_name="pdf",
                timeout=2,
                eval_project_dir=".",
                claude_cli="/fake/claude",
            )

        self.assertFalse(triggered)


if __name__ == "__main__":
    unittest.main()
