"""Detect whether a `claude -p` stream-json run invoked a probe skill.

Uses --include-partial-messages events to decide early from stream events
(content_block_start) rather than waiting for the full assistant message,
which only arrives after tool execution.
"""

import json
import os
import select
import subprocess
import time
from collections.abc import Iterator

PROBE_TOOLS = ("Skill", "Read")
READ_CHUNK_BYTES = 8192
POLL_INTERVAL_SECONDS = 1.0


def watch_for_trigger(process: subprocess.Popen, probe_name: str, timeout: int) -> bool:
    """Read the process output until a verdict is reached or timeout expires.

    Kills the process on every exit path (verdict, timeout, exception).
    """
    detector = TriggerDetector(probe_name)
    try:
        for event in iter_stream_events(process, timeout):
            verdict = detector.classify(event)
            if verdict is not None:
                return verdict
        return False
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()


def iter_stream_events(process: subprocess.Popen, timeout: int) -> Iterator[dict]:
    """Yield parsed JSON events from the process stdout until EOF or timeout."""
    start_time = time.time()
    buffer = ""
    while time.time() - start_time < timeout:
        if process.poll() is not None:
            remaining = process.stdout.read()
            if remaining:
                buffer += remaining.decode("utf-8", errors="replace")
            yield from parse_json_lines(buffer)
            return

        ready, _, _ = select.select([process.stdout], [], [], POLL_INTERVAL_SECONDS)
        if not ready:
            continue

        chunk = os.read(process.stdout.fileno(), READ_CHUNK_BYTES)
        if not chunk:
            return
        buffer += chunk.decode("utf-8", errors="replace")
        while "\n" in buffer:
            line, buffer = buffer.split("\n", 1)
            yield from parse_json_lines(line)


def parse_json_lines(text: str) -> Iterator[dict]:
    """Yield every line of text that parses as JSON; skip the rest."""
    for line in text.split("\n"):
        line = line.strip()
        if not line:
            continue
        try:
            yield json.loads(line)
        except json.JSONDecodeError:
            continue


class TriggerDetector:
    """Decides from stream-json events whether the probe skill was invoked.

    Accumulates partial tool_use input across content_block_delta events so
    the verdict can be returned before the tool finishes running.
    """

    def __init__(self, probe_name: str):
        self.probe_name = probe_name
        self.pending_tool_name: str | None = None
        self.accumulated_json = ""

    def classify(self, event: dict) -> bool | None:
        """Return True/False once the event decides triggering, else None."""
        event_type = event.get("type")
        if event_type == "stream_event":
            return self._classify_stream_event(event.get("event", {}))
        if event_type == "assistant":
            return self._classify_assistant_message(event.get("message", {}))
        if event_type == "result":
            return False
        return None

    def _classify_stream_event(self, stream_event: dict) -> bool | None:
        se_type = stream_event.get("type", "")
        if se_type == "content_block_start":
            return self._start_tool_block(stream_event.get("content_block", {}))
        if se_type == "content_block_delta" and self.pending_tool_name:
            return self._accumulate_tool_input(stream_event.get("delta", {}))
        if se_type in ("content_block_stop", "message_stop"):
            if self.pending_tool_name:
                return self.probe_name in self.accumulated_json
            if se_type == "message_stop":
                return False
        return None

    def _start_tool_block(self, content_block: dict) -> bool | None:
        if content_block.get("type") != "tool_use":
            return None
        tool_name = content_block.get("name", "")
        if tool_name not in PROBE_TOOLS:
            return False
        self.pending_tool_name = tool_name
        self.accumulated_json = ""
        return None

    def _accumulate_tool_input(self, delta: dict) -> bool | None:
        if delta.get("type") != "input_json_delta":
            return None
        self.accumulated_json += delta.get("partial_json", "")
        if self.probe_name in self.accumulated_json:
            return True
        return None

    def _classify_assistant_message(self, message: dict) -> bool | None:
        """Fallback: decide from the first tool_use in a full assistant message."""
        for content_item in message.get("content", []):
            if content_item.get("type") != "tool_use":
                continue
            tool_name = content_item.get("name", "")
            tool_input = content_item.get("input", {})
            if tool_name == "Skill":
                return self.probe_name in tool_input.get("skill", "")
            if tool_name == "Read":
                return self.probe_name in tool_input.get("file_path", "")
            return False
        return None
