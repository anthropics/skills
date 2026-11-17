"""Tests for run_eval.py trigger detection (issues #1552 and #1559).

These tests drive `run_single_query` with a fake `claude -p` subprocess
whose stdout is a real pipe fed canned stream-json events, so no Claude
Code installation is needed.

Bugs covered:
  #1552-1  the drained tail of the subprocess stream is never parsed, so
           a single-turn answer (common case) always scores "not triggered"
  #1552-2  parallel workers share one .claude/commands directory, so each
           claude -p sees N-1 other workers' skill copies and usually
           triggers a different one
  #1559-1  a non-skill first tool call (Bash orientation, git status, ls)
           ends the run before the skill can fire
  #1559-2  a different skill firing first also ends the run; only a
           positive match is conclusive

Run with:  python -m pytest skills/skill-creator/tests/
"""

import json
import os
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

TESTS_DIR = Path(__file__).resolve().parent
SKILL_CREATOR_DIR = TESTS_DIR.parent
sys.path.insert(0, str(SKILL_CREATOR_DIR))
sys.path.insert(0, str(SKILL_CREATOR_DIR / "scripts"))

from scripts import run_eval  # noqa: E402


# ---------------------------------------------------------------------------
# Stream event builders (Claude Code stream-json shapes)
# ---------------------------------------------------------------------------


def _event(se_type, **se_kwargs):
    return {"type": "stream_event", "event": {"type": se_type, **se_kwargs}}


def tool_start(name, tool_id="toolu_1"):
    return _event(
        "content_block_start",
        index=0,
        content_block={"type": "tool_use", "id": tool_id, "name": name, "input": {}},
    )


def tool_delta(partial_json):
    return _event(
        "content_block_delta",
        index=0,
        delta={"type": "input_json_delta", "partial_json": partial_json},
    )


def block_stop():
    return _event("content_block_stop", index=0)


def message_stop():
    return _event("message_stop")


def result_event():
    return {"type": "result", "subtype": "success", "result": ""}


def stream(*events) -> bytes:
    """Serialize events as newline-delimited stream-json bytes."""
    return ("\n".join(json.dumps(e) for e in events) + "\n").encode()


def skill_stream(clean_name, *, before=None, other_first=False):
    """A stream where the target skill is called (optionally after other
    tool calls / a different skill completing first)."""
    events: list[dict] = []
    if before:
        events.extend(before)
    if other_first:
        events.extend([
            tool_start("Skill", tool_id="toolu_other"),
            tool_delta('{"skill":"some-other-skill-00000000"}'),
            block_stop(),
        ])
    events.extend([
        tool_start("Skill"),
        tool_delta(f'{{"skill":"{clean_name}"}}'),
        block_stop(),
        result_event(),
    ])
    return stream(*events)


class FakeClaudeProcess:
    """A fake subprocess whose stdout is a real pipe with canned output.

    exit_after: number of poll() calls returning None before reporting
    exit. 0 = the process already exited (all output lands in one go,
    the drained-tail case); 1 = one streaming iteration, then exit.
    """

    def __init__(self, data: bytes, exit_after: int = 0):
        read_fd, write_fd = os.pipe()
        os.write(write_fd, data)
        os.close(write_fd)
        self.stdout = os.fdopen(read_fd, "rb", closefd=True)
        self._polls = 0
        self._exit_after = exit_after
        self.killed = False
        self.waited = False

    def poll(self):
        self._polls += 1
        if self._polls <= self._exit_after:
            return None
        return 0

    def kill(self):
        self.killed = True

    def wait(self):
        self.waited = True


@pytest.fixture
def fake_claude(monkeypatch):
    """Install a fake Popen; returns (install, captured_kwargs)."""

    captured = {}

    def install(data: bytes, exit_after: int = 0):
        proc = FakeClaudeProcess(data, exit_after=exit_after)

        def fake_popen(cmd, **kwargs):
            captured["cmd"] = cmd
            captured["kwargs"] = kwargs
            # Snapshot the per-run command file at spawn time (the real
            # run deletes it in cleanup).
            cwd = Path(kwargs["cwd"])
            commands_dir = cwd / ".claude" / "commands"
            captured["command_files"] = [
                f.name for f in commands_dir.glob("*.md")
            ] if commands_dir.is_dir() else []
            return proc

        monkeypatch.setattr(run_eval.subprocess, "Popen", fake_popen)
        # The streaming branch calls select on the pipe; force "readable"
        # so the test is portable (Windows select only handles sockets).
        monkeypatch.setattr(
            run_eval.select,
            "select",
            lambda r, w, x, timeout=None: (list(r), [], []),
        )
        return proc

    return install, captured


@pytest.fixture
def fixed_clean_name(monkeypatch):
    """Make the run's generated clean_name deterministic."""
    monkeypatch.setattr(
        run_eval.uuid, "uuid4", lambda: SimpleNamespace(hex="deadbeef12345678")
    )
    return "my-skill-skill-deadbeef"


def run(query="do the thing", project_root=None, tmp_path=None, timeout=10):
    root = str(project_root or tmp_path)
    return run_eval.run_single_query(
        query=query,
        skill_name="my-skill",
        skill_description="Does a thing.",
        timeout=timeout,
        project_root=root,
    )


def skill_call_stream(clean_name):
    """Minimal stream: the target skill is invoked and the run ends."""
    return stream(
        tool_start("Skill"),
        tool_delta(f'{{"skill":"{clean_name}"}}'),
        block_stop(),
        result_event(),
    )


# ---------------------------------------------------------------------------
# Drained tail is parsed (#1552-1)
# ---------------------------------------------------------------------------


def test_drained_tail_is_parsed(fake_claude, fixed_clean_name, tmp_path):
    """All output lands in one read after the process exits — the common
    single-turn case. The old code read the tail and never parsed it."""
    install, _ = fake_claude
    install(skill_call_stream(fixed_clean_name), exit_after=0)
    assert run(project_root=tmp_path) is True


def test_drained_tail_without_trigger_is_false(fake_claude, fixed_clean_name, tmp_path):
    install, _ = fake_claude
    install(stream(tool_start("Bash"), tool_delta('{"command":"ls"}'), block_stop(), result_event()), exit_after=0)
    assert run(project_root=tmp_path) is False


# ---------------------------------------------------------------------------
# Streaming branch still detects triggers
# ---------------------------------------------------------------------------


def test_streaming_chunks_are_parsed(fake_claude, fixed_clean_name, tmp_path):
    install, _ = fake_claude
    install(skill_call_stream(fixed_clean_name), exit_after=1)
    assert run(project_root=tmp_path) is True


# ---------------------------------------------------------------------------
# Non-skill first tool call is not a verdict (#1559-1)
# ---------------------------------------------------------------------------


def test_non_skill_first_tool_call_keeps_reading(fake_claude, fixed_clean_name, tmp_path):
    """The model opens with a Bash orientation call (git status), then
    calls the skill. Old code returned False on the Bash tool_use."""
    install, _ = fake_claude
    before = [
        tool_start("Bash", tool_id="toolu_bash"),
        tool_delta('{"command":"git status"}'),
        block_stop(),
    ]
    install(skill_stream(fixed_clean_name, before=before), exit_after=0)
    assert run(project_root=tmp_path) is True


def test_read_orientation_then_skill(fake_claude, fixed_clean_name, tmp_path):
    """A Read call before the skill must not end the run either."""
    install, _ = fake_claude
    before = [
        tool_start("Read", tool_id="toolu_read"),
        tool_delta('{"file_path":"CLAUDE.md"}'),
        block_stop(),
    ]
    install(skill_stream(fixed_clean_name, before=before), exit_after=0)
    assert run(project_root=tmp_path) is True


# ---------------------------------------------------------------------------
# A different skill completing first is not a verdict (#1559-2)
# ---------------------------------------------------------------------------


def test_other_skill_completing_first_keeps_reading(fake_claude, fixed_clean_name, tmp_path):
    """Another Skill block starts and completes before the target fires.
    Old code returned a verdict as soon as any Skill block completed."""
    install, _ = fake_claude
    install(skill_stream(fixed_clean_name, other_first=True), exit_after=0)
    assert run(project_root=tmp_path) is True


def test_message_stop_before_trigger_keeps_reading(fake_claude, fixed_clean_name, tmp_path):
    """A turn boundary (message_stop) before the skill fires must not be
    treated as a negative verdict."""
    install, _ = fake_claude
    before = [
        tool_start("Bash", tool_id="toolu_bash"),
        tool_delta('{"command":"pwd"}'),
        block_stop(),
        message_stop(),
    ]
    install(skill_stream(fixed_clean_name, before=before), exit_after=0)
    assert run(project_root=tmp_path) is True


# ---------------------------------------------------------------------------
# Per-run commands directory isolation (#1552-2 / #1559-3)
# ---------------------------------------------------------------------------


def test_command_file_lives_in_per_run_root(fake_claude, fixed_clean_name, tmp_path):
    install, captured = fake_claude
    install(skill_stream(fixed_clean_name), exit_after=0)

    assert run(project_root=tmp_path) is True

    cwd = Path(captured["kwargs"]["cwd"])
    # The run happened in its own .eval-runs/<id> root, not the project's
    # shared .claude/commands/ directory, and that root held exactly the
    # run's own command file.
    assert cwd.parent.name == ".eval-runs"
    assert cwd.name == "deadbeef"
    assert captured["command_files"] == [f"{fixed_clean_name}.md"]
    assert not (tmp_path / ".claude").exists()


def test_run_root_cleaned_up(fake_claude, fixed_clean_name, tmp_path):
    install, _ = fake_claude
    install(skill_stream(fixed_clean_name), exit_after=0)
    assert run(project_root=tmp_path) is True
    eval_runs = tmp_path / ".eval-runs"
    if eval_runs.exists():
        assert not any(eval_runs.iterdir()), "run roots must be removed after each query"


def test_two_runs_do_not_share_a_commands_dir(fake_claude, fixed_clean_name, monkeypatch, tmp_path):
    """Sequential runs each get their own root; the second must not see
    the first's command file (parallel workers use the same path)."""
    install, captured = fake_claude
    install(skill_stream(fixed_clean_name), exit_after=0)
    assert run(project_root=tmp_path) is True
    first_cwd = Path(captured["kwargs"]["cwd"])

    # Second run: a fresh uuid makes a fresh clean_name.
    install(skill_stream("my-skill-skill-0badf00d"), exit_after=0)
    monkeypatch.setattr(
        run_eval.uuid, "uuid4", lambda: SimpleNamespace(hex="0badf00d12345678")
    )
    assert run(project_root=tmp_path) is True
    second_cwd = Path(captured["kwargs"]["cwd"])

    assert first_cwd != second_cwd
    # The first run's command file was removed by its own cleanup.
    assert not (tmp_path / ".eval-runs").exists() or not any((tmp_path / ".eval-runs").iterdir())
