"""Probe isolation tests for ``scripts/run_eval.py``.

Each ``run_single_query`` call must write its probe command file into a
fresh temporary project directory, run ``claude -p`` with that directory as
``cwd``, and remove the directory afterwards. Without that, parallel workers
see each other's probes and the measured trigger rate is wrong, and a run
from a directory under ``~`` leaks probes into ``~/.claude/commands/``.

``subprocess.Popen`` is replaced by a fake that records the ``cwd`` it was
given and feeds one stream-json event back through a real pipe.
"""

import json
import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from scripts import run_eval

SKILL_NAME = "demo-skill"
DESCRIPTION = "Demo skill. Use when the user asks for a demo."
TIMEOUT_SECONDS = 5


def probe_files(project_dir: Path) -> list[Path]:
    return sorted((project_dir / ".claude" / "commands").glob(f"{SKILL_NAME}-skill-*.md"))


def trigger_event(probe_name: str) -> bytes:
    event = {
        "type": "assistant",
        "message": {"content": [{"type": "tool_use", "name": "Skill", "input": {"skill": probe_name}}]},
    }
    return (json.dumps(event) + "\n").encode()


class FakePopen:
    """Stand-in for a finished ``claude -p`` process that triggered its probe."""

    launches: list[dict] = []

    def __init__(self, cmd, cwd, **_ignored):
        project_dir = Path(cwd)
        probes = probe_files(project_dir)
        FakePopen.launches.append({
            "cwd": project_dir,
            "cwd_existed": project_dir.is_dir(),
            "probes": probes,
        })
        read_fd, write_fd = os.pipe()
        with os.fdopen(write_fd, "wb") as writer:
            writer.write(trigger_event(probes[0].stem) if probes else b"")
        self.stdout = os.fdopen(read_fd, "rb")

    def poll(self):
        return 0

    def kill(self):
        pass

    def wait(self):
        return 0


@pytest.fixture
def fake_popen(monkeypatch, tmp_path):
    FakePopen.launches = []
    monkeypatch.setattr(subprocess, "Popen", FakePopen)
    monkeypatch.setattr(tempfile, "tempdir", str(tmp_path))
    return FakePopen


def run_once() -> bool:
    return run_eval.run_single_query("show me a demo", SKILL_NAME, DESCRIPTION, TIMEOUT_SECONDS)


def test_probe_is_written_into_fresh_directory_passed_as_cwd(fake_popen, tmp_path):
    entries_before = set(tmp_path.iterdir())

    triggered = run_once()

    launch = fake_popen.launches[0]
    assert triggered is True
    assert launch["cwd_existed"]
    assert launch["cwd"] not in entries_before
    assert launch["cwd"].parent == tmp_path
    assert len(launch["probes"]) == 1


def test_probe_directory_is_removed_after_the_call(fake_popen):
    run_once()

    assert not fake_popen.launches[0]["cwd"].exists()


def test_probe_directory_is_removed_when_popen_raises(monkeypatch, tmp_path):
    monkeypatch.setattr(tempfile, "tempdir", str(tmp_path))
    seen: list[Path] = []

    def exploding_popen(cmd, cwd, **_ignored):
        seen.append(Path(cwd))
        raise OSError("claude not found")

    monkeypatch.setattr(subprocess, "Popen", exploding_popen)

    with pytest.raises(OSError):
        run_once()

    assert seen and not seen[0].exists()


def test_sequential_calls_use_different_directories(fake_popen):
    run_once()
    run_once()

    cwds = [launch["cwd"] for launch in fake_popen.launches]
    assert len(cwds) == 2
    assert cwds[0] != cwds[1]


def test_nothing_is_written_under_home_claude_commands(fake_popen, monkeypatch, tmp_path):
    home = tmp_path / "home"
    global_commands = home / ".claude" / "commands"
    global_commands.mkdir(parents=True)
    workdir = home / "plugins" / "skill-creator"
    workdir.mkdir(parents=True)
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.chdir(workdir)

    run_once()

    assert list(global_commands.iterdir()) == []
    assert not (workdir / ".claude").exists()


def test_probe_name_is_unique_per_call(fake_popen):
    run_once()
    run_once()

    names = [launch["probes"][0].name for launch in fake_popen.launches]
    assert names[0] != names[1]
    assert all(name.startswith(f"{SKILL_NAME}-skill-") for name in names)


def test_probe_command_file_embeds_the_description(fake_popen, monkeypatch):
    captured: dict[str, str] = {}
    original_init = FakePopen.__init__

    def capturing_init(self, cmd, cwd, **kwargs):
        original_init(self, cmd, cwd, **kwargs)
        captured["text"] = probe_files(Path(cwd))[0].read_text()

    monkeypatch.setattr(FakePopen, "__init__", capturing_init)

    run_once()

    assert captured["text"].startswith("---\ndescription: |\n")
    assert DESCRIPTION in captured["text"]


def test_run_eval_module_has_no_project_root_discovery():
    assert not hasattr(run_eval, "find_project_root")


def test_popen_receives_claude_command_with_query(fake_popen, monkeypatch):
    recorded: dict[str, list] = {}
    original_init = FakePopen.__init__

    def recording_init(self, cmd, cwd, **kwargs):
        recorded["cmd"] = cmd
        original_init(self, cmd, cwd, **kwargs)

    monkeypatch.setattr(FakePopen, "__init__", recording_init)

    run_once()

    assert recorded["cmd"][:3] == ["claude", "-p", "show me a demo"]
    assert "--include-partial-messages" in recorded["cmd"]
