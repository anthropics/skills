from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path


CODEX_ROOT = Path(__file__).resolve().parents[1]
HOOK_PATH = CODEX_ROOT / "scripts" / "ars_codex_hook.py"
MANIFEST_PATH = CODEX_ROOT / "full-runtime-manifest.json"


def _load_hook():
    spec = importlib.util.spec_from_file_location("ars_codex_hook", HOOK_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(module)
    return module


def test_announce_reports_canonical_aliases_without_slashes() -> None:
    hook = _load_hook()
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))

    payload = hook.announce()

    assert payload["name"] == manifest["adapter"]["name"]
    assert "ars-plan" in payload["aliases"]
    assert "ars-reviewer" in payload["aliases"]
    assert all(not alias.startswith("/") for alias in payload["aliases"])
    assert len(payload["aliases"]) == len(set(payload["aliases"]))


def test_cli_announce_does_not_echo_environment_values(monkeypatch) -> None:
    monkeypatch.setenv("OPENAI_API_KEY", "sk-test-should-not-appear")

    result = subprocess.run(
        [sys.executable, str(HOOK_PATH), "announce"],
        check=True,
        capture_output=True,
        text=True,
    )

    assert "sk-test-should-not-appear" not in result.stdout
    payload = json.loads(result.stdout)
    assert payload["hooks"] == "opt-in with ARS_CODEX_HOOKS=1"
