"""Shared helpers for script unit tests.

Avoid duplicating subprocess.run boilerplate across multiple test files.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any


def run_script(
    script_path: Path,
    *args: str,
    cwd: Path | None = None,
    extra_env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    """Invoke a script via subprocess, capturing stdout/stderr as text.

    extra_env values are merged into os.environ (not replaced).
    """
    if args and not all(isinstance(a, str) for a in args):
        raise TypeError(f"All positional args must be str, got {args!r}")
    env = os.environ.copy()
    if extra_env:
        env.update(extra_env)
    return subprocess.run(
        [sys.executable, str(script_path), *args],
        capture_output=True,
        text=True,
        cwd=cwd,
        env=env,
    )


def load_module_from_path(name: str, path: Path):
    """Import a script file as a module (for unit-testing its functions).

    Centralises the spec_from_file_location -> module_from_spec ->
    exec_module boilerplate. Six pre-existing test files carry local copies
    under various names (_load, _load_lint, _load_module) — they can migrate
    at next edit; new test files should call this.
    """
    import importlib.util

    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_skill_linter(script_path: Path, root: Path) -> subprocess.CompletedProcess[str]:
    """Invoke a SKILL.md linter (--path arg + PYTHONPATH=scripts/)."""
    return run_script(
        script_path,
        "--path",
        str(root),
        extra_env={"PYTHONPATH": str(script_path.parent)},
    )


def load_json_schema(path: Path) -> dict[str, Any]:
    """Load a JSON Schema file and verify it parses as Draft 2020-12.

    Centralised so test files don't re-implement the same load + check_schema
    pair. Mirrors the helper at scripts/check_literature_corpus_schema.py
    (which predates this module) — that script can migrate at next edit.
    """
    from jsonschema import Draft202012Validator

    with path.open("r", encoding="utf-8") as f:
        schema = json.load(f)
    Draft202012Validator.check_schema(schema)
    return schema


def build_schema_validator(schema: dict[str, Any]):
    """Construct a Draft 2020-12 validator with format checking enabled.

    Without format_checker, format keywords (date-time on verified_at /
    acknowledged_at / generated_at) validate silently — a hole codex flagged
    in T3 review of literature_corpus_entry.schema.json.
    """
    from jsonschema import Draft202012Validator

    return Draft202012Validator(
        schema, format_checker=Draft202012Validator.FORMAT_CHECKER
    )
