#!/usr/bin/env python3
"""Config loader for the handoff skill.

Precedence (highest wins):
  1. Project config:  <cwd>/.handoff/config.json
  2. Global config:   ~/.config/handoff/config.json
  3. Built-in defaults

Also detects the setup-declined sentinel so the first-run prompt is shown at
most once per user.

Stdlib-only. Importable from other scripts.
"""


import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

GLOBAL_CONFIG_DIR = Path.home() / ".config" / "handoff"
GLOBAL_CONFIG_PATH = GLOBAL_CONFIG_DIR / "config.json"
GLOBAL_SETUP_DECLINED = GLOBAL_CONFIG_DIR / ".setup-declined"

PROJECT_CONFIG_DIRNAME = ".handoff"
PROJECT_CONFIG_FILENAME = "config.json"

DEFAULTS: dict[str, Any] = {
    "version": 1,
    "save_location": {"mode": "temp", "path": None},
    "retention_days": 7,
    "redaction": "strict",
    "include_git_context": True,
    "skill_recommendation_scope": "all",
    "filename_style": "mktemp",
    "setup_completed_at": None,
}


def project_config_path(cwd: Path | None = None) -> Path:
    cwd = cwd or Path.cwd()
    return cwd / PROJECT_CONFIG_DIRNAME / PROJECT_CONFIG_FILENAME


def _read_json(path: Path) -> dict[str, Any] | None:
    try:
        with path.open("r", encoding="utf-8") as f:
            data = json.load(f)
        if not isinstance(data, dict):
            return None
        return data
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None


def _deep_merge(base: dict[str, Any], override: dict[str, Any]) -> dict[str, Any]:
    out = dict(base)
    for k, v in override.items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = _deep_merge(out[k], v)
        else:
            out[k] = v
    return out


def load_config(cwd: Path | None = None) -> dict[str, Any]:
    """Return effective config = defaults <- global <- project."""
    config = dict(DEFAULTS)
    global_cfg = _read_json(GLOBAL_CONFIG_PATH)
    if global_cfg:
        config = _deep_merge(config, global_cfg)
    project_cfg = _read_json(project_config_path(cwd))
    if project_cfg:
        config = _deep_merge(config, project_cfg)
    return config


def setup_completed() -> bool:
    """True if global setup has run at least once."""
    cfg = _read_json(GLOBAL_CONFIG_PATH)
    return bool(cfg and cfg.get("setup_completed_at"))


def setup_declined() -> bool:
    """True if the user explicitly declined first-run setup."""
    return GLOBAL_SETUP_DECLINED.exists()


def should_prompt_setup(cwd: Path | None = None) -> bool:
    """Show 'Run setup now? (Y/n)' only if config absent AND not declined."""
    if setup_completed():
        return False
    if setup_declined():
        return False
    if _read_json(project_config_path(cwd)):
        return False
    return True


def mark_setup_declined() -> None:
    GLOBAL_CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    GLOBAL_SETUP_DECLINED.touch()


def write_global_config(config: dict[str, Any]) -> Path:
    GLOBAL_CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    with GLOBAL_CONFIG_PATH.open("w", encoding="utf-8") as f:
        json.dump(config, f, indent=2, sort_keys=True)
    if GLOBAL_SETUP_DECLINED.exists():
        try:
            GLOBAL_SETUP_DECLINED.unlink()
        except OSError:
            pass
    return GLOBAL_CONFIG_PATH


def write_project_config(config: dict[str, Any], cwd: Path | None = None) -> Path:
    path = project_config_path(cwd)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(config, f, indent=2, sort_keys=True)
    return path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Inspect handoff config.")
    parser.add_argument("--show", action="store_true", help="Print the effective config.")
    parser.add_argument("--status", action="store_true", help="Print setup status.")
    parser.add_argument("--sample", action="store_true", help="Print the built-in defaults.")
    args = parser.parse_args(argv)

    if args.sample:
        print(json.dumps(DEFAULTS, indent=2, sort_keys=True))
        return 0

    if args.status:
        print(
            json.dumps(
                {
                    "global_config_exists": GLOBAL_CONFIG_PATH.exists(),
                    "global_config_path": str(GLOBAL_CONFIG_PATH),
                    "project_config_exists": project_config_path().exists(),
                    "project_config_path": str(project_config_path()),
                    "setup_completed": setup_completed(),
                    "setup_declined": setup_declined(),
                    "should_prompt_setup": should_prompt_setup(),
                },
                indent=2,
            )
        )
        return 0

    if args.show or not any([args.sample, args.status]):
        print(json.dumps(load_config(), indent=2, sort_keys=True))
        return 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
