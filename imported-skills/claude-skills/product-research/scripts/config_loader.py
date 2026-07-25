#!/usr/bin/env python3
"""config_loader.py - Customization loader for the product-research skill.

Stdlib-only. Importable from the skill's other scripts. Precedence (highest wins):
  1. Project config:  <cwd>/.research-ops/product-research.json
  2. Global config:   ~/.config/research-ops/product-research.json
  3. Built-in DEFAULTS

Onboarding answers (written by onboard.py) live in these files; every tool in this
skill reads them so the user's customization applies automatically.
Set RESEARCH_OPS_NO_CONFIG=1 to ignore saved config.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any

SKILL = "product-research"

GLOBAL_CONFIG_DIR = Path.home() / ".config" / "research-ops"
GLOBAL_CONFIG_PATH = GLOBAL_CONFIG_DIR / f"{SKILL}.json"
PROJECT_CONFIG_DIRNAME = ".research-ops"

DEFAULTS: dict[str, Any] = {
    "version": 1,
    "skill": SKILL,
    "default_profile": "b2b-saas",
    "insight_min_sources": 3,
    "default_method": "usability",
    "stakes_high": False,
    "setup_completed_at": None,
}


def project_config_path(cwd: Path | None = None) -> Path:
    cwd = cwd or Path.cwd()
    return cwd / PROJECT_CONFIG_DIRNAME / f"{SKILL}.json"


def _read_json(path: Path) -> dict[str, Any] | None:
    try:
        with path.open(encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else None
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
    config = dict(DEFAULTS)
    if os.environ.get("RESEARCH_OPS_NO_CONFIG") == "1":
        return config
    global_cfg = _read_json(GLOBAL_CONFIG_PATH)
    if global_cfg:
        config = _deep_merge(config, global_cfg)
    project_cfg = _read_json(project_config_path(cwd))
    if project_cfg:
        config = _deep_merge(config, project_cfg)
    return config


def setup_completed() -> bool:
    cfg = _read_json(GLOBAL_CONFIG_PATH) or _read_json(project_config_path())
    return bool(cfg and cfg.get("setup_completed_at"))


def write_config(config: dict[str, Any], scope: str = "global", cwd: Path | None = None) -> Path:
    path = project_config_path(cwd) if scope == "project" else GLOBAL_CONFIG_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as f:
        json.dump(config, f, indent=2, sort_keys=True)
    return path


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=f"Inspect {SKILL} customization config.")
    p.add_argument("--show", action="store_true", help="Print the effective config")
    p.add_argument("--status", action="store_true", help="Print setup status + paths")
    p.add_argument("--sample", action="store_true", help="Print the built-in defaults")
    args = p.parse_args(argv)

    if args.sample:
        print(json.dumps(DEFAULTS, indent=2, sort_keys=True))
    elif args.status:
        print(json.dumps({
            "skill": SKILL,
            "global_config_path": str(GLOBAL_CONFIG_PATH),
            "global_config_exists": GLOBAL_CONFIG_PATH.exists(),
            "project_config_path": str(project_config_path()),
            "project_config_exists": project_config_path().exists(),
            "setup_completed": setup_completed(),
        }, indent=2))
    else:
        print(json.dumps(load_config(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
