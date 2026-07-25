#!/usr/bin/env python3
"""Safe Codex hook wrapper for ARS.

The wrapper is read-only by design. It prints adapter metadata and does not
inspect environment variables, network, shell history, or user files.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


SCRIPT = Path(__file__).resolve()
CODEX_ROOT = SCRIPT.parents[1]
MANIFEST = CODEX_ROOT / "full-runtime-manifest.json"


def announce() -> dict[str, object]:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    aliases: list[str] = []
    for command in manifest["commands"]:
        for alias in command["aliases"]:
            normalized = alias.lstrip("/")
            if normalized not in aliases:
                aliases.append(normalized)
    return {
        "name": manifest["adapter"]["name"],
        "full_runtime": "opt-in with ARS_CODEX_FULL_RUNTIME=1",
        "agent_team": "opt-in with ARS_CODEX_AGENT_TEAM=1",
        "hooks": "opt-in with ARS_CODEX_HOOKS=1",
        "aliases": aliases,
        "note": "Hook wrapper is read-only and does not print secrets or mutate files.",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["announce"])
    args = parser.parse_args()
    if args.action == "announce":
        print(json.dumps(announce(), ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
