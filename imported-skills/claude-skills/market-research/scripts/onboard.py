#!/usr/bin/env python3
"""onboard.py - Onboarding questionnaire for the market-research skill.

Stdlib-only. Asks the user a short set of questions BEFORE they size a market or field
a survey, then writes the answers to a customization config read by every tool in this
skill via config_loader.py. The answers become defaults for profile, survey confidence,
margin of error, and sizing method.

Modes: --show | --defaults | --set key=value (repeatable) | --reset | --scope {global,project}
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import config_loader as cfg  # noqa: E402

NUMERIC_KEYS = {"default_confidence", "default_moe"}

QUESTIONS = [
    ("default_profile",
     "1. What market are you researching?",
     ["b2b-saas", "consumer", "enterprise", "marketplace", "hardware", "services"], str),
    ("default_confidence",
     "2. Default survey confidence level?",
     ["0.80", "0.85", "0.90", "0.95", "0.99"], float),
    ("default_moe",
     "3. Default survey margin of error (fraction, e.g. 0.05)?",
     None, float),
    ("sizing_method",
     "4. Default market-sizing method?",
     ["top-down", "bottoms-up", "both"], str),
]


def _print_questions() -> None:
    print(f"Onboarding questions — {cfg.SKILL}:\n")
    for _k, prompt, choices, _c in QUESTIONS:
        line = f"  {prompt}"
        if choices:
            line += f"   [{' / '.join(choices)}]"
        print(line)


def run_interactive(config: dict) -> dict:
    print(f"Onboarding — {cfg.SKILL}. Press Enter to keep the current/default value.\n")
    for key, prompt, choices, caster in QUESTIONS:
        suffix = f" [{'/'.join(choices)}]" if choices else ""
        cur = f" (current: {config.get(key)})" if config.get(key) is not None else ""
        raw = input(f"{prompt}{suffix}{cur}: ").strip()
        if not raw:
            continue
        try:
            config[key] = caster(raw)
        except ValueError:
            print(f"   ! invalid value for {key}, keeping current")
    return config


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=f"Onboarding for the {cfg.SKILL} skill.")
    p.add_argument("--show", action="store_true")
    p.add_argument("--defaults", action="store_true", help="write built-in defaults, no prompt")
    p.add_argument("--set", action="append", default=[], metavar="key=value")
    p.add_argument("--reset", action="store_true")
    p.add_argument("--scope", choices=["global", "project"], default="global")
    args = p.parse_args(argv)

    if args.show:
        _print_questions()
        print("\nCurrent effective config:")
        print(json.dumps(cfg.load_config(), indent=2, sort_keys=True))
        return 0

    if args.reset:
        path = cfg.project_config_path() if args.scope == "project" else cfg.GLOBAL_CONFIG_PATH
        if path.exists():
            path.unlink(); print(f"removed {path}")
        else:
            print(f"no config at {path}")
        return 0

    config = cfg.load_config()

    if args.set:
        for item in args.set:
            if "=" not in item:
                print(f"error: --set expects key=value, got '{item}'", file=sys.stderr)
                return 2
            k, v = item.split("=", 1)
            if k in NUMERIC_KEYS:
                try:
                    v = float(v)
                except ValueError:
                    pass
            config[k] = v
    elif not args.defaults:
        if sys.stdin.isatty():
            config = run_interactive(config)
        else:
            print("non-interactive shell: use --defaults or --set key=value. Showing questions:\n")
            _print_questions()
            return 0

    config["setup_completed_at"] = _dt.datetime.now(_dt.timezone.utc).isoformat()
    path = cfg.write_config(config, scope=args.scope)
    print(f"saved {cfg.SKILL} customization -> {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
