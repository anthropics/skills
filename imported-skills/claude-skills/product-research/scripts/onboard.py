#!/usr/bin/env python3
"""onboard.py - Onboarding questionnaire for the product-research skill.

Stdlib-only. Asks the user a short set of questions BEFORE they plan a study, then
writes the answers to a customization config read by every tool in this skill via
config_loader.py. The answers become defaults for profile, the insight source-threshold,
the default saturation method, and the high-stakes flag.

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

INT_KEYS = {"insight_min_sources"}
BOOL_KEYS = {"stakes_high"}

QUESTIONS = [
    ("default_profile",
     "1. What kind of product is this?",
     ["b2b-saas", "consumer-app", "enterprise", "marketplace", "hardware", "platform"], str),
    ("insight_min_sources",
     "2. How many independent participants must support a finding before it counts as an insight (not an anecdote)?",
     None, int),
    ("default_method",
     "3. Default sample-saturation method?",
     ["usability", "thematic", "evaluative-coverage"], str),
    ("stakes_high",
     "4. Is this high-stakes / high-heterogeneity research (raise sample sizes)?",
     ["true", "false"], str),
]


def _coerce(key: str, value: str):
    if key in INT_KEYS:
        return int(value)
    if key in BOOL_KEYS:
        return str(value).strip().lower() in ("true", "yes", "y", "1")
    return value


def _print_questions() -> None:
    print(f"Onboarding questions — {cfg.SKILL}:\n")
    for _k, prompt, choices, _c in QUESTIONS:
        line = f"  {prompt}"
        if choices:
            line += f"   [{' / '.join(choices)}]"
        print(line)


def run_interactive(config: dict) -> dict:
    print(f"Onboarding — {cfg.SKILL}. Press Enter to keep the current/default value.\n")
    for key, prompt, choices, _caster in QUESTIONS:
        suffix = f" [{'/'.join(choices)}]" if choices else ""
        cur = f" (current: {config.get(key)})" if config.get(key) is not None else ""
        raw = input(f"{prompt}{suffix}{cur}: ").strip()
        if not raw:
            continue
        try:
            config[key] = _coerce(key, raw)
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
            try:
                config[k] = _coerce(k, v)
            except ValueError:
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
