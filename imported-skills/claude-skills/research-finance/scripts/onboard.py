#!/usr/bin/env python3
"""onboard.py - Onboarding questionnaire for the research-finance skill.

Stdlib-only. Asks the user a short set of questions BEFORE they build an R&D program
budget, then writes the answers to a customization config read by every tool in this
skill via config_loader.py. The answers become defaults for profile, F&A rate, runway
threshold, accounting standard, and the named finance owner printed on routing outputs.

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

NUMERIC_KEYS = {"default_fa_rate", "runway_threshold_months"}

QUESTIONS = [
    ("default_profile",
     "1. What R&D area is this program?",
     ["pharma-rd", "biotech", "medtech", "deep-tech", "software-rd", "university-lab"], str),
    ("default_fa_rate",
     "2. F&A / indirect rate as a fraction (e.g. 0.55), or blank to use the profile default?",
     None, float),
    ("runway_threshold_months",
     "3. Runway alert threshold in months (warn below this)?",
     None, float),
    ("accounting_standard",
     "4. Which accounting standard governs capitalize-vs-expense?",
     ["ifrs", "usgaap"], str),
    ("finance_owner",
     "5. Named finance/controller owner who signs accounting treatment?",
     None, str),
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
