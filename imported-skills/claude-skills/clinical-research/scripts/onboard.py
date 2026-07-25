#!/usr/bin/env python3
"""onboard.py - Onboarding questionnaire for the clinical-research skill.

Stdlib-only. Asks the user a short set of questions BEFORE they start designing a
study, then writes their answers to a customization config (read by every tool in
this skill via config_loader.py). Customization is the point: the answers become the
defaults for profile, alpha/power/dropout, and the named owners printed on outputs.

Modes:
  --show               print the questions + the current effective config, then exit
  --defaults           write the built-in defaults without prompting (non-interactive)
  --set key=value ...  set specific answers non-interactively (repeatable)
  --reset              delete the saved config at the chosen scope
  --scope {global,project}  where to save (default: global = ~/.config/research-ops)

With no flags and an interactive terminal, it walks the questions one at a time.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import config_loader as cfg  # noqa: E402

# (key, prompt, choices_or_None, caster, default_key_in_DEFAULTS)
QUESTIONS = [
    ("default_profile",
     "1. What development area are you working in?",
     ["drug", "device", "biologic", "diagnostic", "digital-therapeutic"], str, "default_profile"),
    ("default_alpha",
     "2. Default two-sided significance level (alpha)?",
     ["0.10", "0.05", "0.025", "0.01"], float, "default_alpha"),
    ("default_power",
     "3. Default target power (1 - beta)?",
     ["0.80", "0.85", "0.90", "0.95"], float, "default_power"),
    ("default_dropout",
     "4. Default anticipated dropout fraction (for sample-size inflation)?",
     None, float, "default_dropout"),
    ("owner.biostatistician",
     "5. Named biostatistician who signs the sample-size justification?",
     None, str, None),
    ("owner.medical_monitor",
     "6. Named medical monitor for the study?",
     None, str, None),
    ("owner.regulatory_owner",
     "7. Named regulatory owner who signs the gate decision?",
     None, str, None),
]


def _apply(config: dict, key: str, value) -> None:
    if key.startswith("owner."):
        config.setdefault("owners", {})[key.split(".", 1)[1]] = value
    else:
        config[key] = value


def _print_questions() -> None:
    print(f"Onboarding questions — {cfg.SKILL}:\n")
    for _, prompt, choices, _c, _d in QUESTIONS:
        line = f"  {prompt}"
        if choices:
            line += f"   [{ ' / '.join(choices) }]"
        print(line)


def run_interactive(config: dict) -> dict:
    print(f"Onboarding — {cfg.SKILL}. Press Enter to keep the current/default value.\n")
    for key, prompt, choices, caster, dkey in QUESTIONS:
        current = config.get("owners", {}).get(key.split(".", 1)[1]) if key.startswith("owner.") \
            else config.get(key)
        suffix = f" [{ '/'.join(choices) }]" if choices else ""
        cur = f" (current: {current})" if current is not None else ""
        raw = input(f"{prompt}{suffix}{cur}: ").strip()
        if not raw:
            continue
        try:
            _apply(config, key, caster(raw))
        except ValueError:
            print(f"   ! invalid value for {key}, keeping current")
    return config


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=f"Onboarding for the {cfg.SKILL} skill.")
    p.add_argument("--show", action="store_true", help="print questions + effective config")
    p.add_argument("--defaults", action="store_true", help="write built-in defaults, no prompt")
    p.add_argument("--set", action="append", default=[], metavar="key=value",
                   help="set an answer non-interactively (repeatable)")
    p.add_argument("--reset", action="store_true", help="delete saved config at the scope")
    p.add_argument("--scope", choices=["global", "project"], default="global")
    args = p.parse_args(argv)

    if args.show:
        _print_questions()
        print("\nCurrent effective config:")
        import json
        print(json.dumps(cfg.load_config(), indent=2, sort_keys=True))
        return 0

    if args.reset:
        path = cfg.project_config_path() if args.scope == "project" else cfg.GLOBAL_CONFIG_PATH
        if path.exists():
            path.unlink()
            print(f"removed {path}")
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
            # best-effort type coercion for known numeric keys
            if k in ("default_alpha", "default_power", "default_dropout"):
                try:
                    v = float(v)
                except ValueError:
                    pass
            _apply(config, k, v)
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
