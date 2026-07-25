#!/usr/bin/env python3
"""onboard.py - First-run onboarding wizard for the markdown-html design-system.

Stdlib-only. Walks the user through 10 questions ONCE, validates the brand colors
against WCAG 2.2 AA, derives the 12 CSS custom properties, and writes the result
to a customization config that every markdown-html converter (md-document,
md-review, md-slides) reads via config_loader.py.

Modes:
  --show                   print the questions + current effective config
  --defaults               write the built-in defaults without prompting
  --set key=value ...      set specific answers non-interactively (repeatable)
  --reset                  delete the saved config at the chosen scope
  --scope {global,project} where to save (default: global = ~/.config/markdown-html)

With no flags and an interactive terminal, walks the questions one at a time.
Refuses to complete onboarding if:
  - default_output_dir is empty or unwritable (Q1 hard rule)
  - the chosen brand colors fail WCAG AA contrast for body text on bg

Pattern lifted from research-ops/skills/clinical-research/scripts/onboard.py
(QUESTIONS table, _apply, run_interactive, main shape) and adapted for the
design-system surface (color validation via brand_palette_validator, palette
derivation persisted into the config alongside the raw user inputs).
"""

from __future__ import annotations

import argparse
import datetime as _dt
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import brand_palette_validator as bpv  # noqa: E402
import config_loader as cfg  # noqa: E402

DESIGN_STYLES = ["editorial", "technical", "minimal", "playful"]
CODE_THEMES = ["light", "dark", "auto"]
TOC_BEHAVIORS = ["sticky-sidebar", "collapsible-top", "inline", "none"]
SAFE_FONTS = [
    "Inter", "Roboto", "Open Sans", "Lato", "Source Sans 3", "IBM Plex Sans",
    "Merriweather", "Source Serif 4", "Lora", "Playfair Display",
    "JetBrains Mono", "Fira Code",
]

# (key, prompt, choices_or_None, caster, hint)
QUESTIONS = [
    ("default_output_dir",
     "1. Where should generated HTML files go? (path; must be writable)",
     None, str, "e.g., ./markdown-html-out/ or ~/Documents/claude-html/"),
    ("brand.primary",
     "2. Brand primary color (HEX)?",
     None, str, "e.g., #0A1628 (dark navy) or #FF6B35 (orange)"),
    ("brand.accent",
     "3. Brand accent color (HEX, optional — leave blank to derive)?",
     None, str, "e.g., #00D4AA (teal) or leave blank for auto-derive"),
    ("typography.heading_font",
     "4. Heading Google Font?",
     SAFE_FONTS, str, "pick from the list or type your own"),
    ("typography.body_font",
     "5. Body Google Font?",
     SAFE_FONTS, str, "Inter/Roboto/Lato pair well as body fonts"),
    ("design_style",
     "6. Design style?",
     DESIGN_STYLES, str, "editorial = magazine-like; technical = docs-like; minimal = sparse; playful = product-marketing"),
    ("code_theme",
     "7. Syntax-highlighting theme?",
     CODE_THEMES, str, "auto = follows prefers-color-scheme"),
    ("toc.behavior",
     "8. Table-of-contents behavior?",
     TOC_BEHAVIORS, str, "sticky-sidebar = best for long docs; inline = best for slides"),
    ("company_name",
     "9. Company / project name (optional, shows in footer)?",
     None, str, "leave blank to omit"),
    ("logo_url",
     "10. Logo URL (optional; base64-embedded at render time)?",
     None, str, "leave blank to omit; URL or local path both work"),
]


def _apply(config: dict, key: str, value) -> None:
    """Apply a dotted key path into the nested config dict."""
    if "." in key:
        parts = key.split(".")
        d = config
        for part in parts[:-1]:
            d = d.setdefault(part, {})
        d[parts[-1]] = value
    else:
        config[key] = value


def _get(config: dict, key: str):
    if "." in key:
        parts = key.split(".")
        d = config
        for part in parts:
            if not isinstance(d, dict):
                return None
            d = d.get(part)
        return d
    return config.get(key)


def _derive_and_check_palette(config: dict) -> tuple[bool, str]:
    """Run brand_palette_validator on the current colors and store the derived palette.

    Returns (ok, message). If WCAG body-text contrast FAILs, ok=False.
    """
    primary = _get(config, "brand.primary") or bpv.rgb_to_hex((10, 22, 40))
    accent = _get(config, "brand.accent") or None
    bg = _get(config, "brand.bg") or None
    text = _get(config, "brand.text") or None
    result = bpv.validate(primary, accent, bg, text)
    config["derived_palette"] = result["derived_palette"]
    if result["verdict"] == "FAIL":
        msgs = [f for f in result["findings"] if f["level"] == "FAIL"]
        return False, "; ".join(m["message"] for m in msgs)
    if result["verdict"] == "WARN":
        msgs = [f for f in result["findings"] if f["level"] == "WARN"]
        return True, "warnings: " + "; ".join(m["message"] for m in msgs)
    return True, "WCAG AA contrast met"


def _writable(path_str: str) -> bool:
    if not path_str or not path_str.strip():
        return False
    p = Path(path_str).expanduser()
    parent = p.parent if p.suffix else p
    # If neither the path nor its parent exists, walk up until we find one
    while not parent.exists():
        if parent.parent == parent:
            return False
        parent = parent.parent
    return os.access(parent, os.W_OK)


def _print_questions() -> None:
    print(f"Onboarding questions — markdown-html/{cfg.SKILL}:\n")
    for key, prompt, choices, _c, hint in QUESTIONS:
        line = f"  {prompt}"
        if choices:
            line += f"\n     choices: {', '.join(choices[:6])}{'...' if len(choices) > 6 else ''}"
        if hint:
            line += f"\n     hint: {hint}"
        print(line)
        print()


def run_interactive(config: dict) -> dict:
    print(f"Onboarding — markdown-html/{cfg.SKILL}. Press Enter to keep the current/default.\n")
    for key, prompt, choices, caster, hint in QUESTIONS:
        current = _get(config, key)
        suffix = ""
        if choices:
            suffix = f" [{ '/'.join(choices[:4]) }{'...' if len(choices) > 4 else ''}]"
        cur = f" (current: {current})" if current not in (None, "") else ""
        if hint:
            print(f"   hint: {hint}")
        raw = input(f"{prompt}{suffix}{cur}: ").strip()
        if not raw:
            continue
        try:
            _apply(config, key, caster(raw))
        except ValueError:
            print(f"   ! invalid value for {key}, keeping current")
        print()
    return config


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Onboarding for the markdown-html design-system skill."
    )
    p.add_argument("--show", action="store_true", help="print questions + effective config")
    p.add_argument("--defaults", action="store_true", help="write built-in defaults, no prompt")
    p.add_argument("--set", action="append", default=[], metavar="key=value",
                   help="set an answer non-interactively (repeatable; supports dotted keys like brand.primary=#FF6B35)")
    p.add_argument("--reset", action="store_true", help="delete saved config at the scope")
    p.add_argument("--scope", choices=["global", "project"], default="global")
    args = p.parse_args(argv)

    if args.show:
        _print_questions()
        print("Current effective config:")
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
            # numeric keys
            if k == "typography.scale_ratio":
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

    # Hard rule 1: refuse if default_output_dir is empty or unwritable
    out_dir = config.get("default_output_dir") or ""
    if not _writable(out_dir):
        print(
            f"refusing to save: default_output_dir '{out_dir}' is empty or its parent "
            f"is not writable. Pick a path you control (e.g., ./markdown-html-out/ or "
            f"~/Documents/claude-html/) and re-run.",
            file=sys.stderr,
        )
        return 3

    # Hard rule 2: refuse if WCAG AA body-text contrast fails on the chosen colors
    ok, msg = _derive_and_check_palette(config)
    if not ok:
        print(
            f"refusing to save: WCAG AA contrast failed for the chosen colors — {msg}. "
            f"Pick a darker primary (or a lighter text), or leave brand.bg/brand.text "
            f"blank to let the validator derive a passing pair.",
            file=sys.stderr,
        )
        return 4
    if msg.startswith("warnings:"):
        print(f"note: {msg} — proceeding (warnings, not failures).")

    config["setup_completed_at"] = _dt.datetime.now(_dt.timezone.utc).isoformat()
    path = cfg.write_config(config, scope=args.scope)
    print(f"saved markdown-html/{cfg.SKILL} customization -> {path}")
    print(f"derived 12-token palette stored under derived_palette in the same file.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
