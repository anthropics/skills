#!/usr/bin/env python3
"""First-run setup for the handoff skill.

Walks the user through 5 core questions (and 2 optional) to write a config
that the rest of the skill reads. Idempotent: re-running with --reconfigure
pre-fills with current values.

No defaults are pre-selected for Q1 (save location) — the user makes an
explicit choice on first run.

Stdlib-only.
"""


import argparse
import datetime as dt
import json
import os
import sys
from pathlib import Path
from typing import Any

# Import sibling helper without polluting sys.path long-term.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import config_loader  # noqa: E402

SAVE_LOCATION_OPTIONS = [
    ("temp", "OS temp dir (mktemp -t handoff-XXXXXX.md) — ephemeral"),
    ("home_visible", "Home folder ~/handoffs/"),
    ("home_hidden", "Hidden home folder ~/.handoff/"),
    ("project", "Per-project .handoff/ (auto-gitignored)"),
    ("custom", "Custom path"),
]

RETENTION_OPTIONS = [
    (7, "7 days (recommended for temp dir)"),
    (30, "30 days"),
    (0, "Forever (never delete)"),
    (-1, "Manual (never touch existing files)"),
]

REDACTION_OPTIONS = [
    ("strict", "Strict — block save until findings are resolved"),
    ("warn", "Warn — flag findings inline, save anyway"),
    ("off", "Off — skip the linter (not recommended)"),
]

GIT_CONTEXT_OPTIONS = [
    (True, "Yes — auto-include branch, last commit, dirty-file count"),
    (False, "No — pure prose handoff"),
]

SCOPE_OPTIONS = [
    ("all", "All repo skills (recommended)"),
    ("current_domain", "Current domain only"),
    ("off", "Off — no recommendations"),
]

FILENAME_OPTIONS = [
    ("date_slug", "YYYY-MM-DD-slug.md (sorts chronologically)"),
    ("timestamp", "handoff-YYYYMMDD-HHMMSS.md"),
    ("mktemp", "handoff-XXXXXX.md (mktemp-style random)"),
]


def _prompt_choice(question: str, options: list[tuple[Any, str]], current: Any = None) -> Any:
    print()
    print(question)
    for i, (value, label) in enumerate(options, start=1):
        marker = " (current)" if current is not None and value == current else ""
        print(f"  {i}. {label}{marker}")
    while True:
        prompt = "Enter number"
        if current is not None:
            prompt += " (press Enter to keep current)"
        prompt += ": "
        try:
            raw = input(prompt).strip()
        except EOFError:
            print("\nAborted.", file=sys.stderr)
            sys.exit(2)
        except KeyboardInterrupt:
            print("\nAborted.", file=sys.stderr)
            sys.exit(2)
        if raw == "" and current is not None:
            return current
        if raw.isdigit():
            idx = int(raw)
            if 1 <= idx <= len(options):
                return options[idx - 1][0]
        print(f"  Please enter a number between 1 and {len(options)}.")


def _prompt_text(question: str, current: str | None = None, allow_empty: bool = False) -> str:
    while True:
        suffix = f" [{current}]" if current else ""
        try:
            raw = input(f"{question}{suffix}: ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nAborted.", file=sys.stderr)
            sys.exit(2)
        if raw == "" and current is not None:
            return current
        if raw == "" and allow_empty:
            return ""
        if raw:
            return raw
        print("  Please enter a value.")


def _resolve_custom_path(raw: str) -> Path:
    path = Path(raw).expanduser().resolve()
    return path


def _validate_writable_dir(path: Path) -> bool:
    try:
        path.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        print(f"  Cannot create {path}: {exc}", file=sys.stderr)
        return False
    if not os.access(path, os.W_OK):
        print(f"  Path {path} is not writable.", file=sys.stderr)
        return False
    return True


def _maybe_append_gitignore(project_root: Path) -> None:
    gitignore = project_root / ".gitignore"
    line = ".handoff/"
    try:
        existing = gitignore.read_text(encoding="utf-8") if gitignore.exists() else ""
    except OSError:
        existing = ""
    if line in existing.splitlines():
        return
    try:
        answer = input(f"  Append '{line}' to {gitignore}? (Y/n): ").strip().lower()
    except (EOFError, KeyboardInterrupt):
        return
    if answer in ("", "y", "yes"):
        try:
            with gitignore.open("a", encoding="utf-8") as f:
                if existing and not existing.endswith("\n"):
                    f.write("\n")
                f.write(f"{line}\n")
            print(f"  Added '{line}' to {gitignore}.")
        except OSError as exc:
            print(f"  Could not write {gitignore}: {exc}", file=sys.stderr)


def run_setup(scope: str = "global", reconfigure: bool = False) -> int:
    print("=" * 60)
    print("Handoff skill — first-run setup")
    print("=" * 60)
    print()
    print("This walks you through 5 questions (~30 seconds). You can")
    print("rerun at any time with: /cs:handoff-setup")
    print()

    current = config_loader.load_config() if reconfigure else dict(config_loader.DEFAULTS)

    # Q1 — save location (no pre-selected default)
    save_mode = _prompt_choice(
        "Q1. Where should handoff documents be saved?",
        SAVE_LOCATION_OPTIONS,
        current=current.get("save_location", {}).get("mode") if reconfigure else None,
    )
    save_path: str | None = None
    if save_mode == "custom":
        while True:
            raw = _prompt_text(
                "  Enter custom path",
                current=current.get("save_location", {}).get("path") if reconfigure else None,
            )
            resolved = _resolve_custom_path(raw)
            if _validate_writable_dir(resolved):
                save_path = str(resolved)
                break
    elif save_mode == "project":
        save_path = str((Path.cwd() / ".handoff").resolve())
        if _validate_writable_dir(Path(save_path)):
            _maybe_append_gitignore(Path.cwd())
    elif save_mode == "home_visible":
        save_path = str((Path.home() / "handoffs").resolve())
        _validate_writable_dir(Path(save_path))
    elif save_mode == "home_hidden":
        save_path = str((Path.home() / ".handoff").resolve())
        _validate_writable_dir(Path(save_path))

    # Q2 — retention
    retention_days = _prompt_choice(
        "Q2. How long should old handoff files stick around?",
        RETENTION_OPTIONS,
        current=current.get("retention_days") if reconfigure else None,
    )

    # Q3 — redaction strictness
    redaction = _prompt_choice(
        "Q3. If the redaction linter finds secrets, what should happen?",
        REDACTION_OPTIONS,
        current=current.get("redaction") if reconfigure else None,
    )

    # Q4 — git context
    include_git = _prompt_choice(
        "Q4. Auto-include branch + last commit + dirty-file count?",
        GIT_CONTEXT_OPTIONS,
        current=current.get("include_git_context") if reconfigure else None,
    )

    # Q5 — recommender scope
    rec_scope = _prompt_choice(
        "Q5. Which skills should the recommender scan?",
        SCOPE_OPTIONS,
        current=current.get("skill_recommendation_scope") if reconfigure else None,
    )

    # Q6 — filename style (only if not temp)
    if save_mode == "temp":
        filename_style = "mktemp"
    else:
        filename_style = _prompt_choice(
            "Q6. Filename style for saved handoffs?",
            FILENAME_OPTIONS,
            current=current.get("filename_style") if reconfigure else None,
        )

    config = {
        "version": 1,
        "save_location": {"mode": save_mode, "path": save_path},
        "retention_days": retention_days,
        "redaction": redaction,
        "include_git_context": include_git,
        "skill_recommendation_scope": rec_scope,
        "filename_style": filename_style,
        "setup_completed_at": dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z",
    }

    if scope == "project":
        path = config_loader.write_project_config(config)
    else:
        path = config_loader.write_global_config(config)

    print()
    print("=" * 60)
    print(f"Config saved to {path}")
    print("Rerun with: /cs:handoff-setup")
    print("=" * 60)
    return 0


def decline_setup() -> int:
    config_loader.mark_setup_declined()
    print(
        "Setup skipped. Using defaults (OS temp dir, 7-day retention, strict redaction).\n"
        "Rerun at any time with: /cs:handoff-setup"
    )
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="First-run setup for the handoff skill.",
        epilog="Prompt-once-then-default model. Q1 has no pre-selected option.",
    )
    parser.add_argument(
        "--reconfigure",
        action="store_true",
        help="Walk questions again with current values pre-filled.",
    )
    parser.add_argument(
        "--project",
        action="store_true",
        help="Write a project-local override at .handoff/config.json instead of the global config.",
    )
    parser.add_argument(
        "--decline",
        action="store_true",
        help="Mark setup as declined; use built-in defaults and never prompt again.",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Print a sample config and exit (no prompts).",
    )
    args = parser.parse_args(argv)

    if args.sample:
        print(json.dumps(config_loader.DEFAULTS, indent=2, sort_keys=True))
        return 0

    if args.decline:
        return decline_setup()

    scope = "project" if args.project else "global"
    return run_setup(scope=scope, reconfigure=args.reconfigure)


if __name__ == "__main__":
    sys.exit(main())
