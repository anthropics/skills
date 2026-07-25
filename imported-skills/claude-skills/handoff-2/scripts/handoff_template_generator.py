#!/usr/bin/env python3
"""Handoff template generator.

Creates a 5-section scaffold at the configured save location. The agent
fills in the bodies. Prints the resulting path to stdout.

Stdlib-only.
"""


import argparse
import datetime as dt
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import config_loader  # noqa: E402


def _slugify(text: str, max_len: int = 40) -> str:
    text = re.sub(r"[^A-Za-z0-9]+", "-", text).strip("-").lower()
    if not text:
        text = "handoff"
    return text[:max_len].rstrip("-")


def _git_context(cwd: Path) -> str | None:
    def _run(cmd: list[str]) -> str | None:
        try:
            result = subprocess.run(
                cmd,
                cwd=str(cwd),
                check=False,
                capture_output=True,
                text=True,
                timeout=5,
            )
        except (OSError, subprocess.SubprocessError):
            return None
        if result.returncode != 0:
            return None
        return result.stdout.strip()

    if _run(["git", "rev-parse", "--is-inside-work-tree"]) != "true":
        return None
    branch = _run(["git", "branch", "--show-current"]) or "(detached)"
    last_commit = _run(["git", "log", "-1", "--oneline"]) or "(no commits)"
    status = _run(["git", "status", "--porcelain"]) or ""
    dirty_count = sum(1 for line in status.splitlines() if line.strip())
    lines = [
        "_Git context (auto-included from config)._",
        "",
        f"- Branch: `{branch}`",
        f"- Last commit: `{last_commit}`",
        f"- Dirty files: {dirty_count}",
    ]
    return "\n".join(lines)


HANDOFF_FILENAME_TOKENS = ("handoff-", "handoff_", "handoff.md")


def _save_dirs(config: dict) -> list[Path]:
    """Directories where existing handoffs might live, in lookup order."""
    save = config.get("save_location", {})
    mode = save.get("mode", "temp")
    raw_path = save.get("path")
    dirs: list[Path] = []
    if mode == "temp":
        dirs.append(Path(tempfile.gettempdir()))
    elif raw_path:
        dirs.append(Path(raw_path))
    proj = Path.cwd() / ".handoff"
    if proj.exists() and proj not in dirs:
        dirs.append(proj)
    return [d for d in dirs if d.exists()]


def _find_latest_handoff(config: dict) -> Path | None:
    latest: tuple[float, Path] | None = None
    for d in _save_dirs(config):
        try:
            for entry in d.iterdir():
                if not entry.is_file() or not entry.name.lower().endswith(".md"):
                    continue
                name = entry.name.lower()
                if not any(t in name for t in HANDOFF_FILENAME_TOKENS):
                    continue
                try:
                    mtime = entry.stat().st_mtime
                except OSError:
                    continue
                if latest is None or mtime > latest[0]:
                    latest = (mtime, entry)
        except OSError:
            continue
    return latest[1] if latest else None


def _resolve_save_path(config: dict, goal: str, now: dt.datetime) -> Path:
    save = config.get("save_location", {})
    mode = save.get("mode", "temp")
    raw_path = save.get("path")
    filename_style = config.get("filename_style", "mktemp")
    slug = _slugify(goal)
    if mode == "temp" or filename_style == "mktemp":
        fd, name = tempfile.mkstemp(prefix="handoff-", suffix=".md")
        os.close(fd)
        return Path(name)
    if filename_style == "date_slug":
        filename = f"{now.strftime('%Y-%m-%d')}-{slug}.md"
    elif filename_style == "timestamp":
        filename = f"handoff-{now.strftime('%Y%m%d-%H%M%S')}.md"
    else:
        filename = f"handoff-{now.strftime('%Y%m%d-%H%M%S')}.md"

    if mode == "project":
        base = Path(raw_path) if raw_path else (Path.cwd() / ".handoff")
    elif mode == "home_visible":
        base = Path(raw_path) if raw_path else (Path.home() / "handoffs")
    elif mode == "home_hidden":
        base = Path(raw_path) if raw_path else (Path.home() / ".handoff")
    elif mode == "custom":
        if not raw_path:
            raise SystemExit("Custom save mode requires save_location.path in config.")
        base = Path(raw_path)
    else:
        base = Path(tempfile.gettempdir())
    base.mkdir(parents=True, exist_ok=True)
    return base / filename


def _scaffold(goal: str, git_block: str | None, now: dt.datetime) -> str:
    iso = now.replace(microsecond=0).isoformat() + "Z"
    git_section = git_block if git_block else "_<!-- git context disabled or not in a repo -->_"
    return f"""---
generated_at: {iso}
goal: "{goal}"
---

# Handoff — {now.strftime('%Y-%m-%d')}

> A fresh agent reads this to continue the work.
> Do not duplicate artifacts (PRDs, plans, ADRs, commits, diffs).
> Reference them by path or URL.

## Goal of next session

{goal or "_<!-- one sentence: what the next session must accomplish -->_"}

## State of play

{git_section}

_<!-- What's done, what's in flight, what's blocked. Reference artifacts; do not paste them. -->_

- Done: _<!-- ... -->_
- In flight: _<!-- ... -->_
- Blocked: _<!-- ... -->_

## Open decisions

_<!-- What must the next agent decide before continuing? -->_

- _<!-- decision 1, with options and any tradeoffs already considered -->_

## Skills to use

_<!-- 3-5 skills max. One-line why per skill. -->_

- _<!-- skill name — why this session needs it -->_

## Artifacts

_<!-- Paths and URLs only. No duplicated content. -->_

- _<!-- e.g. PR: https://github.com/org/repo/pull/123 -->_
- _<!-- e.g. PRD: documentation/implementation/foo.md -->_

---

_Inspired by Matt Pocock's handoff (MIT). See README for full credit._
"""


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Generate a handoff scaffold.")
    parser.add_argument("--goal", default="", help="Goal of the next session (from user argument).")
    parser.add_argument(
        "--print-path-only",
        action="store_true",
        help="Print only the generated path. Default prints path + brief summary.",
    )
    parser.add_argument(
        "--sample",
        action="store_true",
        help="Render the scaffold to stdout instead of writing a file.",
    )
    parser.add_argument(
        "--no-git",
        action="store_true",
        help="Skip git context even if enabled in config.",
    )
    parser.add_argument(
        "--refresh",
        action="store_true",
        help="Reuse the most recent handoff in the configured location instead of creating a new file. The agent edits it in place.",
    )
    args = parser.parse_args(argv)

    config = config_loader.load_config()
    now = dt.datetime.utcnow()
    goal = args.goal.strip()

    if args.refresh and not args.sample:
        existing = _find_latest_handoff(config)
        if existing is not None:
            if args.print_path_only:
                print(str(existing))
            else:
                print(f"Refresh: reusing existing handoff at {existing}")
                print("Edit the file in place to reflect the current state.")
            return 0
        # Fall through to creating a new one — refresh becomes create-if-missing.

    git_block: str | None = None
    if not args.no_git and config.get("include_git_context", True):
        git_block = _git_context(Path.cwd())

    content = _scaffold(goal=goal, git_block=git_block, now=now)

    if args.sample:
        sys.stdout.write(content)
        return 0

    save_path = _resolve_save_path(config, goal=goal, now=now)
    try:
        save_path.write_text(content, encoding="utf-8")
    except OSError as exc:
        print(f"Failed to write {save_path}: {exc}", file=sys.stderr)
        return 2

    if args.print_path_only:
        print(str(save_path))
    else:
        print(f"Scaffold written: {save_path}")
        print("Fill in the five sections, then run the redaction linter.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
