#!/usr/bin/env python3
"""Warn when shared/prisma_trAIce_protocol.md is older than 180 days.

Non-blocking: exit 0 even on stale, but print warning to stderr.
Exit 1 only on parse error (missing or malformed snapshot_date).

Usage:
  python scripts/check_prisma_trAIce_freshness.py [path]

Default path: shared/prisma_trAIce_protocol.md (relative to repo root).
"""
from __future__ import annotations

import argparse
import sys
from datetime import date, datetime
from pathlib import Path

import yaml

DEFAULT_PATH = Path(__file__).resolve().parent.parent / "shared" / "prisma_trAIce_protocol.md"
STALE_THRESHOLD_DAYS = 180


def extract_frontmatter(text: str) -> dict:
    """Extract YAML frontmatter between opening and closing '---' fences."""
    if not text.startswith("---"):
        raise ValueError("No opening '---' fence")
    lines = text.splitlines()
    end_idx = None
    for i in range(1, len(lines)):
        if lines[i].strip() == "---":
            end_idx = i
            break
    if end_idx is None:
        raise ValueError("No closing '---' fence")
    fm_text = "\n".join(lines[1:end_idx])
    data = yaml.safe_load(fm_text)
    if not isinstance(data, dict):
        raise ValueError("Frontmatter is not a mapping")
    return data


def parse_snapshot_date(fm: dict) -> date:
    raw = fm.get("snapshot_date")
    if not raw:
        raise ValueError("snapshot_date missing")
    if isinstance(raw, date):
        return raw
    try:
        return datetime.strptime(str(raw), "%Y-%m-%d").date()
    except ValueError as exc:
        raise ValueError(f"snapshot_date malformed: {raw}") from exc


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, nargs="?", default=DEFAULT_PATH)
    args = parser.parse_args()

    try:
        text = args.path.read_text(encoding="utf-8")
        fm = extract_frontmatter(text)
        snapshot = parse_snapshot_date(fm)
    except (FileNotFoundError, ValueError, yaml.YAMLError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    age_days = (date.today() - snapshot).days
    if age_days > STALE_THRESHOLD_DAYS:
        print(
            f"WARNING: prisma_trAIce_protocol.md snapshot is {age_days} days old "
            f"(threshold {STALE_THRESHOLD_DAYS}). Upstream may have updated — "
            f"please review {fm.get('upstream_source', 'https://github.com/cqh4046/PRISMA-trAIce')} "
            f"and re-sync if needed. (STALE status surfaced; non-blocking.)",
            file=sys.stderr,
        )
    else:
        print(f"OK: snapshot is {age_days} days old (current)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
