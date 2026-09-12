#!/usr/bin/env python3
"""Move OUTBOX files older than 24 hours into OUTBOX_archive.

Run from repo root:
  python scripts/archive_outbox.py
"""
from __future__ import annotations

import shutil
from datetime import datetime, timedelta
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUTBOX = ROOT / "OUTBOX"
ARCHIVE = ROOT / "OUTBOX_archive"
AGE = timedelta(hours=24)


def main():
    now = datetime.now()
    ARCHIVE.mkdir(exist_ok=True)
    if not OUTBOX.exists():
        return
    for path in OUTBOX.iterdir():
        if path.is_file():
            mtime = datetime.fromtimestamp(path.stat().st_mtime)
            if now - mtime >= AGE:
                dest = ARCHIVE / path.name
                shutil.move(str(path), dest)
                print(f"Archived {path.name}")


if __name__ == "__main__":
    main()
