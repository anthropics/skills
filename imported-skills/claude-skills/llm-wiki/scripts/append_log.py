#!/usr/bin/env python3
"""
append_log.py — Append a standardized entry to wiki/log.md.

The log is append-only and uses a consistent header so unix tools can parse it:
    ## [YYYY-MM-DD] <op> | <title>

A useful tip: if each entry starts with a consistent prefix, the log becomes
parseable with simple unix tools — `grep "^## \\[" log.md | tail -5` gives you
the last 5 entries.

Usage:
    python append_log.py --vault ~/vaults/research --op ingest --title "Anthropic Monosemanticity"
    python append_log.py --vault . --op query --title "interpretability vs mechinterp" --detail "3 pages touched"
    python append_log.py --vault . --op lint --title "weekly health check" --detail "2 contradictions" --json

Valid ops:
    ingest   — a source was read and integrated into the wiki
    query    — a question was answered (filed back as a page)
    lint     — a health-check pass ran
    create   — a new page was created outside of an ingest
    update   — an existing page was updated outside of an ingest
    delete   — a page was removed
    note     — freeform note (contradictions flagged, thesis revisions, etc.)

Exit codes:
    0   success
    1   invalid vault / missing log.md / invalid op / write failure
"""
from __future__ import annotations
import argparse
import datetime as dt
import json
import sys
from pathlib import Path

VALID_OPS = {"ingest", "query", "lint", "create", "update", "delete", "note"}


def _error(message, as_json=False):
    """Print an error and exit with code 1. Respects --json mode."""
    if as_json:
        print(json.dumps({"status": "error", "message": message}))
    else:
        print(f"[error] {message}", file=sys.stderr)
    sys.exit(1)


def validate_vault(vault):
    """Return the log.md path or raise if vault is invalid."""
    if not vault.exists():
        raise FileNotFoundError(f"vault does not exist: {vault}")
    log_path = vault / "wiki" / "log.md"
    if not log_path.exists():
        raise FileNotFoundError(f"{log_path} does not exist — is this a vault?")
    return log_path


def format_entry(op, title, detail):
    """Build the standardized log entry string."""
    today = dt.date.today().isoformat()
    header = f"## [{today}] {op} | {title}"
    body = f"\n{detail}\n" if detail else "\n"
    return today, header, f"\n{header}\n{body}"


def append_log(vault, op, title, detail, as_json=False):
    """Append a standardized entry to wiki/log.md inside the vault."""
    if op not in VALID_OPS:
        _error(f"unknown op '{op}'. Valid: {sorted(VALID_OPS)}", as_json)

    try:
        log_path = validate_vault(vault)
    except FileNotFoundError as e:
        _error(str(e), as_json)

    today, header, entry_text = format_entry(op, title, detail)

    try:
        with log_path.open("a", encoding="utf-8") as f:
            f.write(entry_text)
    except OSError as e:
        _error(f"failed to write {log_path}: {e}", as_json)

    result = {
        "status": "ok",
        "log_path": str(log_path),
        "date": today,
        "op": op,
        "title": title,
        "header": header,
        "detail": detail,
    }

    if as_json:
        print(json.dumps(result, indent=2))
    else:
        print(f"[ok] appended to {log_path}")
        print(f"     {header}")
        if detail:
            print(f"     detail: {detail}")

    return result


def main():
    p = argparse.ArgumentParser(
        description="Append a standardized entry to wiki/log.md",
        epilog="Format: ## [YYYY-MM-DD] <op> | <title>",
    )
    p.add_argument("--vault", required=True, help="Vault root directory")
    p.add_argument(
        "--op",
        required=True,
        choices=sorted(VALID_OPS),
        help="Operation type (ingest, query, lint, create, update, delete, note)",
    )
    p.add_argument("--title", required=True, help="Short title for the entry")
    p.add_argument("--detail", default=None, help="Optional detail text")
    p.add_argument(
        "--json", action="store_true", help="Emit result as JSON instead of human-readable"
    )
    args = p.parse_args()
    append_log(
        Path(args.vault).expanduser().resolve(),
        args.op,
        args.title,
        args.detail,
        as_json=args.json,
    )


if __name__ == "__main__":
    main()
