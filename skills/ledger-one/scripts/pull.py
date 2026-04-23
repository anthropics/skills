#!/usr/bin/env python3
"""Fetch, categorize, and persist recent transactions from SimpleFIN."""
import argparse
import logging
import os
import sys
from pathlib import Path

import psycopg
from anthropic import Anthropic
from dotenv import load_dotenv

from ledger_one.pull import run_pull


def main():
    load_dotenv()
    parser = argparse.ArgumentParser()
    parser.add_argument("--days", type=int, default=7)
    parser.add_argument("--categories", type=Path, default=Path("config/categories.yaml"))
    parser.add_argument("--dry-run", action="store_true",
                        help="Fetch and categorize but do not write to the database.")
    args = parser.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(name)s: %(message)s")

    access_url = _require("SIMPLEFIN_ACCESS_URL")
    db_url = _require("DATABASE_URL")
    _require("ANTHROPIC_API_KEY")
    model = os.environ.get("LEDGER_CATEGORIZATION_MODEL", "claude-haiku-4-5-20251001")

    if not args.categories.exists():
        print(f"Missing {args.categories}. Copy config/categories.yaml.example.", file=sys.stderr)
        sys.exit(1)

    client = Anthropic(max_retries=5)
    with psycopg.connect(db_url, autocommit=True) as conn:
        stats = run_pull(
            db=conn, access_url=access_url, days=args.days,
            categories_file=args.categories,
            anthropic_client=client, model=model,
            dry_run=args.dry_run,
        )
    # Never log or print access_url, anywhere.
    print("Pull complete:", stats)
    if stats["errors"]:
        print("SimpleFIN reported errors:", stats["errors"])
    if stats["stale_accounts"]:
        print(
            f"Stale balance_date on accounts: {stats['stale_accounts']}. "
            "SimpleFIN likely serving cached data — check the Bridge UI.",
            file=sys.stderr,
        )
        return 1
    return 0


def _require(name: str) -> str:
    val = os.environ.get(name)
    if not val:
        print(f"Missing env var: {name}", file=sys.stderr)
        sys.exit(1)
    return val


if __name__ == "__main__":
    sys.exit(main())
