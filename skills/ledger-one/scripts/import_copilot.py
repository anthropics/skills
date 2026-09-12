#!/usr/bin/env python3
"""Bootstrap merchant_categories and import historical transactions from a Copilot CSV."""
import argparse
import os
import sys
from datetime import date
from pathlib import Path
import psycopg
from dotenv import load_dotenv
from ledger_one.import_copilot import import_csv


def main():
    load_dotenv()
    parser = argparse.ArgumentParser()
    parser.add_argument("csv", type=Path)
    parser.add_argument("--account-id", required=True,
                        help="The SimpleFIN account ID to attribute these historical rows to.")
    parser.add_argument(
        "--before", required=True, type=date.fromisoformat,
        help="YYYY-MM-DD cutoff. Transactions on or after this date are ignored. "
             "Set this to the first day ledger-one (SimpleFIN) will handle forward "
             "so the two data sources don't overlap."
    )
    args = parser.parse_args()

    with psycopg.connect(os.environ["DATABASE_URL"], autocommit=True) as conn:
        stats = import_csv(conn, args.csv, account_id=args.account_id, before=args.before)
    print("Import complete:", stats)


if __name__ == "__main__":
    sys.exit(main() or 0)
