import csv
import hashlib
from collections import Counter, defaultdict
from datetime import date
from pathlib import Path
from ledger_one.normalize import normalize_merchant

REQUIRED_COLUMNS = {"date", "name", "amount", "category"}
BATCH = 500


def import_csv(db, csv_path: Path, *, account_id: str, before: date) -> dict:
    """Import Copilot CSV: seed merchant_categories + import transactions strictly
    before `before` (exclusive). Idempotent via deterministic transaction IDs."""
    merchant_counts: dict[str, Counter] = defaultdict(Counter)
    tx_rows: list[tuple] = []

    with open(csv_path, newline="") as f:
        reader = csv.DictReader(f)
        missing = REQUIRED_COLUMNS - set(reader.fieldnames or [])
        if missing:
            raise ValueError(
                f"CSV missing expected columns: {sorted(missing)}. "
                f"Copilot export should have: date, name, amount, category, account."
            )
        for row in reader:
            try:
                row_date = date.fromisoformat(row["date"][:10])
            except (ValueError, KeyError):
                continue
            if row_date >= before:
                continue
            name = row["name"]
            category = row["category"]
            pattern = normalize_merchant(name)
            if pattern and category:
                merchant_counts[pattern][category] += 1
                tx_id = _deterministic_id(row)
                tx_rows.append((
                    tx_id, account_id, row["amount"], name, pattern,
                    category, row["date"], False,
                ))

    # Seed merchant_categories (most common category this run wins).
    with db.transaction():
        for pattern, counts in merchant_counts.items():
            top_category = counts.most_common(1)[0][0]
            db.execute(
                """
                INSERT INTO merchant_categories (merchant_pattern, category, last_updated)
                VALUES (%s, %s, now())
                ON CONFLICT (merchant_pattern) DO UPDATE SET
                  category = EXCLUDED.category,
                  last_updated = now()
                """,
                (pattern, top_category),
            )

    # Insert transactions in batches, idempotent via ON CONFLICT.
    tx_inserted = 0
    with db.cursor() as cur, db.transaction():
        for i in range(0, len(tx_rows), BATCH):
            batch = tx_rows[i : i + BATCH]
            cur.executemany(
                """
                INSERT INTO transactions (
                  id, account_id, amount, description, merchant_pattern,
                  category, posted_at, categorization_source, categorized_at,
                  pending
                ) VALUES (%s, %s, %s, %s, %s, %s, %s, 'copilot_import', now(), %s)
                ON CONFLICT (id) DO NOTHING
                """,
                batch,
            )
            tx_inserted += cur.rowcount

    return {
        "merchant_mappings": len(merchant_counts),
        "transactions_imported": tx_inserted,
    }


def _deterministic_id(row: dict) -> str:
    key = f"copilot:{row['date']}:{row['name']}:{row['amount']}"
    return "copilot-" + hashlib.blake2b(key.encode(), digest_size=8).hexdigest()
