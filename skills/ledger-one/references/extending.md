# Extending ledger-one

`ledger-one` is the data layer only — no UI, no API, no opinions about how you query. The expected pattern is a **two-layer architecture**:

1. **Public layer** (`ledger-one` repo): schema + pull pipeline + CLI. Install once, pull updates.
2. **Companion layer** (your repo): UI, dashboards, reports, or custom analytics. Imports `ledger_one` as a library.

## Contract

The companion layer:
- **Reads** freely from any table (`transactions`, `accounts`, `merchant_categories`).
- **Writes** only to `category_overrides` (via `scripts/ledger_cli.py override add` or direct SQL).
- **Updates** `transactions.category` when the user manually recategorizes — the DB trigger updates `merchant_categories` automatically.
- **Filters on `pending`** when reporting "settled" spend. The `transactions.pending` column is `true` for authorized-but-not-posted charges. Amounts can shift (tips, FX) or vanish (auth drops) before posting. Add `AND NOT pending` to any historical/analytical query; omit it only when showing real-time committed spend.

## Example: companion dashboard repo

```python
# dashboard/app.py
import os
import psycopg
from ledger_one.normalize import normalize_merchant  # reuse the public layer's normalizer

def top_merchants_this_month():
    with psycopg.connect(os.environ["DATABASE_URL"]) as conn:
        return conn.execute("""
            SELECT merchant_pattern, SUM(-amount) AS spent
            FROM transactions
            WHERE posted_at >= date_trunc('month', now()) AND amount < 0
              AND NOT pending
            GROUP BY merchant_pattern ORDER BY spent DESC LIMIT 10
        """).fetchall()

def recategorize(conn, tx_id: str, new_category: str):
    # The learn trigger will update merchant_categories automatically.
    conn.execute("UPDATE transactions SET category = %s WHERE id = %s",
                 (new_category, tx_id))
```

Install `ledger_one` into the companion project with `pip install -e /path/to/ledger-one` or vendor it as a git submodule. Both layers share the same `DATABASE_URL`.

## Schema migrations

Migrations live in `scripts/migrations/YYYY-MM-DD-*.sql`. Apply each manually via `psql "$DATABASE_URL" -f <file>`. There's no migration framework — the files are idempotent (`IF NOT EXISTS` / `IF EXISTS` clauses) and self-documenting. The companion layer should treat `scripts/schema.sql` as the stable contract and not depend on columns not listed there.
