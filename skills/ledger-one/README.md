# ledger-one

Pull bank transactions from SimpleFIN into your own Postgres, categorized with Claude. A self-hosted alternative to YNAB, Copilot, Monarch, Rocket Money, Mint, and other personal-finance apps — for people who want to own their data.

- **~$15/year** (SimpleFIN Bridge) + pennies in Claude API calls.
- **Your database**, your queries, your UI.
- **Pending and posted transactions** — in-flight charges show up within minutes of swiping, then transition to posted in the same row when the bank finalizes.
- Ships as an Anthropic skill — Claude walks you through setup.

## Architecture

A 3-tier categorization cascade:

1. **Explicit overrides** (`category_overrides` table) — user rules that always win.
2. **Learned patterns** (`merchant_categories` table) — built from your history, seeded optionally from a Copilot CSV export.
3. **Claude Haiku** — fallback for genuinely novel merchants, prompt-cached so it's near-free.

### Pending transactions

Each row in `transactions` carries a `pending BOOLEAN` flag. SimpleFIN is queried with `pending=1`, so authorized-but-not-posted charges land in the DB immediately — categorized on first sight. When the bank posts the charge, the same row is updated in place (`pending=false`, real `posted_at`, final `amount`) and the user-assigned category is preserved. Already-posted rows are protected from mutation by a `WHERE transactions.pending = true` guard on the upsert.

Add `AND NOT pending` to reporting queries that should only reflect settled spend. See [`references/querying_data.md`](references/querying_data.md) for the patterns.

Schema: [`scripts/schema.sql`](scripts/schema.sql). Migrations: [`scripts/migrations/`](scripts/migrations/). Pipeline: [`ledger_one/pull.py`](ledger_one/pull.py).

## Requirements

- **Python 3.11+**
- **Postgres 14+** (the learn trigger uses `REFERENCING NEW TABLE` which requires PG 14 or later; Neon's free tier runs PG 17)
- **SimpleFIN Bridge account** (~$15/year)
- **Anthropic API key** (Haiku categorization costs ~$0.10-0.20/month at typical volume)

## 5-minute quickstart

1. Install: `pip install -e ".[dev]"`
2. Copy `.env.example` to `.env`, then claim the SimpleFIN token. The claim script writes `SIMPLEFIN_ACCESS_URL` into `.env` without printing the raw secret (see [`references/simplefin_setup.md`](references/simplefin_setup.md)).
3. Neon Postgres → apply `scripts/schema.sql`, then apply each file in `scripts/migrations/` in date order (see [`references/neon_setup.md`](references/neon_setup.md)).
4. (Optional) Import Copilot history: `python scripts/import_copilot.py ~/copilot.csv --account-id <id> --before YYYY-MM-DD`.
5. `cp config/categories.yaml.example config/categories.yaml` and edit.
6. `python scripts/pull.py --days 90`.

Full walkthrough: [`SKILL.md`](SKILL.md).

Never paste `SIMPLEFIN_ACCESS_URL`, `DATABASE_URL`, or API keys into chat or commit them to git. Put them directly into local env files or your deployment secret store.
See [`SECURITY.md`](SECURITY.md) for reporting and secret-handling guidance.

## Extending

This is the data layer. Build your UI on top in a separate repo:

```python
from ledger_one.normalize import normalize_merchant
import psycopg
# ... read from transactions, write only to category_overrides
```

See [`references/extending.md`](references/extending.md) for the full pattern.

## Querying your data

Sample SQL: [`references/querying_data.md`](references/querying_data.md).

## License

MIT.
