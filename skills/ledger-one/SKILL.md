---
name: ledger-one
description: Self-hosted personal finance tracker — alternative to YNAB, Copilot, Monarch, Rocket Money, Mint, and similar apps. Pulls bank transactions (pending and posted) from SimpleFIN into the user's own Postgres database, categorizes them using the user's history plus Claude. Use when the user says "track my spending", "pull my bank transactions", "categorize transactions", "import from Copilot", "set up a budgeting tool", "replace YNAB", "replace Monarch", "replace Mint", "replace Copilot Money", or asks anything about SimpleFIN, Neon, or personal finance data.
---

# ledger-one

Data layer for personal finance: pulls SimpleFIN transactions (pending and posted), categorizes them (overrides → learned patterns → Claude), and persists them in the user's own Postgres. No UI — query the data directly or build your own.

## When to use this skill
- User wants to track spending without YNAB / Copilot / Monarch / Rocket Money / Mint
- User wants to pull transactions from their bank into their own database
- User has a Copilot Money CSV export and wants to keep their labeled history
- User wants Claude to categorize transactions
- User wants pending charges visible the moment they're swiped (not 1-3 days later)

## First-time setup (Claude walks through these steps)

1. **SimpleFIN Bridge account + bank link.** See `references/simplefin_setup.md`.
2. **Create local env file.** Copy `.env.example` → `.env`.
3. **Claim token.** `python scripts/claim_token.py <base64-token>` writes `SIMPLEFIN_ACCESS_URL` into `.env` without printing the raw secret.
4. **Neon database.** See `references/neon_setup.md`.
5. **Apply schema.** `psql "$DATABASE_URL" -f scripts/schema.sql` (or paste into Neon SQL editor). Then apply each file in `scripts/migrations/` in filename order: `for f in scripts/migrations/*.sql; do psql "$DATABASE_URL" -f "$f"; done`. Each is idempotent.
6. **(Required if coming from Copilot) Import historical data.**
   - Export CSV from Copilot (`references/copilot_export.md`).
   - Pick a cutover date — the first day ledger-one will own forward. Typically today.
   - `python scripts/import_copilot.py ~/copilot.csv --account-id <id> --before YYYY-MM-DD`
7. **Configure categories.** Copy `config/categories.yaml.example` → `config/categories.yaml`, edit.
8. **Fill the rest of `.env`.** Add `DATABASE_URL`, `ANTHROPIC_API_KEY`, and optionally `LEDGER_CATEGORIZATION_MODEL`.
9. **First pull.** `python scripts/pull.py --days 90`
10. **Cron.** See `references/deploy_cron.md` — GitHub Actions workflow included.

Never ask the user to paste raw secrets into chat. `SIMPLEFIN_ACCESS_URL`, `DATABASE_URL`, and API keys should go straight into `.env`, `.env.test`, or the deployment secret manager.

## Ongoing
- **Add an override:** `python scripts/ledger_cli.py override add "STARBUCKS" "Coffee"`
- **Recategorize a transaction:** just `UPDATE transactions SET category = '...'`. The DB trigger updates the learned mapping automatically.
- **Pending vs posted:** each row has a `pending BOOLEAN`. Pending charges appear the moment they're swiped; the same row flips to `pending=false` when the bank finalizes (user-set category preserved). Add `AND NOT pending` to queries that should only reflect settled spend.
- **Query data:** `references/querying_data.md`.

## Extending
See `references/extending.md` — a separate app or analytics repo can import `ledger_one`, read from the same DB, and only write to `category_overrides`.
