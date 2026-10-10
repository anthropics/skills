# Exporting data from Copilot Money

1. Open the Copilot Money iOS app.
2. Settings → Account → Export Data.
3. Select "Transactions" (and any date range — default all-time is fine).
4. Copilot emails you a `.csv` file. Download it.

## Expected columns

`ledger-one` expects these columns (default Copilot export format):
- `date` (YYYY-MM-DD)
- `name` (merchant / description)
- `amount` (negative = debit)
- `category` (your Copilot category)
- `account` (source account name)

If your export uses different column names, edit them in a text editor before importing.

## The `--before` cutoff (important)

Pick a **cutover date** — the first day you want ledger-one to own transactions going forward. Typically today. Copilot history up to that date is imported; everything on/after is skipped so it doesn't collide with your first SimpleFIN backfill.

Example: if today is 2026-04-15 and you want ledger-one to take over today:

```
python scripts/import_copilot.py ~/Downloads/copilot.csv \
  --account-id <simplefin-account-id> \
  --before 2026-04-15
```

Then your first SimpleFIN pull handles 2026-04-15 forward:

```
python scripts/pull.py --days 90
```

The `--account-id` attributes all Copilot rows to a single SimpleFIN account. If you had multiple accounts in Copilot, run the import once per account with a filtered CSV, or accept that all historical rows are grouped under one account_id for reporting purposes.

## Idempotency

Re-running the import with the same CSV and cutoff is a no-op — transaction IDs are deterministic hashes of `date+name+amount`.
