# Deploying the daily pull

## Option 1: GitHub Actions (recommended)

The code can live in a public or private repo. Secrets must stay in GitHub Actions secrets, local env files, or your hosting provider's secret store. Then:

1. Add three repo secrets in Settings → Secrets and variables → Actions:
   - `SIMPLEFIN_ACCESS_URL`
   - `DATABASE_URL`
   - `ANTHROPIC_API_KEY`
2. The workflow at `.github/workflows/pull.yml` runs daily at 18:00 UTC. Adjust the cron expression as desired, but fire it *after* your bank's daily SimpleFIN refresh (see "Picking a cron time" below).
3. Trigger a manual run from the Actions tab to verify.

SimpleFIN enforces a limit of ~24 API calls per day per access token. Once daily is well under that.

## Option 2: Railway

1. Create a Railway project from this repo.
2. Add the three secrets as environment variables.
3. Enable the "Cron" feature and set the schedule to `0 18 * * *` running `python scripts/pull.py --days 7`.

## Option 3: Local crontab

```
0 18 * * * cd /path/to/ledger-one && .venv/bin/python scripts/pull.py --days 7 >> /tmp/ledger-one.log 2>&1
```

Make sure `.env` is present at the project root so `python-dotenv` picks up the credentials.

## Picking a cron time

SimpleFIN syncs each linked bank on its own ~24h cadence. If your cron fires *before* SimpleFIN's daily refresh for a given bank, that day's new transactions land in the pull the *next* day — one-day lag, indefinitely. Pick a UTC hour that falls after the latest-refreshing bank (observe the `balance-date` on the payload; see `project_simplefin_silent_staleness` memory for the rationale).

For US East Chase, SimpleFIN refresh has been observed around 13:00 UTC; 18:00 UTC gives a ~5h buffer for jitter. If you add a bank later that refreshes later in the day, shift the cron.

## Failure behavior

The pull script exits **non-zero** (GitHub Actions run goes red) when:
- Required env vars are missing (`SIMPLEFIN_ACCESS_URL`, `DATABASE_URL`, `ANTHROPIC_API_KEY`).
- The `SIMPLEFIN_ACCESS_URL` fails validation (not HTTPS, or host doesn't match `*.simplefin.org`).
- An account's `balance_date` is more than 36h behind `now()` — this is how silent SimpleFIN bank-connection staleness gets surfaced, since `errors: []` in the payload does **not** guarantee the bank connection is healthy. Re-authenticate the flagged bank at [bridge.simplefin.org](https://beta-bridge.simplefin.org).

Expected successful run output ends with a one-line `Pull complete: {...stats...}` including keys like `pending_inserts`, `posted_inserts`, `pending_to_posted_transitions`, and `duplicate_pending_suspects`. If `duplicate_pending_suspects > 0`, Chase (or another bank) may be re-issuing transaction IDs on pending→posted — see the upsert design note in the README.

## Caveats

- **Never commit `.env` or `.env.test`.** They are local secret files and should stay out of git.
- **Secret masking:** GitHub Actions masks secrets that match exact strings. `ledger-one` never prints the access URL, but if you add logging, audit it first.
- **Per-account bank errors:** the SimpleFIN payload's own `errors`/`errlist` fields are logged as warnings but do not fail the run. Stale balance-date is the gate that actually fails runs.
