# Neon Postgres setup

1. Go to [https://console.neon.tech](https://console.neon.tech). Free tier is plenty.
2. Create a new project. Any region; pick the one closest to you. Postgres 17 recommended.
3. Copy the **connection string** from the project dashboard (it looks like `postgresql://user:pass@host/db?sslmode=require`).
4. Paste it into `.env` as `DATABASE_URL`.
5. Apply the schema:
   - Option A (terminal): `psql "$DATABASE_URL" -f scripts/schema.sql`
   - Option B (browser): open Neon SQL Editor, paste the contents of `scripts/schema.sql`, click Run.
6. Apply migrations (in date order) for any schema changes that post-date your install:
   ```
   for f in scripts/migrations/*.sql; do psql "$DATABASE_URL" -f "$f"; done
   ```
   Each migration file is idempotent (uses `IF NOT EXISTS`), so rerunning is safe.
7. Verify: `psql "$DATABASE_URL" -c "\dt"` should list `accounts`, `transactions`, `merchant_categories`, `category_overrides`.

**Backup branches:** Neon supports instant DB branching. Create a dedicated `test` branch in the console for throwaway test data, then copy `.env.test.example` to `.env.test` and set `TEST_DATABASE_URL` there. Destructive DB tests refuse non-local URLs unless you explicitly opt in for a single shell by exporting `LEDGER_ONE_ALLOW_DESTRUCTIVE_TEST_DB` equal to the *exact* `<host>/<dbname>` of your test DB (e.g. `ep-wild-shape-xxxx.us-east-2.aws.neon.tech/neondb`). A literal `1` or any other value is refused on purpose — the check is match-or-skip to prevent pointing destructive tests at prod.
