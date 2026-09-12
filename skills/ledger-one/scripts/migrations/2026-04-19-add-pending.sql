-- Add pending-transaction support.
--
-- Safe on Postgres 11+: non-volatile DEFAULT stores only metadata; no table rewrite,
-- so ACCESS EXCLUSIVE lock is held for microseconds even on populated tables.
--
-- Rollback: ALTER TABLE transactions DROP COLUMN pending;
-- After rollback, any rows still in pending state will appear as posted with
-- swipe-time posted_at. Re-pull to refresh with real posted timestamps.
--
-- Apply: psql "$DATABASE_URL" -f scripts/migrations/2026-04-19-add-pending.sql
-- Run outside the 18:00 UTC cron window to avoid racing an in-flight pull.

ALTER TABLE transactions
  ADD COLUMN IF NOT EXISTS pending BOOLEAN NOT NULL DEFAULT false;

CREATE INDEX IF NOT EXISTS idx_transactions_pending
  ON transactions (pending)
  WHERE pending = true;
