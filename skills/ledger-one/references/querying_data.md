# Querying ledger-one data

All queries run against your Postgres database directly (`psql "$DATABASE_URL"` or Neon SQL editor).

**Amount sign convention:** negative = debit (money out), positive = credit (money in).

**Pending vs posted:** the `transactions.pending` column (BOOLEAN) distinguishes pending charges (visible in the bank app within minutes of swipe) from posted charges (finalized by the bank, 1–3 business days later). Most reporting queries below add `AND NOT pending` so they reflect settled activity only — pending amounts can shift (tips, FX conversion) or vanish (auth drops). When you want real-time committed spend, drop the `AND NOT pending` filter.

## Pending quick views

```sql
-- What's currently pending (haven't posted yet)?
SELECT posted_at::date AS swipe_date, description, -amount AS amount
FROM transactions WHERE pending
ORDER BY posted_at DESC;

-- Stuck pendings (auth dropped, never posted): worth investigating
SELECT posted_at::date, description, -amount AS amount
FROM transactions
WHERE pending AND posted_at < now() - interval '14 days'
ORDER BY posted_at;
```

## This month's spending by category

```sql
SELECT category, SUM(-amount) AS spent
FROM transactions
WHERE posted_at >= date_trunc('month', now()) AND amount < 0 AND NOT pending
GROUP BY category ORDER BY spent DESC;
```

## Pace-matched MTD vs last month same day

```sql
WITH d AS (SELECT EXTRACT(DAY FROM now())::int AS day)
SELECT
  SUM(CASE WHEN posted_at >= date_trunc('month', now()) THEN -amount ELSE 0 END) AS this_month,
  SUM(CASE WHEN posted_at >= date_trunc('month', now() - interval '1 month')
           AND posted_at <  date_trunc('month', now() - interval '1 month') + (SELECT day FROM d) * interval '1 day'
           THEN -amount ELSE 0 END) AS last_month_same_pace
FROM transactions WHERE amount < 0 AND NOT pending;
```

## Top 10 merchants this month

```sql
SELECT merchant_pattern, COUNT(*), SUM(-amount) AS spent
FROM transactions
WHERE posted_at >= date_trunc('month', now()) AND amount < 0 AND NOT pending
GROUP BY merchant_pattern ORDER BY spent DESC LIMIT 10;
```

## Subscription-like recurring charges

```sql
SELECT merchant_pattern, COUNT(*) AS occurrences, AVG(-amount) AS avg_amount
FROM transactions
WHERE amount < 0 AND posted_at > now() - interval '6 months' AND NOT pending
GROUP BY merchant_pattern
HAVING COUNT(*) >= 4 AND STDDEV(amount) / NULLIF(ABS(AVG(amount)), 0) < 0.1
ORDER BY avg_amount DESC;
```

## Year-over-year for a category

```sql
SELECT DATE_TRUNC('month', posted_at) AS month, SUM(-amount) AS spent
FROM transactions
WHERE category = 'Groceries' AND posted_at > now() - interval '2 years' AND NOT pending
GROUP BY month ORDER BY month;
```

## Transactions in a specific category / month

```sql
SELECT posted_at::date, description, -amount AS amount
FROM transactions
WHERE category = 'Restaurants'
  AND posted_at >= '2026-04-01' AND posted_at < '2026-05-01'
  AND NOT pending
ORDER BY posted_at;
```

## Categorization source breakdown this week

```sql
SELECT categorization_source, COUNT(*)
FROM transactions
WHERE created_at > now() - interval '7 days'
GROUP BY categorization_source;
```
