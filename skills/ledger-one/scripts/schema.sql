CREATE TABLE IF NOT EXISTS accounts (
  id TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  institution TEXT,
  currency TEXT DEFAULT 'USD',
  last_balance NUMERIC,
  last_balance_date TIMESTAMPTZ,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS transactions (
  id TEXT PRIMARY KEY,
  account_id TEXT REFERENCES accounts(id),
  amount NUMERIC NOT NULL,
  description TEXT,
  merchant_pattern TEXT,
  category TEXT,
  posted_at TIMESTAMPTZ NOT NULL,
  raw_payload JSONB,
  categorized_at TIMESTAMPTZ,
  categorization_source TEXT,
  created_at TIMESTAMPTZ DEFAULT now(),
  pending BOOLEAN NOT NULL DEFAULT false
);

CREATE TABLE IF NOT EXISTS merchant_categories (
  merchant_pattern TEXT PRIMARY KEY,
  category TEXT NOT NULL,
  last_updated TIMESTAMPTZ DEFAULT now()
);

CREATE TABLE IF NOT EXISTS category_overrides (
  merchant_pattern TEXT PRIMARY KEY,
  category TEXT NOT NULL,
  created_at TIMESTAMPTZ DEFAULT now()
);

CREATE INDEX IF NOT EXISTS idx_transactions_posted_at ON transactions(posted_at);
CREATE INDEX IF NOT EXISTS idx_transactions_category ON transactions(category);
CREATE INDEX IF NOT EXISTS idx_transactions_account_posted ON transactions(account_id, posted_at);
CREATE INDEX IF NOT EXISTS idx_transactions_merchant_pattern ON transactions(merchant_pattern);
CREATE INDEX IF NOT EXISTS idx_transactions_pending ON transactions (pending) WHERE pending = true;

CREATE OR REPLACE FUNCTION ledger_one_learn_on_update()
RETURNS TRIGGER AS $$
BEGIN
  INSERT INTO merchant_categories (merchant_pattern, category, last_updated)
  SELECT DISTINCT ON (n.merchant_pattern) n.merchant_pattern, n.category, now()
  FROM new_rows n
  JOIN old_rows o ON n.id = o.id
  WHERE n.merchant_pattern IS NOT NULL
    AND n.merchant_pattern <> ''
    AND n.category IS DISTINCT FROM o.category
  ORDER BY n.merchant_pattern, n.id DESC
  ON CONFLICT (merchant_pattern) DO UPDATE
    SET category = EXCLUDED.category,
        last_updated = EXCLUDED.last_updated;
  RETURN NULL;
END;
$$ LANGUAGE plpgsql;

DROP TRIGGER IF EXISTS trg_ledger_one_learn ON transactions;
CREATE TRIGGER trg_ledger_one_learn
  AFTER UPDATE ON transactions
  REFERENCING NEW TABLE AS new_rows OLD TABLE AS old_rows
  FOR EACH STATEMENT
  EXECUTE FUNCTION ledger_one_learn_on_update();
