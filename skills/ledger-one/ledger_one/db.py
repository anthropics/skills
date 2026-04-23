import json
import psycopg


def upsert_accounts(db: psycopg.Connection, accounts: list[dict]) -> None:
    if not accounts:
        return
    rows = [
        (a["id"], a["name"], a.get("institution"), a.get("currency", "USD"),
         a.get("balance"), a.get("balance_date"))
        for a in accounts
    ]
    with db.cursor() as cur:
        cur.executemany(
            """
            INSERT INTO accounts (id, name, institution, currency, last_balance, last_balance_date)
            VALUES (%s, %s, %s, %s, %s, %s)
            ON CONFLICT (id) DO UPDATE SET
              name = EXCLUDED.name,
              institution = EXCLUDED.institution,
              currency = EXCLUDED.currency,
              last_balance = EXCLUDED.last_balance,
              last_balance_date = EXCLUDED.last_balance_date
            """,
            rows,
        )


def upsert_transactions(db: psycopg.Connection, txns: list[dict]) -> tuple[int, int]:
    """Insert new transactions; update pending rows on pending→posted transition.

    Returns (inserted_count, updated_count). The ON CONFLICT WHERE guard means
    already-posted rows (pending=false in DB) are NEVER mutated by this path —
    only pending rows can transition to posted. Inserts and pending→posted
    updates both go through here.
    """
    if not txns:
        return (0, 0)
    rows = [
        (
            t["id"], t["account_id"], t["amount"], t["description"],
            t["merchant_pattern"], t["category"], t["posted_at"],
            json.dumps(t.get("raw_payload") or {}), t["source"],
            bool(t.get("pending", False)),
        )
        for t in txns
    ]
    sql = """
        INSERT INTO transactions (
          id, account_id, amount, description, merchant_pattern,
          category, posted_at, raw_payload, categorized_at,
          categorization_source, pending
        ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s::jsonb, now(), %s, %s)
        ON CONFLICT (id) DO UPDATE SET
          pending = EXCLUDED.pending,
          posted_at = EXCLUDED.posted_at,
          amount = EXCLUDED.amount,
          merchant_pattern = EXCLUDED.merchant_pattern,
          raw_payload = EXCLUDED.raw_payload
        WHERE transactions.pending = true
        RETURNING (xmax = 0) AS inserted
    """
    # pull.py sends truly-new rows and pending→posted transitions. The WHERE
    # guard on ON CONFLICT blocks any update against a row that's already
    # posted — which is load-bearing (not just defensive): it prevents a stale
    # or concurrent caller from clobbering a finalized row's posted_at/amount.
    # Guard-blocked rows return an empty RETURNING set and contribute 0 to both
    # counters; all other input rows produce exactly one RETURNING row.
    inserted = 0
    updated = 0
    with db.cursor() as cur:
        cur.executemany(sql, rows, returning=True)
        while True:
            for r in cur.fetchall():
                if r[0]:
                    inserted += 1
                else:
                    updated += 1
            if not cur.nextset():
                break
    return (inserted, updated)
