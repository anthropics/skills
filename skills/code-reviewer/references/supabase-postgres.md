# Supabase and Postgres checks

Apply these on top of the general review passes in SKILL.md when the code uses Supabase, PostgREST, or Postgres with row-level security. Ask for the migrations and RLS policies if they aren't in the code under review; in this stack, the policies are the real security layer.

## Contents

- Row-level security
- Keys and auth
- Injection
- Correctness
- Edge Functions
- Performance

## Row-level security

Any table the anon or authenticated key can reach must have RLS enabled **and** correct policies. Check every policy:

- `USING (true)`, or a missing `WITH CHECK` on insert/update, lets users write rows they don't own or change `user_id`/`org_id` to someone else's.
- Policies should compare against `auth.uid()` (or a tenant/membership lookup), never against a value the client sends.
- SELECT, INSERT, UPDATE, and DELETE need their own policies; flag missing ones. UPDATE needs both `USING` and `WITH CHECK`.
- New tables in migrations without `ALTER TABLE ... ENABLE ROW LEVEL SECURITY`.
- Storage: public buckets holding private files; `storage.objects` policies that don't check folder ownership.

## Keys and auth

- **The service-role key** must never be in client code, `NEXT_PUBLIC_*`/`VITE_*` variables, or mobile apps. Server code that uses it bypasses RLS, so that code must do its own authorization checks.
- **`user_metadata` is editable by the user.** Never base roles or permissions on `raw_user_meta_data`/`user_metadata`. Use `app_metadata`, a roles table, or custom claims set on the server.
- **On the server, use `supabase.auth.getUser()`** (it validates the token with the auth server), not `getSession()`, for authorization decisions.

## Injection

- Filter strings built from input: `.or(\`name.ilike.%${q}%\`)`, `.filter(col, op, input)`, or `.order(input)` with no allow-list let users inject extra filter clauses. Sanitize the input or use the typed methods, for example `.ilike('name', \`%${q}%\`)`.
- Postgres functions called through `.rpc()`: look for `EXECUTE` with string concatenation or `format('%s', ...)` instead of `format('%I', ...)`/`%L` or `EXECUTE ... USING`.
- `SECURITY DEFINER` functions bypass RLS. They need explicit authorization checks, `SET search_path = ''` (or a fixed schema), and limited `GRANT EXECUTE`. Flag `SECURITY DEFINER` functions or views exposed in the `public` schema.

## Correctness

- Multi-step writes done as separate client calls instead of one transaction or RPC, so a failure halfway leaves data inconsistent.
- Check-then-insert races that need a unique constraint or `ON CONFLICT`.

## Edge Functions

- Verify the JWT (don't turn off `verify_jwt` without a reason), check the CORS config, and verify webhook signatures.

## Performance

- N+1: `.from('x').select().eq('id', item.id)` per item, including inside `Promise.all(items.map(...))`. Fix with a nested select (`select('*, order_items(*, product:products(*))')`), `.in('id', ids)`, or a single RPC or view.
- `select('*')` when a few columns or a count is needed; no pagination (`.range()`, `.limit()`, or cursor-based paging for large tables).
- Missing indexes on columns used in filters, joins, ordering, foreign keys, and **RLS policies** (a policy runs on every row it checks); suggest `EXPLAIN ANALYZE` to confirm.
