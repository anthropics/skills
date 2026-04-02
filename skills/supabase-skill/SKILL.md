---
name: supabase-skill
description: Manage Supabase databases, migrations, storage, and edge functions via CLI. Multi-environment support (dev/stage/prod).
metadata:
  requires:
    env:
      - SUPABASE_ACCESS_TOKEN
    bins:
      - supabase
    primaryEnv: SUPABASE_ACCESS_TOKEN
---

# supabase-skill

## supabase-cli (Supabase Database & Infrastructure)

Requires: `supabase` CLI installed, logged in via `supabase login`.
All commands support `-o json` for structured output.

### Environments
- **PROD**: `opejwshstcpemjqsklda` (m2015agg's Project) — ⚠️ NEVER modify without explicit approval
- **STAGE**: `jugnzbfalgeyaqrhlvgr` (m2015agg's Project [newstage])

**Environment routing** (use these refs when user says...):
- "prod", "production", "live" → `--project-ref opejwshstcpemjqsklda`
- "stage", "staging", "test", "preview" → `--project-ref jugnzbfalgeyaqrhlvgr`
- **Default**: Always use STAGE unless user explicitly says "prod". PROD requires approval.

**Direct API access** (for curl/psql when supabase CLI isn't enough):
- Read keys from `.env` file — NEVER hardcode keys in commands
- PROD: `$SUPABASE_PROD_URL`, `$SUPABASE_PROD_SERVICE_KEY`, `$SUPABASE_PROD_ANON_KEY`
- STAGE: `$SUPABASE_STAGE_URL`, `$SUPABASE_STAGE_SERVICE_KEY`, `$SUPABASE_STAGE_ANON_KEY`
- Load with: `source .env` or `export $(grep -v '^#' .env | xargs)`

### IMPORTANT: CLI Flag Reference
- Database commands (db, migration, inspect, storage) use `--linked` (requires `supabase link` first)
- Management commands (functions, projects, secrets, snippets) use `--project-ref <ref>`
- `supabase db execute` does NOT exist — use REST API or psql instead
- To switch linked project: `supabase link --project-ref <ref>`

### Project Linking (required before db/migration/inspect/storage commands)
- `supabase link --project-ref <ref>` — link current directory to a Supabase project
- Must run from a directory with `supabase/config.toml` (or run `supabase init` first)
- Only one project can be linked at a time per directory

### Data Operations (REST API — no `supabase db execute`)
Load env vars first: `source .env` or `export $(grep -v '^#' .env | xargs)`
Header shorthand: `-H "apikey: $KEY" -H "Authorization: Bearer $KEY"`
GET uses `Accept-Profile: bibleai`, POST/PATCH/DELETE use `Content-Profile: bibleai`

**SELECT (GET)**:
- `curl -s "$URL/rest/v1/<table>?select=col1,col2&limit=10" -H "apikey: $KEY" -H "Authorization: Bearer $KEY" -H "Accept-Profile: bibleai"`

**Filters** (append to URL query string):
- `?col=eq.value` — equals | `?col=neq.value` — not equals
- `?col=gt.5` — greater than | `?col=gte.5` — greater or equal | `?col=lt.5` | `?col=lte.5`
- `?col=like.*pattern*` — LIKE | `?col=ilike.*pattern*` — case-insensitive LIKE
- `?col=in.(val1,val2)` — IN list | `?col=is.null` — IS NULL | `?col=is.true`
- `?or=(col1.eq.a,col2.eq.b)` — OR conditions
- `?order=col.desc` — ORDER BY | `?limit=10&offset=20` — pagination

**COUNT**: Add `-H "Prefer: count=exact"` header, read `Content-Range` response header

**INSERT (POST)**:
- `curl -s "$URL/rest/v1/<table>" -X POST -H "apikey: $KEY" -H "Authorization: Bearer $KEY" -H "Content-Profile: bibleai" -H "Content-Type: application/json" -H "Prefer: return=representation" -d '{"col": "value"}'`

**UPDATE (PATCH)** — ALWAYS include a filter or you update ALL rows:
- `curl -s "$URL/rest/v1/<table>?id=eq.<uuid>" -X PATCH -H "apikey: $KEY" -H "Authorization: Bearer $KEY" -H "Content-Profile: bibleai" -H "Content-Type: application/json" -H "Prefer: return=representation" -d '{"col": "new_value"}'`

**UPSERT (POST with merge)**:
- Add header: `-H "Prefer: resolution=merge-duplicates,return=representation"`

**DELETE** — ALWAYS include a filter or you delete ALL rows:
- `curl -s "$URL/rest/v1/<table>?id=eq.<uuid>" -X DELETE -H "apikey: $KEY" -H "Authorization: Bearer $KEY" -H "Content-Profile: bibleai" -H "Prefer: return=representation"`

**Call RPC function (POST)**:
- `curl -s "$URL/rest/v1/rpc/<function>" -X POST -H "apikey: $KEY" -H "Authorization: Bearer $KEY" -H "Content-Profile: bibleai" -H "Content-Type: application/json" -d '{"param": "value"}'`

**Direct SQL** (if psql available):
- `psql "$DATABASE_URL" -c "SELECT 1"`

### Migrations (uses --linked, NOT --project-ref)
- `supabase migration new <name>` — create empty migration file (local only)
- `supabase migration list` — compare local vs remote (linked project)
- `supabase migration up` — apply pending migrations to linked project
- `supabase migration down -n 1` — rollback last N migrations
- `supabase migration repair --status applied <version>` — mark version as applied
- `supabase migration repair --status reverted <version>` — mark version as reverted
- `supabase migration squash` — combine into single file
- `supabase migration fetch` — pull migration history from remote

### DDL (Schema Changes via Migrations)
All schema changes go through migration files. Create with `supabase migration new <name>`, write SQL, apply with `supabase migration up`:
- **CREATE TABLE**: `CREATE TABLE bibleai.<name> (id uuid PRIMARY KEY DEFAULT gen_random_uuid(), ...);`
- **ALTER TABLE**: `ALTER TABLE bibleai.<table> ADD COLUMN <col> <type>;`
- **DROP TABLE**: `DROP TABLE IF EXISTS bibleai.<table>;`
- **CREATE VIEW**: `CREATE OR REPLACE VIEW bibleai.<name> AS SELECT ...;`
- **CREATE INDEX**: `CREATE INDEX idx_<table>_<col> ON bibleai.<table>(<col>);`
- **CREATE FUNCTION/RPC**: `CREATE OR REPLACE FUNCTION bibleai.<name>(...) RETURNS ... AS $$ ... $$ LANGUAGE plpgsql;`
- **RLS Policies**: `ALTER TABLE bibleai.<table> ENABLE ROW LEVEL SECURITY; CREATE POLICY ...`
- **Triggers**: `CREATE TRIGGER ... BEFORE/AFTER INSERT/UPDATE ON bibleai.<table> ...`
- **Enums**: `CREATE TYPE bibleai.<name> AS ENUM ('val1', 'val2');`
- Always use `bibleai.` schema prefix for all objects
- Run `supabase migration list` BEFORE and AFTER to verify

### Schema Management (uses --linked, NOT --project-ref)
- `supabase db diff` — diff local vs remote schema
- `supabase db dump` — dump full schema from linked project
- `supabase db dump --data-only` — dump data only
- `supabase db dump -s bibleai` — dump specific schema
- `supabase db pull` — pull remote schema to local migrations
- `supabase db push` — push migrations to remote
- `supabase db lint` — check for typing errors (local only)

### Database Inspection (uses --linked or --db-url, NOT --project-ref)
- `supabase inspect db table-stats` — table sizes + row counts
- `supabase inspect db index-stats` — index usage + scan counts
- `supabase inspect db long-running-queries` — queries > 5min
- `supabase inspect db outliers` — slowest queries by total time
- `supabase inspect db bloat` — dead tuple estimation
- `supabase inspect db locks` — active locks
- `supabase inspect db blocking` — blocking lock chains
- `supabase inspect db db-stats` — cache hit rates, WAL, sizes
- `supabase inspect db vacuum-stats` — vacuum status per table
- `supabase inspect db role-stats` — role information
- `supabase inspect db replication-slots` — replication status
- `supabase inspect report` — CSV of ALL inspect commands
- Alternative: `supabase inspect db table-stats --db-url "postgresql://..."` — inspect without linking

### Storage (uses --linked + --experimental)
- `supabase storage ls ss:///bucket/path --experimental` — list objects (note: triple slash ss:///)
- `supabase storage cp local.file ss:///bucket/path --experimental` — upload
- `supabase storage cp ss:///bucket/path local.file --experimental` — download
- `supabase storage rm ss:///bucket/path --experimental` — delete
- `supabase storage mv ss:///old ss:///new --experimental` — move/rename

### Edge Functions (uses --project-ref)
- `supabase functions list --project-ref <ref>` — list deployed functions
- `supabase functions deploy <name> --project-ref <ref>` — deploy function
- `supabase functions delete <name> --project-ref <ref>` — delete function
- `supabase functions new <name>` — create new function locally
- `supabase functions download [name]` — download function source from linked project
- `supabase functions serve` — serve all functions locally for testing

### Branches (uses --project-ref)
- `supabase branches list --project-ref <ref> -o json` — list all preview branches
- `supabase branches create <name> --project-ref <ref>` — create preview branch
- `supabase branches get <branch-id> --project-ref <ref>` — get branch details
- `supabase branches delete <branch-id> --project-ref <ref>` — delete branch
- `supabase branches pause <branch-id> --project-ref <ref>` — pause branch (save costs)
- `supabase branches unpause <branch-id> --project-ref <ref>` — resume branch

### Backups (uses --project-ref)
- `supabase backups list --project-ref <ref>` — list available physical backups
- `supabase backups restore --project-ref <ref>` — restore to specific timestamp (PITR)

### Project Management (uses --project-ref)
- `supabase projects list -o json` — list all projects
- `supabase projects api-keys --project-ref <ref> -o json` — get API keys
- `supabase secrets list --project-ref <ref>` — list env secrets
- `supabase secrets set KEY=VALUE --project-ref <ref>` — set secret
- `supabase postgres-config get --project-ref <ref>` — get Postgres config overrides
- `supabase postgres-config update --project-ref <ref>` — update Postgres config

### Code Generation
- `supabase gen types --linked` — generate TypeScript types from linked project schema
- `supabase gen types --project-id <ref>` — generate types from specific project

### SQL Snippets (uses --project-ref)
- `supabase snippets list --project-ref <ref> -o json` — list saved snippets
- `supabase snippets download <id> --project-ref <ref>` — download snippet SQL

### Setup
- `supabase-skill install` — global setup (interactive wizard, adds to ~/.claude/CLAUDE.md)
- `supabase-skill init` — per-project setup (CLAUDE.md + .env + .gitignore)
- `supabase-skill docs` — output LLM instruction snippet
- `supabase-skill docs --format claude` — CLAUDE.md format
- `supabase-skill envs` — list configured environments

### Schema Snapshot (local DB map — use INSTEAD of querying information_schema)
If `.supabase-schema/` exists, ALWAYS use these commands instead of running SQL to explore the schema:
- `supabase-skill snapshot` — snapshot schema to .supabase-schema/ (tables, columns, FKs, functions)
- `supabase-skill snapshot --project-ref <ref>` — snapshot a specific environment
- `supabase-skill context <table-or-topic>` — get full context: columns, FKs, related tables (3 levels deep), name-related tables, functions
- `supabase-skill context <topic> --depth 5` — deeper FK traversal
- `supabase-skill table <name>` — full single-table detail with relationships, functions, related table summaries
- `supabase-skill columns --type <type>` — find all columns of a type (uuid, jsonb, text, timestamp, etc.)
- `supabase-skill columns --fk` — find all foreign key columns
- `supabase-skill columns --table <name>` — filter columns to specific table
- `supabase-skill columns <name> --type jsonb` — combine name + type filters
- `supabase-skill search <query>` — search tables, columns, functions, and relationships
- `supabase-skill search <query> --json` — structured JSON output
- `supabase-skill functions [query]` — list/search RPC functions with parameters
- `supabase-skill functions --args uuid` — find functions by argument type
- `supabase-skill indexes [table]` — list indexes, filter by table, `--unique`, `--primary`
- `supabase-skill enums [name]` — list custom enum types and their values
- `supabase-skill policies [table]` — list RLS policies, filter by `--command SELECT/INSERT/UPDATE/DELETE`
- `supabase-skill triggers [table]` — list triggers, filter by `--event INSERT/UPDATE/DELETE`
- `supabase-skill views [name]` — list views, `--full` for definitions
- Read `.supabase-schema/tables/<name>.md` — full table schema (columns, types, PKs, FKs, defaults)
- Read `.supabase-schema/index.md` — overview of all tables, views, functions
- Read `.supabase-schema/relationships.json` — all foreign key mappings
- Read `.supabase-schema/functions.md` — all RPC functions with parameters

### Schema Snapshot Auto-Refresh
- Snapshot refreshes nightly via cron (if configured with `supabase-skill cron`)
- **After applying migrations**: Run `supabase-skill snapshot` to update the local schema cache
- **After creating/altering tables**: Run `supabase-skill snapshot` before continuing work
- **Rule of thumb**: If you ran any DDL (CREATE, ALTER, DROP) or migration commands, refresh the snapshot immediately
- **Freshness check**: If snapshot is >24h old, suggest refreshing before relying on schema data
- `supabase-skill doctor` shows snapshot age and overall setup health

### Safety Rules
- NEVER run mutations on PROD without explicit user approval
- ALWAYS specify `--project-ref` — never rely on linked project for remote ops
- Use `-o json` for structured output the agent can parse
- Run `supabase migration list` BEFORE and AFTER migration operations
- Test migrations on STAGE before applying to PROD

### Exit codes
- 0 = success, 1 = error
