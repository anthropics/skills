---
name: migrate
description: Migrates vector data from Pinecone to PostgreSQL with pgvector using vec2pg. Use when the user mentions Pinecone to Postgres migration, pgvector setup, vec2pg, vector index export, moving embeddings off Pinecone, or Supabase/pgvector as a Pinecone replacement — even if they only say "migrate my vectors" or "switch from Pinecone".
license: Complete terms in LICENSE.txt
compatibility: Python 3.10+, Docker, pip install vec2pg, Pinecone API key, network access for Pinecone API and Docker image pull
metadata:
  author: mem0ai
  version: "1.0.0"
  category: development-and-technical
---

# Pinecone → PostgreSQL Migration

Automatic database migration skill. Migrates data from **Pinecone** to **PostgreSQL with pgvector** using [vec2pg](https://github.com/supabase-community/vec2pg).

## Workflow

Copy this checklist and track progress:

```
Migration Progress:
- [ ] Step 1: Install vec2pg
- [ ] Step 2: Start pgvector Postgres container
- [ ] Step 3: Run vec2pg migration
- [ ] Step 4: Verify row count in Postgres
```

### Step 1: Install dependencies

```bash
pip3 install vec2pg
```

### Step 2: Ensure Docker is running and pull pgvector image

```bash
docker run --name pgvector_postgres \
  -e POSTGRES_USER=${PG_USER} \
  -e POSTGRES_PASSWORD=${PG_PSD} \
  -e POSTGRES_DB=${PG_DB} \
  -p 5432:5432 \
  -d pgvector/pgvector:pg16
```

Read `PG_USER`, `PG_PSD` (postgres password), and `PG_DB` from the shell or `.env` file. If the container already exists, run `docker start pgvector_postgres` instead.

### Step 3: Migrate data

```bash
vec2pg pinecone migrate $INDEX $PINECONE_API_KEY $PG_STR
```

Read `INDEX`, `PINECONE_API_KEY`, and `PG_STR` from the shell or `.env` file.

### Step 4: Verify migration

```bash
psql "$PG_STR" -c "SELECT COUNT(*) FROM vec2pg.\"${INDEX}\";"
```

Compare the count against Pinecone index `total_vector_count`.

## Agent instructions

1. Load env vars from `.env` if present — see [references/environment.md](references/environment.md).
2. Confirm Docker is running before Step 2.
3. Run steps in order; do not skip the pgvector container setup.
4. Report final row count and flag port/container conflicts on `5432`.
5. Do not commit API keys or connection strings.

## Safety

- Pinecone source data is read-only; migration does not delete Pinecone vectors.
- Prefer a fresh local Postgres container before touching production databases.

## References

- Environment variables: [references/environment.md](references/environment.md)
- Troubleshooting and output schema: [references/troubleshooting.md](references/troubleshooting.md)
- vec2pg: https://github.com/supabase-community/vec2pg
