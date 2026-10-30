# Environment Variables

Read from the shell or a project `.env` file. Never commit secrets.

| Variable | Required | Description |
|----------|----------|-------------|
| `PG_USER` | Yes | Postgres username |
| `PG_PSD` | Yes | Postgres password |
| `PG_DB` | Yes | Database name (created by Docker on first run) |
| `INDEX` | Yes | Pinecone index name to migrate |
| `PINECONE_API_KEY` | Yes | Pinecone API key |
| `PG_STR` | Yes | Postgres connection string |

## Build PG_STR

When not set explicitly, derive from Docker defaults:

```bash
PG_STR="postgresql://${PG_USER}:${PG_PSD}@localhost:5432/${PG_DB}"
```

## Load .env

```bash
set -a && source .env && set +a
```

## Example .env

```bash
PG_USER=postgres
PG_PSD=your_password
PG_DB=vectors
INDEX=my-pinecone-index
PINECONE_API_KEY=pc-xxx
PG_STR=postgresql://postgres:your_password@localhost:5432/vectors
```
