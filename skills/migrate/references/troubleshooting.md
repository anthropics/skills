# Troubleshooting

| Issue | Fix |
|-------|-----|
| Port 5432 in use | Stop conflicting Postgres or use `-p 5433:5432` and update `PG_STR` |
| Container name taken | `docker rm -f pgvector_postgres` then re-run, or `docker start pgvector_postgres` |
| Auth failed | Verify `PG_USER` / `PG_PSD` match Docker env vars and `PG_STR` |
| Empty table after migration | Confirm `INDEX` name and `PINECONE_API_KEY` are correct |
| `vec2pg: command not found` | Re-run `pip3 install vec2pg` in the active Python environment |
| Docker not running | Start Docker Desktop or the Docker daemon before Step 2 |

## Output schema

vec2pg writes to schema `vec2pg`, table `vec2pg.<index_name>`:

| Column | Type | Description |
|--------|------|-------------|
| `id` | text | Vector ID from Pinecone |
| `vector` | vector | Embedding values |
| `metadata` | jsonb | Pinecone metadata payload |
| `namespace` | text | Pinecone namespace |

Reshape into a production table after migration:

```sql
INSERT INTO my_vectors (id, embedding, metadata, namespace)
SELECT id, vector, metadata, namespace
FROM vec2pg.my_index;
```
