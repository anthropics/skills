# supabase-skill Benchmark Results

**Model:** sonnet
**Runs per eval:** 3
**Date:** 2026-03-18 13:31

## Summary

| Eval | Task | With Skill (avg ms) | Without Skill (avg ms) | Speedup | With Pass | Without Pass |
|------|------|---------------------|----------------------|---------|-----------|--------------|
| schema_lookup | What columns does the episodes table have, includi... | 13015ms | 15555ms | 1.19x | 3/3 | 0/3 |
| relationship_traversal | What tables are related to the plans table? Includ... | 11225ms | 18540ms | 1.65x | 3/3 | 0/3 |
| column_search | Find all columns of type jsonb across the bibleai ... | 13733ms | 13952ms | 1.01x | 3/3 | 1/3 |
| function_lookup | What RPC functions are available in the bibleai sc... | 22554ms | 14554ms | 0.64x | 3/3 | 0/3 |
| migration_generation | Write a migration to add a 'priority' integer colu... | 42394ms | 36730ms | 0.86x | 3/3 | 3/3 |
| cross_table_query | How are chat_sessions, chat_messages, and users re... | 19629ms | 16217ms | 0.82x | 3/3 | 0/3 |

## Raw Data

See `benchmark.json` for full results.

Individual responses in `with_skill/` and `without_skill/` directories.

Grading details in `grading/` directory.
