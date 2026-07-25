# Expected Outputs

Sample outputs for each script in `scripts/`. Use these as fixtures when testing
or to verify the scripts behave correctly end-to-end.

| Script | Fixture |
|---|---|
| `init_vault.py --json` | `init_vault.json` |
| `ingest_source.py --json` | `ingest_source.json` |
| `update_index.py --json` | `update_index.json` |
| `append_log.py --json` | `append_log.json` |
| `wiki_search.py --json` | `wiki_search.json` |
| `lint_wiki.py --json` | `lint_wiki.json` |
| `graph_analyzer.py --json` | `graph_analyzer.json` |
| `export_marp.py --json` | `export_marp.json` |

These were captured against a small 2-page example vault (one concept page and
one source page, both with proper frontmatter). Paths have been anonymized to
`/tmp/test-vault`.
