# Bulk Workflows

Argument specifications for `cache_results_history` and common multi-step batch
patterns for search, fetch, linking, and large-scale retrieval.

## `cache_results_history` — Batch-upload PMIDs for bulk retrieval

Uploads a batch of PMIDs to the NCBI History Server and returns a `webenv` and
`query_key` session handle. Use this when working with **more than ~10 PMIDs**
or when the same batch of IDs will be passed to multiple subsequent calls (e.g.
fetch abstracts *and* link to genes). For small batches (≤10 IDs), pass them
inline instead — it saves a round-trip. The returned handles can be passed to
`fetch_article_abstracts` or `find_linked_biological_data`.

```bash
uv run scripts/pubmed_api.py ./batch_session.json cache_results_history "35113657,31234568,29474920"
```

**Arguments:**

-   `pmids` (list[str], required) – comma-separated PMIDs to upload.

**Output:**

```json
{
  "webenv": "NCID_1_123456789_130.14.18.97_9001",
  "query_key": "1"
}
```

--------------------------------------------------------------------------------

## Workflow Recipes

### Search → batch fetch abstracts → summarize

```bash
uv run scripts/pubmed_api.py ./mrna_melanoma_results.json search_pubmed "mRNA vaccines melanoma" --max_results 5 --sort_by relevance
uv run scripts/pubmed_api.py ./mrna_melanoma_abstracts.json fetch_article_abstracts "PMID1,PMID2,PMID3,PMID4,PMID5"
```

### Search → full text (open-access only)

```bash
uv run scripts/pubmed_api.py ./psilocybin_depression_results.json search_pubmed "psilocybin depression" --max_results 5 --sort_by relevance
uv run scripts/pubmed_api.py ./psilocybin_depression_full_text.json get_full_text_pmc "PMID1"
```

If `get_full_text_pmc` returns an error, the paper is not open-access; use
`fetch_article_abstracts` instead.

### Fuzzy citation → fetch

```bash
uv run scripts/pubmed_api.py ./nature2006_pmids.json match_raw_citations "nature|2006||||takahashi k|key0|"
uv run scripts/pubmed_api.py ./abstracts.json fetch_article_abstracts "RESOLVED_PMID"
```

### Cross-database exploration

```bash
uv run scripts/pubmed_api.py ./35113657_links.json discover_available_links "35113657"
uv run scripts/pubmed_api.py ./35113657_gene_links.json find_linked_biological_data "35113657" gene pubmed_gene
uv run scripts/pubmed_api.py ./35113657_compound_links.json find_linked_biological_data "35113657" pccompound pubmed_pccompound
uv run scripts/pubmed_api.py ./35113657_nuccore_links.json find_linked_biological_data "35113657" nuccore pubmed_nuccore
uv run scripts/pubmed_api.py ./35113657_citing_papers.json find_linked_biological_data "35113657" pubmed pubmed_pubmed_citedin
```

### Bulk Retrieval and Data Slimming (N > 10)

For large result batches, avoid processing IDs iteratively. Chain
`cache_results_history` and **shell pipelines** to perform batch retrieval and
slimming in one turn.

```bash
# 1. Search and batch-upload to get a session handle
PMIDS=$(uv run scripts/pubmed_api.py ./s.json search_pubmed "CRISPR" --max_results 50 && cat ./s.json | jq -r 'join(",")')
uv run scripts/pubmed_api.py ./session.json cache_results_history "$PMIDS"
WEBENV=$(cat ./session.json | jq -r '.webenv')

# 2. Bulk fetch AND slim to only relevant fields in ONE turn
# Use brackets in jq [ ... ] to ensure the output is a valid JSON array.
uv run scripts/pubmed_api.py ./full.json fetch_article_abstracts "" --webenv "$WEBENV" --query_key 1
cat ./full.json | jq '[.[] | {pmid: .pmid, title: .title, abstract: .abstract}]' > ./slim.json
```

When using `--webenv`/`--query_key`, pass `""` for the `pmids` argument.
