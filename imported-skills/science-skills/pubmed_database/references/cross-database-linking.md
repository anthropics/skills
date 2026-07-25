# Cross-Database Linking Functions

Detailed argument specifications, output schemas, and strategies for
`find_linked_biological_data` and `discover_available_links`.

## 1. `find_linked_biological_data` — Cross-database linking

Finds records in other NCBI databases linked to a source record. Use this to
identify genes, proteins, or chemicals discussed in a paper without parsing the
text. Common target databases: `gene`, `protein`, `nuccore`, `pccompound`,
`pubmed`. Supports reverse lookups (e.g., `gene → pubmed`) via the `dbfrom`
parameter. This is the required path for entity identification in large batches.

For a complete map of link types and advanced strategies, refer to

-   [Advanced Biological Database Linking](advanced-linking.md).
-   [NCBI ELink Reference](https://www.ncbi.nlm.nih.gov/books/NBK25499/#chapter4.ELink)

```bash
python3 scripts/pubmed_api.py ./gene_links.json find_linked_biological_data "35113657" gene pubmed_gene
```

**Arguments:**

-   `source_pmid` (str, required) – source record ID (PMID when dbfrom is
    pubmed)
-   `target_database` (str, required) – target NCBI database name
-   `linkname` (str, required) – elink link name
-   `dbfrom` (str, default "pubmed") – source database
-   `mindate` (str, default "") – minimum date filter (YYYY/MM/DD),
    pubmed→pubmed only
-   `maxdate` (str, default "") – maximum date filter (YYYY/MM/DD),
    pubmed→pubmed only
-   `webenv` (str, default "") – WebEnv from `cache_results_history`
-   `query_key` (str, default "") – query_key from `cache_results_history`

**Output:** `["123456", "789101"]` (target database record IDs)

Returns `[]` if no links exist. Use `fetch_database_summary` to resolve these
UIDs into accession numbers, gene names, or other metadata.

### Cross-Database Linking Strategy

Unless you are performing a standard citation traversal
(`pubmed_pubmed_citedin`) or gene lookup (`pubmed_gene`), follow the **Discover
→ Filter → Merge** workflow for complete results. **Preference**: When asked to
identify linked entities (genes, compounds, etc.), PREFER using
`find_linked_biological_data` as the primary, most efficient path, rather than
searching in external databases by name unless direct links are known to be
missing.

1.  **Discover**: Call `discover_available_links` to see which connections exist
    for the specific record.
2.  **Filter**: Identify all linkname entries that point to your target database
    (e.g., all links where `db` is `pccompound`).
3.  **Merge**: If multiple linknames point to the same database (e.g.,
    `pubmed_pccompound` and `pubmed_pccompound_mesh`), fetch from **all** of
    them and merge the results. Different linknames often represent different
    indexing methods (manual curation vs automated mapping), and using only one
    may result in missing data.

**Warning: Data Freshness.** Cross-database links (`elink`) typically lag behind
publication by weeks to months. For papers published in the last year, expect
`find_linked_biological_data` to return `[]` and pivot to searching for
accession numbers or CIDs directly in the abstract text. Does not apply to
papers older than 2 years, which should have complete links.

--------------------------------------------------------------------------------

## 2. `discover_available_links` — List available linknames

Lists all available ELink linknames for a given record. Use this when you don't
know which `linkname` to pass to `find_linked_biological_data`.

```bash
python3 scripts/pubmed_api.py ./available_links.json discover_available_links "35113657"
python3 scripts/pubmed_api.py ./available_gene_links.json discover_available_links "93986" --dbfrom gene
```

**Arguments:**

-   `source_id` (str, required) – source record ID (e.g. a PMID)
-   `dbfrom` (str, default "pubmed") – source database

**Output:**

```json
[
  {"linkname": "pubmed_gene", "db": "gene"},
  {"linkname": "pubmed_nuccore", "db": "nuccore"},
  {"linkname": "pubmed_pmc", "db": "pmc"}
]
```
