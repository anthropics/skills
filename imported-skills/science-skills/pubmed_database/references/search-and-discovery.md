# Search Functions

Detailed argument specifications, output schemas, search strategies, and
troubleshooting for `search_pubmed` and `global_database_discovery`.

## 1. `search_pubmed` — Find PMIDs by query

Returns a list of PubMed IDs matching a free-text query. Supports full NCBI
query syntax: Boolean operators (`AND`, `OR`, `NOT`), MeSH terms and tags.

1.  Syntax: Use term[tag](e.g., Parkinson[ti]). Tags are NOT case-sensitive.
2.  Most common tags:
    -   [tiab]: Title & Abstract (Best for keyword precision).
    -   [mesh]: Medical Subject Headings (Best for conceptual accuracy).
    -   [pt]: Publication Type (Filter by Review, Clinical Trial, Case Reports).
    -   [dp]: Publication Date (Interchangeable with [pdat]).
3.  Modern Power Moves:
    -   Relative Dates: Use `"last X months"[dp]` or `"last X years"[dp]` (e.g.,
        `"last 1 months"[dp]`).
    -   Proximity Search: `"word1 word2"[tiab:~N]` finds words within N tokens.
        Use this instead of AND for multi-word concepts (e.g., `"gut
        microbiome"[tiab:~2]`).
4.  Reliability: Use YYYY/MM/DD:YYYY/MM/DD[dp] for custom ranges. Avoid dptr.

### Search Strategies & Troubleshooting

If searching returns few or no results, try at most 3 queries before changing
strategy. After 3 failed searches, the query is flawed. Broaden to core entities
(gene + disease), fetch 5 abstracts, and adopt the authors' vocabulary.
Relaxation order:

1.  Drop Field Restrictors: If you used [tiab]/[ti]/[pt] in the query and got no
    results, remove them: key terms often appear in body text, not titles.
    -   Too restrictive: `"CRISPR"[ti] AND "indirect cardiovascular side
        effects"[tiab]`
    -   Better: `"CRISPR" AND "cardiovascular" AND ("side effects" OR "toxicity"
        OR "unintended")`
2.  Use Broad Synonyms: Group standardized synonyms with OR.
    -   Example: `("cardiovascular" OR "cardiac" OR "heart") AND ("toxicity" OR
        "adverse effects" OR "side effects" OR "off-target")`
3.  Use MeSH Terms: If keywords fail, use MeSH indexed terms.
    -   Example: `"CRISPR-Cas Systems"[mesh] AND "Cardiovascular
        Diseases/chemically induced"[mesh]`
4.  Remove Granular Constraints: For highly specific intersections, drop the
    weakest constraint first (e.g., expand date range to 2 years, or drop
    "liver" and filter broader results manually).
5.  Avoid Over-Quoting: Double quotes force **exact phrase matching**, with
    quoted words contiguous in that exact order. E.g., `"dopaminergic neurons"`
    excludes papers with "dopaminergic projection neurons", "dopamine neurons",
    "DA neurons", or with "dopaminergic" and "neurons" in separate sentences.
    Only quote multi-word terms where word order matters (anatomical regions,
    compound names). Use unquoted terms or proximity search (`[tiab:~N]`) for
    conceptual matching.
6.  Finding Primary Data: If you need raw identifiers (Sequence IDs, Chemical
    CIDs), append data-source terms to your query, e.g. `AND (accession[tiab] OR
    "GenBank"[tiab] OR "supplementary"[tiab])`. This filters out review articles
    that discuss concepts but omit the raw data.

For advanced search tags and strategies refer to

-   [PubMed Advanced Search Reference](advanced-search.md).
-   https://pubmed.ncbi.nlm.nih.gov/help/

```bash
uv run scripts/pubmed_api.py ./search_results.json search_pubmed "BRCA1 cancer" --max_results 5 --sort_by relevance
```

**Arguments:**

-   `query` (str, required) – free-text or structured NCBI query
-   `max_results` (int, default 10) – maximum PMIDs to return
-   `sort_by` (str, default "relevance") – `relevance`, `pub_date`, `Author`,
    `JournalName`, or `Title`

**Output:** `["35113657", "31234568"]`

**Filtering tips:**

Prefer restrictors in initial queries to reduce noise. If a restricted query
returns 0 results, see Troubleshooting above.

-   Publication type: append `AND "systematic review"[pt]` or `AND
    "meta-analysis"[pt]` or `AND "clinical trial"[pt]`
-   Date range: append `AND 2023/01:2023/12[dp]`
-   Title/abstract only: use `[tiab]` tag, e.g. `"CRISPR off-target"[tiab]`
-   Exclude noise: append `NOT "comment"[pt] NOT "editorial"[pt]` if getting too
    many non-original research results.

--------------------------------------------------------------------------------

## 2. `global_database_discovery` — Count hits across all NCBI databases

Reports how many records match a query across every NCBI database at once.
Useful for deciding which databases are worth querying for a given topic.

```bash
uv run scripts/pubmed_api.py ./crispr_counts.json global_database_discovery "CRISPR"
```

**Arguments:**

-   `query` (str, required) – free-text query

**Output:** `dict[str, int]` — keys are NCBI database names (e.g. `pubmed`,
`pmc`, `gene`), values are hit counts. Only databases with ≥1 hit are included.
Example: `json {"pubmed": 14500, "pmc": 4200, "gene": 12, "protein": 105}`
