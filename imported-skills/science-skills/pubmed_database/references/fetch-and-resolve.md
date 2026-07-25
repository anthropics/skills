# Fetch & Resolve Functions

Detailed argument specifications, output schemas, and usage guidance for
`fetch_article_abstracts`, `get_full_text_pmc`, and `fetch_database_summary`.

## 1. `fetch_article_abstracts` — Get metadata + abstracts

Retrieves title, authors, journal, publication date, DOI, and abstract text for
a batch of PMIDs via a single efetch XML call. Structured abstracts (BACKGROUND,
METHODS, RESULTS, CONCLUSION) are concatenated with labels.

```bash
uv run scripts/pubmed_api.py ./abstracts.json fetch_article_abstracts "35113657,31234568"
```

**Arguments:**

-   `pmids` (list[str], required) – comma-separated PMIDs
-   `webenv` (str, default "") – WebEnv from `cache_results_history`
-   `query_key` (str, default "") – query_key from `cache_results_history`

**Output:** `list[object]` — one object per PMID:

-   `pmid` (str) — always present
-   `title` (str | null) — `null` for dead/unpopulated records
-   `authors` (list[str]) — `"LastName Initials"` format; may be empty
-   `journal` (str | null) — full journal name
-   `pubdate` (str | null) — `"YYYY Mon DD"` or `MedlineDate` fallback
-   `doi` (str | null) — `null` if no DOI on record
-   `abstract` (str | null) — plain text, or `"LABEL: text\nLABEL: text"` for
    structured abstracts

**Important**: If both the `title` and `abstract` are `null`, the PMID is an
unpopulated or "dead" database record. If this occurs, report that the paper
does not exist. **DO NOT** attempt to summarize neighboring PMIDs or guess the
intended paper unless explicitly asked to disambiguate.

--------------------------------------------------------------------------------

## 2. `get_full_text_pmc` — Open-access full text

Retrieves full text of an open-access article from PMC. **Important** Only
returns articles in the **PMC Open Access Subset** — with licenses that permit
text mining and redistribution. Being "in PMC" is not sufficient; many PMC
articles have restrictive licenses that exclude them from the OA subset.

```bash
uv run scripts/pubmed_api.py ./full_text_35113657.json get_full_text_pmc "35113657"
```

**Arguments:**

-   `pmid` (str, required) – PMID of the article

**Output (success):** `{"pmid": str, "full_text": str}`

**Output (error):** `{"error": str, "endpoint": str}` — article is paywalled,
embargoed, or not in the OA subset.

**Important**: If you plan to use `get_full_text_pmc`, pre-filter your search
with `AND "pmc open access"[filter]` to only return papers that are in the OA
subset. This avoids wasting calls on papers that will inevitably fail. *Note*:
The `"pmc open access"[filter]` is highly restrictive and may return zero
results for some topics. If so, you can fall back to `"free full text"[Filter]`,
but be prepared to handle failures in `get_full_text_pmc` as not all free papers
are in the BioC OA subset. Example:

```bash
uv run scripts/pubmed_api.py ./oa_results.json search_pubmed \
  "psilocybin depression AND \"pmc open access\"[filter]" --max_results 5
```

If retrieval fails, use `fetch_article_abstracts` to fetch the abstract only.

--------------------------------------------------------------------------------

## 3. `fetch_database_summary` — Resolve UIDs from any NCBI database

Retrieves summary metadata for records in any NCBI database. Use this to resolve
the opaque UIDs returned by `find_linked_biological_data` into human-readable
data (accession numbers, gene names, descriptions, etc.).

```bash
uv run scripts/pubmed_api.py ./nuccore_summary.json fetch_database_summary nuccore "1798174254,1798172431"
uv run scripts/pubmed_api.py ./gene_summary.json fetch_database_summary gene "43740568"
uv run scripts/pubmed_api.py ./compound_summary.json fetch_database_summary pccompound "2244"
```

**Arguments:**

-   `database` (str, required) – target NCBI database (e.g. `nuccore`, `gene`,
    `protein`, `pccompound`)
-   `id_list` (list[str], required) – comma-separated UIDs

**Output:** `list[object]` — one object per UID with database-specific fields.
Key fields by database:

-   **nuccore/protein**:
    -   `uid` (str) — NCBI unique identifier for the sequence record
    -   `title` (str) — sequence definition line (e.g. `"Homo sapiens BRCA1
        mRNA, complete cds"`)
    -   `accessionversion` (str) — versioned accession number (e.g.
        `"NM_007294.4"`)
    -   `organism` (str) — source organism (e.g. `"Homo sapiens"`)
    -   `slen` (int) — sequence length in base pairs or amino acids
    -   `moltype` (str) — molecule type (`"dna"`, `"rna"`, `"aa"`)
    -   `sourcedb` (str) — originating database (`"refseq"`, `"insd"`, etc.)
-   **gene**:
    -   `uid` (str) — NCBI Gene ID
    -   `name?` (str) — official gene symbol (e.g. `"BRCA1"`)
    -   `description` (str) — full gene name (e.g. `"BRCA1 DNA repair
        associated"`)
    -   `summary` (str) — functional summary paragraph from RefSeq
    -   `organism` (object) — `{"scientificname": str, "commonname": str,
        "taxid": int}`
    -   `otheraliases` (str) — comma-separated alternative gene symbols
    -   `genomicinfo` (list[object]) — chromosomal location(s), each with
        `chrloc`, `chrstart`, `chrstop`, `exoncount`
-   **pccompound**:
    -   `uid` (str) — NCBI record UID
    -   `cid` (int) — PubChem Compound ID
    -   `synonymlist` (list[str]) — common names and identifiers (e.g.
        `["Aspirin", "Acetylsalicylic acid", ...]`)
    -   `sourcecategorylist` (list[str]) — data source categories (e.g.
        `["Deposited Substances", "Chemical Vendors", ...]`)
