# Utilities

## `verify_medical_spelling` — Spell-check biomedical terms

Suggests spelling corrections for biomedical terms using NCBI's dictionary.
Useful for normalizing user-provided terminology before searching.

```bash
python3 scripts/pubmed_api.py ./spelling.json verify_medical_spelling "rhuematoid arthritus"
```

**Arguments:**

-   `term` (str, required) – term to spell-check

**Output:** `json {"original": "rhuematoid arthritus", "corrected": "rheumatoid
arthritis"}`

Returns the original term unchanged if the spelling is already correct.

--------------------------------------------------------------------------------

## `match_raw_citations` — Resolve messy citations to PMIDs

Resolves incomplete or messy bibliographic citations to PMIDs via the ecitmatch
endpoint. Each citation must be a pipe-delimited string in the format
`journal|year|volume|first_page|author_name|key|`. Empty fields are valid. The
trailing pipe is required.

For field selection strategies, journal name pitfalls, and fallback chains,
refer to [Citation Matching Guide](citation-matching.md).

```bash
uv run scripts/pubmed_api.py ./nature2006_pmids.json match_raw_citations "nature|2006||||takahashi k|key0|"
```

**Arguments:**

-   `citation_strings` (list[str], required) – comma-separated pipe-delimited
    citations

**Output:** `["16904174"]`
