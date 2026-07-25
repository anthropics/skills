# Citation Matching Guide (ecitmatch)

The `match_raw_citations` tool uses NCBI's ecitmatch endpoint, which predates
modern APIs. This guide covers the pipe format, field selection strategies, and
what to do when matching fails.

--------------------------------------------------------------------------------

## 1. The Pipe Format

Each citation is a single string with 7 pipe-separated fields and a trailing
pipe:

```
journal|year|volume|first_page|author_name|key|
```

All fields except `journal` are optional — empty segments are valid. The `key`
is an arbitrary label you choose to track which citation matched which PMID in
the results.

**Examples:** `nature|2006||||takahashi k|ref1| proc natl acad
sci|2007|104|11760|takahashi k|ref2| cell|2020|183||doe j|ref3|`

Assemble the pipe-delimited string directly — all fields except `journal` are
optional, so leave unwanted segments empty.

--------------------------------------------------------------------------------

## 2. Which Fields Matter Most

Not all fields contribute equally. ecitmatch uses fuzzy matching, but some
combinations are far more reliable than others.

**High-value combinations (use these first):** - `journal` + `author` + `year` —
resolves most citations - `journal` + `volume` + `first_page` — uniquely
identifies articles even without author/year

**Low-value on their own:** - `year` alone — too broad - `first_page` alone —
page numbers repeat across volumes - `volume` alone — meaningless without
journal

**Strategy:** Start with whatever fields you have. If it misses, drop the most
uncertain field (often `first_page` or `volume`) and retry — ecitmatch sometimes
does worse with partly-wrong data than with missing data.

--------------------------------------------------------------------------------

## 3. Journal Name Pitfalls

The `journal` field is the most critical and the most error-prone.

**Abbreviation vs. full name:** ecitmatch accepts both, but they are not
interchangeable for all journals. When in doubt, use the NLM abbreviated form.

Common mappings: - "The New England Journal of Medicine" → `n engl j med` -
"Proceedings of the National Academy of Sciences" → `proc natl acad sci` - "The
Journal of Biological Chemistry" → `j biol chem` - "JAMA" → `jama` (already
abbreviated)

**Case:** ecitmatch is case-insensitive. `Nature` and `nature` are equivalent.

**Punctuation:** Strip periods from abbreviations. Use `j biol chem` not `J.
Biol. Chem.`

--------------------------------------------------------------------------------

## 4. Author Name Format

ecitmatch expects **last name followed by first initial**, lowercase, no
periods, no commas.

Source format      | ecitmatch format
:----------------- | :---------------
Takahashi, K.      | `takahashi k`
John A. Smith      | `smith j`
María García-López | `garcia-lopez m`
van der Berg, P.J. | `van der berg p`

Only provide the **first author**. ecitmatch ignores additional authors.

--------------------------------------------------------------------------------

## 5. Batching Multiple Citations

Pass multiple citations as a comma-separated list to `match_raw_citations`:

```bash
uv run scripts/pubmed_api.py /tmp/pubmed_results.json match_raw_citations \
  "nature|2006||||takahashi k|ref1|,cell|2020|183||doe j|ref2|"
```

The response returns PMIDs for matched citations only. Unmatched citations are
silently dropped. Match the `key` field in the response to track which citations
resolved.

--------------------------------------------------------------------------------

## 6. When ecitmatch Fails

ecitmatch has a ~70-80% hit rate on well-formed citations and drops sharply with
messy input. When it returns empty:

### Fallback 1: Search PubMed directly

Construct a query from the citation fields:

```bash
uv run scripts/pubmed_api.py /tmp/pubmed_results.json search_pubmed \
  '"Takahashi" AND "2006" AND "Nature"' 5
```

### Fallback 2: Title search

If you have the paper title (even partial):

```bash
uv run scripts/pubmed_api.py /tmp/pubmed_results.json search_pubmed \
  '"Induction of Pluripotent Stem Cells"[ti]' 5
```

### Fallback 3: Strip fields and retry

Remove the least-reliable field and resubmit:

```bash
uv run scripts/pubmed_api.py /tmp/pubmed_results.json match_raw_citations \
  "nature|2006||||takahashi k|ref1|"
uv run scripts/pubmed_api.py /tmp/pubmed_results.json match_raw_citations \
  "nature|||||takahashi k|ref1|"
```

### Fallback 4: DOI or known identifier

If the source has a DOI, skip ecitmatch entirely:

```bash
uv run scripts/pubmed_api.py /tmp/pubmed_results.json search_pubmed \
  "10.1016/j.cell.2006.07.024[doi]" 1
```

--------------------------------------------------------------------------------

## 7. Common Failure Patterns

-   **Returns empty for a known paper** — Wrong journal abbreviation. Try full
    name or NLM abbreviation.
-   **Returns wrong PMID** — Author name mismatch. Check last-name + initial
    format.
-   **Returns empty for recent paper** — Not yet indexed by ecitmatch. Use
    `search_pubmed` title search.
-   **Returns empty for old paper (pre-1966)** — Pre-MEDLINE era. These papers
    may lack structured metadata.
-   **Multiple citations, partial hits** — One citation has bad data. Check
    returned keys to isolate the miss.
