---
name: clinvar-database
description: >
  Use when needing clinical significance, pathogenicity classifications (e.g.,
  Pathogenic, Benign, VUS), clinical evidence rationales, or finding "hard
  positive" benchmark controls for human genomic variants.
---

# ClinVar Database

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/clinvar_database_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at https://www.ncbi.nlm.nih.gov/clinvar/, then
    (2) create the file recording the notification text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`NCBI_API_KEY`** (optional): Raises the NCBI rate limit from 3 to 10
    requests/second. The skill works without it, but a key is recommended if the
    user plans many queries or encounters a 429 error. You can register for a
    key for free at https://www.ncbi.nlm.nih.gov/account/settings/. You **MUST**
    use the safe credentials protocol in the `credentials` skill to check for
    and request this key if this skill looks relevant to the user's request.

## Overview

ClinVar is the primary consensus record for clinical classifications of human
genomic variations. It provides the "clinical ground truth" for pathogenicity
labels (Pathogenic, Likely Pathogenic, Benign, VUS) based on assertions from
global laboratories.

## When to Use

**Use when you need to:**

-   Find the current clinical significance and star rating (review status) for a
    specific variant.
-   Fetch clinician notes, assertion criteria, or rationales for previous
    clinical laboratory classifications.
-   Retrieve the preferred condition name and associated HPO terms for a
    specific variant.
-   Find a list of variant controls (e.g., "Find all Pathogenic variants in the
    HBB gene within 50bp of a signal").
-   Check for conflicting interpretations for a given variant and identify the
    organizations submitting each classification.

**Do NOT use when you need to:**

-   Find specific allele frequencies in global populations (use **gnomAD**).
-   Describe the normal biological role of a protein and typical inheritance
    patterns (use **OMIM**).
-   Predict mechanistic effects of novel mutations, like frameshifts or exon
    skipping (use **AlphaGenome**).
-   Find recommended surveillance schedules for patients with a pathogenic
    variant (use **GeneReviews**).
-   Generate or view 3D structural models of affected proteins (use **PDB /
    AlphaFold**).

## Quick Start

ClinVar queries are executed via a robust Python wrapper script to handle strict
rate limiting and XML/JSON parsing.

Example: Search for BRCA1 variants

```bash
uv run scripts/clinvar_api.py search --query "BRCA1[gene]" --output results.json
```

## Core Rules

-   **Retmax Constraint**: The search command defaults to `--retmax 200`. For
    any "List all" or gene-wide request, you MUST explicitly set `--retmax`
    higher (e.g., 1000) to ensure data completeness.
-   **Use the Wrapper**: Prefer the wrapper script for standard queries. It
    handles rate limiting, retries, and the complex XML parsing for you. If the
    script's parsed output does not contain the specific fields you need, you
    may modify the script or query the NCBI E-utilities API directly — but be
    aware that the raw XML schemas are complex and vary between record types.
-   If the rate limit is hit, the script will throw a clear error. You **MUST**
    use the safe credentials protocol in the `credentials` skill to check for
    and request the `NCBI_API_KEY` to help the user add it to their `.env` file.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Utility Scripts

### 1. `count` — Count Matching Variants

**Purpose:** Check how many variants match a query without fetching IDs. Use to
decide whether a full `search` is warranted.

*Arguments:*

-   `--query`: (Required) NCBI Entrez search query string.
-   `--output`: (Required) Output JSON file path.

*Example:* `uv run scripts/clinvar_api.py count \ --query "TP53[gene] AND
\"uncertain significance\"[clinsig]" \ --output count.json` *Output:*
`{"total_count": <int>}`

### 2. `search` — Search Variants

**Purpose:** Identify variants based on genomic location, gene symbols, or
clinical attributes using NCBI Entrez search syntax. The search command
**automatically paginates** through all matching results to ensure complete,
deterministic retrieval.

```bash
# Fetch ALL matching variants (default behavior)
uv run scripts/clinvar_api.py search \
  --query "BRCA1[gene]" --output results.json

# Search by Chromosome and Position Range
uv run scripts/clinvar_api.py search \
  --query "11[chr] AND 5225000:5226000[chrpos]" --output results.json

# Combine terms using Entrez syntax
uv run scripts/clinvar_api.py search \
  --query "HBB[gene] AND pathogenic[clinsig]" --output results.json

# Cap results at 50
uv run scripts/clinvar_api.py search \
  --query "TP53[gene]" --retmax 50 --output results.json
```

*Arguments:*

-   `--query`: (Required) NCBI Entrez search query string.
-   `--retmax`: Maximum total number of variant IDs to return. **Default is 0,
    which means "fetch all matching results."** Set to a positive integer to cap
    the result set.
-   `--page_size`: Number of IDs to fetch per API request (default: 500, max:
    10000 per NCBI limits).
-   `--output`: (Required) Output JSON file path.

*Output:* A JSON object containing:

-   `total_count` — Total number of matching variants in ClinVar.
-   `fetched_count` — Number of IDs actually retrieved.
-   `variant_ids` — List of ClinVar Variation ID strings.

### 3. `summary` — Get Interpretation Summary

**Purpose:** Retrieve top-line clinical significance labels, star ratings
(review status), and basic phenotype data for rapid variant screening.

```bash
# Get summary for one or more Variation IDs
uv run scripts/clinvar_api.py summary \
  --variant_ids 12345 67890 --output summary.json
```

*Arguments:*

-   `--variant_ids`: (Required) One or more ClinVar Variation IDs.
-   `--output`: (Required) Output JSON file path.

*Output:* A JSON list of summary objects, each containing:

-   `variant_id`, `title`, `clinical_significance`, `review_status`, \
    `last_evaluated`, `phenotypes`
-   `genes` — list of `{gene_id, symbol, strand}`
-   `variation_type` — e.g., single nucleotide variant, Deletion, Insertion
-   `molecular_consequences` — list of strings (e.g., ["missense variant", \
    "nonsense"])

### 4. `evidence` — Get Clinical Evidence

**Purpose:** Fetch the full clinical record for a single variant, including
free-text clinician rationales, assertion methods, and specific submitter notes.

```bash
# Get full evidence for a single Variation ID
uv run scripts/clinvar_api.py evidence \
  --variant_id 12345 --output evidence.json
```

*Arguments:*

-   `--variant_id`: (Required) A single ClinVar Variation ID.
-   `--output`: (Required) Output JSON file path.

*Output:* A JSON object containing:

-   `variant_id`
-   `allele_info` — `{chromosome, position_start, position_stop,
    reference_allele, alternate_allele, cytogenetic_band, dbsnp_rsid}` (GRCh38
    preferred)
-   `conditions` — list of `{name, medgen_cui, omim_id, orphanet_id, hpo_terms}`
-   `functional_consequences` — list of `{value, sequence_ontology_id}`
-   `structural_variant_details` — `{outer_start, inner_start, inner_stop,
    outer_stop, copy_number}` (present only for CNVs, otherwise null)
-   `citation_references` — list of PubMed IDs cited in the global "Citations"
    section
-   `submissions` — list of per-submitter records, each containing:
    -   `submitter_name`, `classification`, `curator_notes`,
        `assertion_criteria`
    -   `date_last_evaluated` — when the submitter last reviewed the
        classification

## Typical Workflows

### Count-First Workflow (Recommended)

For large or unknown result sets, use `count` first to decide whether to
proceed, then `search` (which auto-paginates and returns `total_count` /
`fetched_count`), then `summary` to screen.

```bash
# Step 1: Gauge size (optional — search also returns total_count)
uv run scripts/clinvar_api.py count \
  --query "HBB[gene] AND pathogenic[clinsig]" --output count.json

# Step 2: Fetch all variant IDs (auto-paginates)
uv run scripts/clinvar_api.py search \
  --query "HBB[gene] AND pathogenic[clinsig]" --output ids.json

# Step 3: Get summaries (extract variant_ids from search output)
uv run scripts/clinvar_api.py summary \
  --variant_ids 12345 67890 --output summary.json
```

### Deep Dive: search → evidence

When you need the full clinical picture for a specific variant — including
submitter rationales, PubMed citations, ontology-linked conditions, and allele
coordinates — use `evidence`.

```bash
uv run scripts/clinvar_api.py evidence \
  --variant_id 12345 --output evidence.json
```

### Workflow: Robust Variant Discovery (Triangulation)

ClinVar metadata is inconsistent. To fulfill "List all" requests, do not rely on
a single filter. Perform the following in a single turn and merge results:

1.  **Search by exact label** (e.g., `"3 prime UTR
    variant"[molecular_consequence]`).
2.  **Search by HGVS nomenclature pattern** (e.g., `c.*`).
3.  **Search by genomic coordinate range** (using `[chrpos]`).

This "triangulation" ensures structural variants with missing labels are not
overlooked.

### Verifying Coding vs. Non-Coding Status via HGVS

`molecular_consequences` alone can be ambiguous (e.g., `splice donor variant`
appears in both coding and non-coding contexts). Always cross-check the `title`
field for HGVS patterns:

-   `c.-…` — 5' UTR (non-coding)
-   `c.*…` — 3' UTR (non-coding)
-   `c.123+N` / `c.123-N` — intronic (non-coding)
-   `p.Trp146Arg` etc. — protein effect (coding)

A variant with UTR/intronic HGVS and no `p.` annotation is non-coding, even with
splicing labels. Conversely, any `p.` annotation indicates a coding effect.

### ClinVar Metadata Reference

-   **3' UTR**
    -   Search String: `"3 prime UTR variant"[mol_consequence]`
    -   HGVS: `c.*`
-   **5' UTR**
    -   Search String: `"5 prime UTR variant"[mol_consequence]`
    -   HGVS: `c.-`
-   To find "high-confidence" variants or expert-reviewed consensus, use the
    `review_status` filter. This is the most efficient way to distinguish
    between single-laboratory assertions and panel-reviewed ground truth.

### When to Use Which Fields

-   **Quick pathogenicity label** — Use `summary` → `clinical_significance`
-   **Gene symbol and strand** — Use `summary` → `genes`
-   **Variant type (SNV, del, etc.)** — Use `summary` → `variation_type`
-   **Protein-level effect** — Use `summary` → `molecular_consequences`
-   **Genomic coordinates (GRCh38)** — Use `evidence` → `allele_info`
-   **Linked conditions (ontology)** — Use `evidence` → `conditions`
-   **SO functional consequence** — Use `evidence` → `functional_consequences`
-   **CNV breakpoints/copy number** — Use `evidence` →
    `structural_variant_details`
-   **PubMed references** — Use `evidence` → `citation_references`
-   **Date of last lab review** — Use both → `last_evaluated`
-   **Clinician rationales** — Use `evidence` → `submissions[].curator_notes`

### Retrieving Genomic Coordinates (Default HG38/GRCh38)

To get precise genomic coordinates in the format `<chrom>:<pos>:<ref>><alt>`
(e.g., `chr5:70951945:G>A`), you must use the `evidence` command, as these
details are not available in the `summary` output.

**You MUST always include genomic coordinates in the format
`<chrom>:<pos>:<ref>><alt>` when listing or presenting variants, even if not
explicitly requested by the user. If coordinates are missing from the summary,
use the `evidence` command or dbSNP fallback to retrieve them.**

1.  **Fetch Evidence**: Use `uv run scripts/clinvar_api.py evidence --variant_id
    <ID> --output evidence.json`.
2.  **Extract VCF Attributes**: The `evidence` command parses the XML. Extract:
    *   Chromosome: `Chr`
    *   Position: `positionVCF` (or `start`)
    *   Ref: `referenceAlleleVCF` (or `referenceAllele`)
    *   Alt: `alternateAlleleVCF` (or `alternateAllele`) from the
        `SequenceLocation` element with `Assembly="GRCh38"`.

**Fallback for Imprecise Coordinates (Gene Range):** ClinVar often returns the
full gene range for non-coding variants. If the extracted coordinates correspond
to the gene range instead of a specific position, use the `dbsnp-database` skill
to resolve the precise coordinates using the `dbsnp_rsid` or HGVS title: 1.Check
for `dbsnp_rsid` in the `evidence` output. 2. Run `uv run scripts/dbsnp_cli.py
resolve-rsid {rsid}` to get precise GRCh38 coordinates. 3. Format as
`<chrom>:<pos>:<ref>><alt>` using the SPDI or HGVS data from dbSNP.

### Structural Variant Note

The `structural_variant_details` field is **only populated for copy number
variants (CNVs)**. For standard SNVs and small indels this field will be `null`.
Use the `allele_info` fields (`position_start`, `position_stop`,
`reference_allele`, `alternate_allele`) instead.

### CNV / Large Deletion Note

Large copy-number variants (CNVs) frequently have empty
`molecular_consequences`. If a variant title mentions "del" and coordinates
overlap your target region, it is relevant regardless of missing labels.

### Obtaining and Using an API Key

You can register for a key for free at
https://www.ncbi.nlm.nih.gov/account/settings/. You **MUST** use the safe
credentials protocol in the `credentials` skill to check for and request this
key if this skill looks relevant to the user's request.

## Best Practices

-   Always use `uv run` to execute `python`.
-   If `jq` is unavailable pivot immediately to using Python one-liners for
    processing JSON (e.g., `uv run python3 -c "import json; ..."`).
-   Use `count` before `search` to understand the result set size.
-   The `search` command fetches all results by default and includes
    `total_count` and `fetched_count` in the output — always verify these match
    to confirm complete retrieval.
-   Entrez results are **unsorted**. To order by date, fetch all results and
    sort locally by `last_evaluated`.

## Common Mistakes

-   **Attempting to parse the E-utilities XML yourself** — Always use the
    provided `clinvar_api.py` client which handles the unpredictable XML schemas
    robustly.
-   **Getting HTTP 429 Too Many Requests** — The client throws an exception
    telling you to pause. You **MUST** use the safe credentials protocol in the
    `credentials` skill to check for and request the `NCBI_API_KEY` to help the
    user add it to their `.env` file, then retry.
-   **Sending raw DNA sequences to the API** — The API expects HGVS
    nomenclature, RS IDs, or proper Entrez coordinate syntax (`11[chr] AND
    1234[chrpos]`), not raw ATCG strings.
-   **For synonymous or non-coding variants** — HGVS nomenclature (e.g., CAPN3
    AND "c.551C>T") is more reliable than coordinate searches ([chrpos]), as
    many ClinVar records for these types lack precise genomic mappings.
-   **Case sensitivity in molecular consequences** — ClinVar returns mixed-case
    strings. Always use case-insensitive matching (`.lower()`) when filtering.
-   **Parsing `search` output as a bare list** — `search` returns a JSON object
    with `total_count`, `fetched_count`, and `variant_ids` — not a bare list.
