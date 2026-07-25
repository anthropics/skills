---
name: dbsnp-database
description: >
  Use when you want to look up, map, and search for short genetic variants
  (SNPs, indels) in NCBI's dbSNP database. Resolves between rsIDs, genomic
  coordinates in VCF format, and HGVS strings. For an rsID, returns variant
  type, gene associations, clinical significance, allele frequencies, and
  genomic coordinates (GRCh38).
---

# dbSNP Database Integration

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/dbsnp_database_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at https://www.ncbi.nlm.nih.gov/snp/, then (2)
    create the file recording the notification text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`NCBI_API_KEY`** (optional): Raises the NCBI rate limit from 3 to 10
    requests/second. The skill works without it, but a key is recommended if the
    user plans many queries or encounters a 429 error. You can register for a
    key for free at https://www.ncbi.nlm.nih.gov/account/settings/. You **MUST**
    use the safe credentials protocol in the `credentials` skill to check for
    and request this key if this skill looks relevant to the user's request.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided wrapper script
    `scripts/dbsnp_cli.py` to query the database rather than constructing custom
    HTTP or curl requests. The script automatically handles rate limiting,
    retries, and JSON parsing.
-   **Command Choice**: Do NOT use `search-region` to find the rsID of a
    specific variant; use `resolve-variant` instead.
-   **Output Size**: Avoid using `--full` on `get-variant` unless specifically
    needed, as raw payloads can exceed 1 MB.
-   **Shell Safety**: Always wrap HGVS strings in single quotes to prevent shell
    expansion errors.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## When to Use

**Use this skill when you need to:**

-   Map a genomic variant to its canonical rsID (from VCF coordinates or HGVS
    notation).
-   Retrieve summary data for an rsID: variant type, gene associations, clinical
    significance, and population allele frequencies.
-   Convert an rsID back to genomic coordinates on a specific assembly.
-   Find all known variants within a chromosomal region.

**Do NOT use when you need to:**

-   Obtain clinical pathogenicity classifications with submitter rationales (use
    **clinvar-database**).
-   Get precise population-level allele frequencies stratified by ancestry (use
    **gnomad-database**).
-   Predict the functional effect of a novel mutation (use
    **alphagenome-single-variant-analysis**).
-   View 3D protein structures affected by a variant (use
    **alphafold-database-fetch-and-analyze / pdb-database**).

## Command Selection Guide

**Pick the right command on the first try.** Match the user's input to the
correct subcommand below — one command call is almost always sufficient.

-   User gives you…: Run this command
-   An rsID (e.g. `rs7412`, `rs268`): `get-variant`
-   Genomic coordinates: chrom pos ref alt (e.g. `8 19962213 C T`):
    `resolve-variant`
-   An HGVS string (e.g. `NC_000008.11:g.19962213del`): `resolve-hgvs`
-   An rsID and they want coordinates back: `resolve-rsid`
-   A chromosomal region (chrom start end): `search-region`

> [!CAUTION] **Do NOT use `search-region` to find the rsID of a specific
> variant.** If the user provides a chromosome, position, reference allele, and
> alternate allele (four values), use `resolve-variant` — it is a direct,
> single-API-call lookup. `search-region` is only for surveying all variants
> within a positional range and returns hundreds/thousands of results.

## Quick Start

```bash
# Look up variant rs7412: type, gene, clinical significance, MAF
uv run scripts/dbsnp_cli.py get-variant rs7412 --output /tmp/rs7412.json

# Find the rsID for a variant at chr8:19962213 C>T
uv run scripts/dbsnp_cli.py resolve-variant 8 19962213 C T \
  --output /tmp/resolve.json
```

All subcommands write JSON to disk. Always save output in the `/tmp/` directory.
The `--output` flag is required.

## Commands

### 1. `get-variant` — Fetch Variant Record

Retrieve the RefSNP record for one rsID. By default the output is abbreviated to
the most useful fields. Both `rs268` and `268` are accepted.

```bash
uv run scripts/dbsnp_cli.py get-variant rs268 --output /tmp/rs268.json
uv run scripts/dbsnp_cli.py get-variant 268 --assembly GCF_000001405.40 \
  --output /tmp/rs268.json
```

*Arguments:*

-   `rsid` (positional, required): The RefSNP identifier.
-   `--assembly`: RefSeq assembly accession (default: `GCF_000001405.40` =
    GRCh38).
-   `--full`: Return the complete raw JSON payload — see warning below.
-   `--output`: Output file path (default: `/tmp/dbsnp_output.json`).

*Abbreviated output fields:*

-   `refsnp_id`: Numeric rsID
-   `variant_type`: e.g. `snv`, `ins`, `del`, `delins`
-   `genes`: Sorted list of gene symbols (locus names)
-   `clinical_significances`: List of clinical significance labels
-   `minor_allele_frequencies`: Study name, allele count, total count
-   `placements`: Genomic placements for the requested assembly

> [!WARNING] **About `--full`:** The raw RefSNP payload is typically 50–500 KB
> and can exceed 1 MB for clinically significant variants with many submissions.
> Only use `--full` when you specifically need data absent from the abbreviated
> output — for example:
>
> -   The complete HGVS nomenclature across every transcript and protein
>     isoform.
> -   Full submission history with individual submitter details and timestamps.
> -   Population-level allele frequency breakdowns by sub-population within a
>     study (e.g. per-population gnomAD counts).
> -   The full set of genomic placements across multiple assemblies (GRCh37 and
>     GRCh38 simultaneously).
> -   Merge history showing which older rsIDs were merged into this one.

### 2. `resolve-variant` — Genomic Coordinates → rsID

Determine the rsID(s) for a variant given its genomic coordinates (chromosome,
position, reference allele, alternate allele). **This is the command to use when
the user provides a variant as space-separated coordinates** like `8 19962213 C
T`.

```bash
uv run scripts/dbsnp_cli.py resolve-variant 8 19962213 C T \
  --output /tmp/resolve.json
```

*Arguments:*

-   `chrom` (positional): Chromosome number (e.g. `8`) or RefSeq sequence
    accession (e.g. `NC_000008.11`). **Chromosomes X and Y must be passed as
    their numeric equivalents: `23` for X and `24` for Y.**
-   `pos` (positional): 1-based genomic position.
-   `ref` (positional): Reference allele (e.g. `C`).
-   `alts` (positional): Alternate allele(s), comma-separated (e.g. `T`).
-   `--assembly`: RefSeq assembly accession (default: `GCF_000001405.40`).
-   `--output`: Output file path (default: `/tmp/dbsnp_output.json`).

*Output:* `{"rsids": ["12345", "67890"]}`

### 3. `resolve-rsid` — rsID → Genomic Coordinates

Get the genomic placement (sequence ID and allele details) for a known rsID on a
specific assembly.

```bash
uv run scripts/dbsnp_cli.py resolve-rsid rs7412 --output /tmp/coords.json
```

*Arguments:*

-   `rsid` (positional): The RefSNP identifier.
-   `--assembly`: RefSeq assembly accession (default: `GCF_000001405.40`).
-   `--output`: Output file path (default: `/tmp/dbsnp_output.json`).

*Output:* `{"rsid": "7412", "assembly": "...", "placements": [...]}`

### 4. `resolve-hgvs` — HGVS → rsID

Find the rsID(s) corresponding to an HGVS expression.

```bash
uv run scripts/dbsnp_cli.py resolve-hgvs 'NC_000008.11:g.19962213del' \
  --output /tmp/hgvs.json
```

*Arguments:*

-   `hgvs` (positional): The HGVS string.
-   `--assembly`: RefSeq assembly accession (default: `GCF_000001405.40`).
-   `--output`: Output file path (default: `/tmp/dbsnp_output.json`).

*Output:* `{"rsids": ["12345"]}`

> [!TIP] HGVS strings often contain characters that shells interpret (colons,
> greater-than signs). Always wrap them in **single quotes** to prevent shell
> expansion.

### 5. `search-region` — Regional Variant Search

Find all rsIDs within a bounded chromosomal region.

```bash
uv run scripts/dbsnp_cli.py search-region 7 117100000 117300000 \
  --output /tmp/region.json
```

*Arguments:*

-   `chrom` (positional): Chromosome (e.g. `7`). **Use `23` for chromosome X and
    `24` for chromosome Y.**
-   `start` (positional): Start position.
-   `end` (positional): End position.
-   `--retmax`: Maximum rsIDs to return (default: 500, ceiling: 5 000).
-   `--output`: Output file path (default: `/tmp/dbsnp_output.json`).

*Output:*

```json
{
  "rsids": ["12345", "67890", "..."],
  "returned": 500,
  "total_available": 1423,
  "truncated": true,
  "note": "Only 500 of 1423 variants returned.  Increase --retmax ..."
}
```

When `total_available` exceeds the returned count, the output includes a
`truncated` flag and a `note`. Increase `--retmax` to retrieve more (up to 5
000).

## Typical Workflows

### Identify a known variant from coordinates

```bash
# Step 1: Map VCF coordinates to rsID
uv run scripts/dbsnp_cli.py resolve-variant 19 44908684 T C \
  --output /tmp/step1.json

# Step 2: Get the full details for the resolved rsID
uv run scripts/dbsnp_cli.py get-variant <rsid_from_step1> \
  --output /tmp/step2.json
```

### Survey variants in a gene region

```bash
# Step 1: Find all variants in a region spanning the CFTR gene
uv run scripts/dbsnp_cli.py search-region 7 117100000 117300000 \
  --retmax 1000 --output /tmp/region.json

# Step 2: Retrieve details on individual rsIDs of interest
uv run scripts/dbsnp_cli.py get-variant <rsid> --output /tmp/detail.json
```

### Translate HGVS notation to genomic coordinates

```bash
# Step 1: Get the rsID for an HGVS expression
uv run scripts/dbsnp_cli.py resolve-hgvs 'NC_000019.10:g.44908684T>C' \
  --output /tmp/hgvs.json

# Step 2: Resolve that rsID to VCF-style coordinates
uv run scripts/dbsnp_cli.py resolve-rsid <rsid> --output /tmp/coords.json
```

## Assembly Defaults and Automatic Fallback

The Variation Services endpoints (used by `get-variant`, `resolve-variant`,
`resolve-rsid`, `resolve-hgvs`) expect a **RefSeq assembly accession**. The
RefSeq accession for GRCh38 is `GCF_000001405.40`, and for GRCh37 it is
`GCF_000001405.25`.

The `search-region` subcommand always searches GRCh38 positions.

> [!IMPORTANT] **Automatic assembly fallback:** The `resolve-variant` and
> `resolve-hgvs` commands automatically try GRCh38 first. If no rsIDs are found,
> they retry with GRCh37 before reporting failure. When a fallback occurs the
> output JSON includes a `"note"` field explaining which assembly succeeded.
> **You do NOT need to manually retry with a different assembly** — the script
> handles this transparently.

You only need to override `--assembly` when you specifically want to
**restrict** the lookup to one assembly (e.g. because the user's coordinates are
known to be GRCh37).

## NCBI API Key and Rate Limiting

Without an API key the script is limited to **3 requests per second**. With a
key this increases to **10 requests per second**.

You can register for a key for free at
https://www.ncbi.nlm.nih.gov/account/settings/. You **MUST** use the safe
credentials protocol in the `credentials` skill to check for and request this
key if this skill looks relevant to the user's request.

## Troubleshooting HTTP 500 Errors

### Reference Allele Mismatch

If you receive an HTTP 500 error with a message detailing that the asserted
reference allele is not equal to the reference sequence:

**What it means:** The coordinate position is likely valid, but the reference
allele (`ref`) you provided does not match the base at that position in the
requested assembly.

**Action:** 1. **DO NOT RETRY** the exact same query mechanically. 2. **Check
the assembly**: Coordinates are assembly-specific. 3. **Switch assembly**: If
you were querying GRCh37, try GRCh38 (using `--assembly GCF_000001405.40`), or
if querying GRCh38, try GRCh37 (using `--assembly GCF_000001405.25`).

## Common Mistakes

-   **Mistake:** Forgetting to quote HGVS strings **Fix:** Wrap in single
    quotes: `'NC_000008.11:g.19962213del'`

-   **Mistake:** Passing a chromosome name to `resolve-variant` instead of a
    sequence accession **Fix:** Use the numeric chromosome ID (e.g. `8`) or a
    RefSeq accession like `NC_000008.11`

-   **Mistake:** Using `--full` on `get-variant` without needing it **Fix:** The
    abbreviated output covers most use cases; `--full` returns 50–500 KB+ of
    JSON

-   **Mistake:** Expecting `search-region` to return all results by default
    **Fix:** The default `--retmax` is 500; check `total_available` in the
    output to see if results were truncated

-   **Mistake:** Using GRCh37 coordinates with `search-region` **Fix:**
    `search-region` always uses GRCh38 positions; lift over coordinates first if
    starting from GRCh37

-   **Mistake:** Manually retrying `resolve-variant` or `resolve-hgvs` with a
    different `--assembly` when the first call fails **Fix:** The script
    automatically tries GRCh38 then GRCh37; a single call is sufficient

-   **Mistake:** Passing `X` or `Y` as the chromosome value **Fix:** Use the
    numeric equivalents: `23` for chromosome X and `24` for chromosome Y. The
    CLI treats chromosomes numerically by default.
