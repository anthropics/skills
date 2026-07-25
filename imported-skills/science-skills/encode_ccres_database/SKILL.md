---
name: encode-ccres-database
description: >
    Query the ENCODE Registry of cis-Regulatory Elements (cCREs) via the SCREEN
    GraphQL API, or make custom queries to the ENCODE Portal REST API for
    experiments and files (ChIP-seq peaks, etc.). Use when you want to query
    regulatory annotations or raw experimental data across human cell types.
---

# ENCODE Database Skill

This skill allows you to query the ENCODE Registry of cCREs (candidate
cis-Regulatory Elements) via the SCREEN GraphQL API. It helps identify
functional non-coding DNA elements (like Promoters, Enhancers, and insulators)
by analyzing biochemical signatures (DNase, H3K4me3, H3K27ac, CTCF).

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/encode_ccres_database_LICENSE.txt does
    not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at
    https://www.encodeproject.org/help/rest-api/, then (2) create the file
    recording the notification text and timestamp.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   **Parsing Output**: Do NOT use `cat` to read the entire JSON output file
    into context, as it can be extremely large. You MUST use `jq` to efficiently
    parse and extract relevant fields.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

### Quick Start

```bash
# Search cCREs by coordinates
uv run scripts/screen_api.py search --chromosome chr11 \
  --start 5205263 --end 5207263 \
  --output /tmp/search.json

# Get details for a specific cCRE
uv run scripts/screen_api.py details EH38E2941922 \
  --output /tmp/details.json
```

All subcommands write JSON to disk. Always save output in a temporary location
like `/tmp/`.

### Identifying High-Confidence ("Type A") Biosamples

Biosamples in ENCODE are often categorized by their data completeness. **"Type
A"** (or high-confidence) biosamples are those that have experimental data for
all four core epigenetic markers: **DNase, H3K4me3, H3K27ac, and CTCF**.

The `biosamples` and `details` commands automatically enrich their output with
an `is_type_a` boolean flag for each biosample.

**Example: Finding high-confidence cell types**

```bash
uv run scripts/screen_api.py biosamples --output /tmp/biosamples.json
# Use jq to filter for Type A biosamples
jq '.data.ccREBiosampleQuery.biosamples[] | select(.is_type_a == true) | .displayname' /tmp/biosamples.json
```

### Parsing Output (CRITICAL)

**Do NOT use `cat` to read the entire JSON output file into context, as it**
**can be extremely large.** Instead, you MUST use `jq` to efficiently parse and
extract the relevant fields from the JSON file saved by the script. If `jq` is
not available on the system, write your own Python filtering code (e.g.,
`python3 -c "import json..."`) to extract the necessary data.

For a complete reference of the JSON structure returned by eachmcommand (so you
know which fields to query with `jq`), read
`references/json_output_structure.md`.

### Available Commands

-   `search`: Search cCREs by coordinates, accessions, or epigenetic signals.

    ```bash
    uv run scripts/screen_api.py search \
        --chromosome chr11 --start 5205263 --end 5207263 \
        --output /tmp/search.json
    ```

-   `nearby-genes`: Find nearby genes for given cCRE accessions.

    ```bash
    uv run scripts/screen_api.py nearby-genes \
        EH38E1516972 --output /tmp/nearby.json
    ```

-   `details`: Get detailed information and biosample-specific max Z-scores for
    a specific cCRE.

    ```bash
    uv run scripts/screen_api.py details EH38E2941922 \
        --output /tmp/details.json
    ```

-   `biosamples`: Get biosample metadata for an assembly.

    ```bash
    uv run scripts/screen_api.py biosamples \
        --output /tmp/biosamples.json
    ```

-   `orthologs`: Get orthologous cCREs in another assembly.

    ```bash
    uv run scripts/screen_api.py orthologs EH38E2941922 \
        --output /tmp/orthologs.json
    ```

-   `linked-genes`: Find linked genes via methods like HiC or eQTLs.

    ```bash
    uv run scripts/screen_api.py linked-genes \
        EH38E1516972 --output /tmp/linked.json
    ```

-   `gene-expression`: Get gene expression (TPM) across all biosamples for a
    named gene. Internally resolves the gene symbol to an Ensembl gene ID, then
    queries per-biosample RNA-seq quantifications.

    ```bash
    uv run scripts/screen_api.py gene-expression GAPDH \
        --output /tmp/gene_expr.json
    ```

-   `entex`: Get ENTEx data for a cCRE or genomic region.

    ```bash
    uv run scripts/screen_api.py entex \
        --accession EH38E1310345 \
        --output /tmp/entex.json
    ```

    ```bash
    uv run scripts/screen_api.py entex \
        --region chr1:1000068:1000409 \
        --output /tmp/entex.json
    ```

-   `gwas`: Query genome-wide association studies, SNPs, or enrichment data.

    ```bash
    uv run scripts/screen_api.py gwas studies \
        --output /tmp/gwas.json
    ```

    ```bash
    uv run scripts/screen_api.py gwas snps --study \
        Ahola-Olli_AV-27989323-Eotaxin_levels \
        --output /tmp/gwas_snps.json
    ```

You can supply the `--assembly mm10` or `--assembly grch38` flag to explicitly
request a specific assembly for most commands. By default, the script targets
`grch38` but will automatically fall back to `mm10` if no results are found or
if the query fails.

## ENCODE Portal REST API (Direct Access)

For accessing raw experiments, ChIP-seq peaks, or other datasets that are not
represented as cCREs in SCREEN, use the `scripts/encode_portal_api.py` script.
It allows custom queries to the ENCODE Portal REST API.

### Usage

```bash
uv run scripts/encode_portal_api.py search "type=Experiment&target.label=ZNF549" --output /tmp/znf549_experiments.json
```

### Data Analysis Tips

When analyzing `.bed` or `.bigBed` files downloaded from ENCODE, standard
bioinformatics tools are highly recommended for finding overlaps (e.g., between
gene promoters and peaks):

-   **`bedtools`**: For fast mathematical operations on genomic intervals.
-   **`bigBedToBed`**: For converting binary BigBed files to readable BED
    format.
-   **`pybedtools`**: A Python wrapper for `bedtools`.

Write custom logic if these tools are not pre-installed.

## Custom Queries (SCREEN GraphQL)

If you need to make a complex GraphQL query that the script does not support,
read `references/graphql_schema.md` for a reference of available queries,
arguments, and return fields in the SCREEN GraphQL API.
