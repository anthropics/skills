---
name: human-protein-atlas-database
description: >
  Use when you want to retrieve semi-quantitative protein expression and
  spatial localisation data from the Human Protein Atlas (HPA).
---

# Human Protein Atlas (HPA) Database Integration

This skill provides semi-quantitative protein expression and spatial
localisation data from the Human Protein Atlas (HPA). While RNA-seq (e.g., GTEx)
tells us if a gene is being transcribed, HPA confirms if the protein product
actually exists, where it is located within the cell (e.g. nucleus vs
cytoplasm), and its concentration in systemic blood circulation. The data is
based on Immunohistochemistry (IHC) across normal human tissues and cancer
types.

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/human_protein_atlas_database_LICENSE.txt
    does not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at
    https://www.proteinatlas.org/about/licence, then (2) create the file
    recording the notification text and timestamp.

## When to Use

**Use this skill when you need to:**

-   Map a gene symbol to its Ensembl ID for HPA queries.
-   Retrieve the semi-quantitative protein abundance in normal human tissues and
    cancer types based on IHC staining (High, Medium, Low, or Not Detected).
-   Find the specific organelles or subcellular structures where a protein has
    been localized (e.g., nucleoplasm, mitochondria).
-   Check the consistency/agreement between RNA-seq consensus and protein
    expression levels.
-   Search for genes based on specific protein expression criteria (e.g.,
    "elevated in amygdala" or "secreted proteins").

**Do NOT use when you need to:**

-   Query eQTLs, pQTLs, or any variant-level associations. HPA provides
    wild-type expression data and knows nothing about QTLs.
-   Query gene expression in non-human species. HPA is strictly for human
    proteins.
-   Retrieve purely quantitative RNA expression without interest in the protein
    product (consider using the GTEx skill instead).

## Command Selection Guide

**Pick the right command on the first try.** Match the user's input to the
correct subcommand below.

-   Map a gene symbol to Ensembl ID: `resolve-ensembl-id`
-   Get tissue protein expression levels: `get-tissue-expression`
-   Get subcellular location of a protein: `get-subcellular-location`
-   Get the full HPA metadata entry for a gene: `get-atlas-entry`
-   Search HPA for genes matching specific criteria: `search-hpa`

## Quick Start

```bash
# Map the ERBB2 gene symbol to its Ensembl ID
uv run scripts/hpa_cli.py resolve-ensembl-id ERBB2 --output /tmp/erbb2_id.json

# Get subcellular location by Ensembl ID
uv run scripts/hpa_cli.py get-subcellular-location ENSG00000141736 --output /tmp/erbb2_location.json
```

All subcommands write JSON to disk. Always save output in the `/tmp/` directory.
The default output file is `/tmp/hpa_output.json` if `--output` is not
specified.

## Commands

### 1. `resolve-ensembl-id` — Gene Symbol → Ensembl ID

Maps a common gene symbol (e.g., "TP53", "ERBB2") to its Ensembl gene ID. HPA
endpoints are strictly Ensembl-based.

```bash
uv run scripts/hpa_cli.py resolve-ensembl-id TP53 --output /tmp/tp53_id.json
```

*Arguments:*

-   `gene_symbol` (positional): The standard gene symbol (e.g., "TP53").
-   `--output`: Output file path (default: `/tmp/hpa_output.json`).

### 2. `get-tissue-expression` — Get Tissue Protein Levels

Returns a list of tissues and their corresponding protein expression levels
(High, Medium, Low, or Not Detected) based on IHC staining.

```bash
uv run scripts/hpa_cli.py get-tissue-expression ENSG00000130234 \
  --tissues "duodenum,thyroid gland" --output /tmp/tissue_expr.json
```

*Arguments:*

-   `ensembl_id` (positional): The Ensembl Gene ID.
-   `--tissues`: Comma-separated list of tissues to filter by (optional,
    defaults to all available tissues).
-   `--output`: Output file path (default: `/tmp/hpa_output.json`).

### 3. `get-subcellular-location` — Get Subcellular Location

Retrieves the specific organelles or cellular structures where the protein has
been localized.

```bash
uv run scripts/hpa_cli.py get-subcellular-location ENSG00000141736 \
  --output /tmp/subcellular.json
```

*Arguments:*

-   `ensembl_id` (positional): The Ensembl Gene ID.
-   `--output`: Output file path.

### 4. `get-atlas-entry` — Get Full HPA Entry

Fetches the full metadata for a gene, including IHC scores, RNA-seq consensus,
and subcellular location.

```bash
uv run scripts/hpa_cli.py get-atlas-entry ENSG00000254647 \
  --output /tmp/ins_entry.json
```

*Arguments:*

-   `ensembl_id` (positional): The Ensembl Gene ID.
-   `--format`: Format of the returned entry, e.g., json (default: `json`).
-   `--output`: Output file path.

### 5. `search-hpa` — Search by Attribute

Allows filtering for genes based on specific criteria (e.g., "elevated in
amygdala").

```bash
uv run scripts/hpa_cli.py search-hpa \
  --query "brain_category_rna:amygdala" \
  --output /tmp/search_results.json
```

*Arguments:*

-   `--query`: The search query string. Refer to references/search-api.md for
    details.
-   `--output`: Output file path.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce fair use and implement retry logic.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## API Versioning

The HPA website at `www.proteinatlas.org` always serves the **latest** data
release. Older archived versions can be accessed via `vNN.proteinatlas.org`
(e.g., `v24.proteinatlas.org`), while the current version's subdomain redirects
to `www.proteinatlas.org`. This skill's scripts query the latest version by
default.

## Common Errors

-   If no results are returned, confirm the query is detailed enough starting
    with the api reference in references/search-api.md
-   If you cannot find the results, search the web for example HPA queries and
    use these to construct a better query.
-   The output is usually large. Use jq or write your own python data parsing
    library to process the search results. Never output to stdout, or cat the
    output file.
