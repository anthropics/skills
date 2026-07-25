---
name: opentargets-database
description: >
  Query Open Targets Platform for target-disease associations, drug target
  discovery, tractability/safety data, genetics/omics evidence, known drugs,
  for therapeutic target identification.
---

# Open Targets Database Skill

## Overview

This skill provides access to the Open Targets Platform GraphQL API. It
aggregates multi-modal evidence from genetics (GWAS/eQTL), pathways, animal
models, and clinical trials to rank target-disease associations and identify
druggable genes.

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/opentargets_database_LICENSE.txt does
    not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at
    https://platform-docs.opentargets.org/licence, then (2) create the file
    recording the notification text and timestamp.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce fair use and implement retry logic.
-   **Output Flag**: The `--output` flag is always required as output can be
    very large. Use `jq` or write your own code to process this JSON file.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Quick Reference

Always use the provided Python script `scripts/query_opentargets.py` to quickly
query the database. It handles API communication, retries, formatting, and
automatically truncates overly large responses. NEVER write your own curl or
similar requests.

**Usage:**

```bash
uv run scripts/query_opentargets.py --output /tmp/opentargets_results.json [OPTIONS] COMMAND [ARGS]...
```

**Common Options:**

-   `--output PATH`: **Required**. Path to write the JSON output file.
-   `--limit N`: Limit the number of items returned in arrays (default is 50).
    Use a smaller number like 10 when doing preliminary exploration.
-   `--page-size N`: Set the API pagination size (default is 200). Increase if
    you need more results (e.g., a study with many credible sets).

**Available Commands:**

-   **`get-gwas-studies`** *`disease_id`*: Fetches all GWAS studies associated
    with a specific disease ID (e.g. `MONDO_0008383` for Rheumatoid Arthritis).
-   **`get-study-credible-sets`** *`study_id`*: Fetches all credible sets for a
    given study ID (e.g. `FINNGEN_R12_RX_CROHN_2NDLINE`). Returns confidence,
    finemapping method, variant, and p-value info.
-   **`get-qtl-credible-sets`** *`variant_id`*: Retrieves QTL credible sets for
    a specific variant ID (e.g. `19_44908822_C_T`).
-   **`get-l2g`** *`variant_id [--study-id ID]`*: Returns Locus-to-Gene (L2G)
    predictions/scores for a locus to identify the most likely causal gene. Only
    `variant_id` is required; use `--study-id` to filter to a specific study.
    Accepts `chr` prefix (e.g. `chr1_113834946_A_G`).
-   **`get-target-druggability`** *`ensembl_id`*: Provides tractability data
    (small molecule, antibody, etc.) and clinical trial safety info for a
    gene/target.
-   **`get-associated-targets`** *`disease_id`*: Find all target genes
    associated with a specific disease ID (EFO or MONDO).
-   **`get-disease-drugs`** *`disease_id [--min-stage STAGE]`*: Find all drugs
    and clinical candidates associated with a disease. Use `--min-stage` to
    filter (e.g., `PHASE_3` for Phase III or Approved).
-   **`get-associated-diseases`** *`ensembl_id`*: Find all diseases associated
    with a specific target Ensembl ID.
-   **`search-disease`** *`query_string`*: Search for a disease by name to find
    its ID and other metadata.
-   **`get-credible-sets-near-target`** *`ensembl_id [--window N]`*: Fetches
    credible sets for a target and filters them to those within a genomic window
    around the target. Useful for finding variants "nearby" a gene.
-   **`custom-query`** *`query [--variables '{}']`*: Run a raw GraphQL query for
    any other Open Targets data.

## L2G Query Usage

The `get-l2g` command has two modes:

*   **Variant only** (`get-l2g <variant_id>`): Returns L2G predictions from
    **all credible sets across all studies** where that variant is the lead
    variant. This can return a large number of results (e.g., hundreds). Use
    this when the user wants a broad view of which gene is most likely causal at
    a locus, or when no specific study is mentioned.
*   **Variant + study** (`get-l2g <variant_id> --study-id <study_id>`): Returns
    L2G predictions only for credible sets from that specific study. Use this
    when the user asks about a specific GWAS study or when you need to narrow
    down the results.

> **Incomplete results warning:** The variant-only mode can return hundreds of
> credible sets. The default `--page-size` is 200, so if the API reports a
> `count` higher than the number of `rows` returned, **you are seeing incomplete
> results**. Always compare `count` to the actual number of rows. If they
> differ, either increase `--page-size` or inform the user that only a subset
> was retrieved.

## Querying by Region

To find studies with variants "nearby" a gene, use
`get-credible-sets-near-target`, which improves upon the base API by performing
a flexible search based on genomic position: `uv run
scripts/query_opentargets.py --output /tmp/results.json
get-credible-sets-near-target ENSG00000156515 --window 500000`

Note that the Open Targets GraphQL schema includes a `regions` parameter for
`credibleSets`, however it performs an exact match against pre-computed region
strings (e.g., `chr10:68769984-69903496`) and there is some missing data. Use
get-credible-sets-near-target as it allows a genomic range overlap search.

This fetches credible sets associated with the target and filters them in Python
based on the variant's genomic position.

## Advanced GraphQL Queries

If you need to query endpoints or fields not exposed by the built-in
subcommands, use the `custom-query` subcommand.

**Before writing a custom query:** Read the reference documentation to
understand the API schema, types, and see example queries. See
[references/OpenTargets_GraphQL_Guide.md](references/OpenTargets_GraphQL_Guide)
for full schema details, endpoints, and examples.

**Example: Finding drugs for a disease**

```bash
uv run scripts/query_opentargets.py custom-query \
  query drugsForDisease($id: String!) {
    disease(efoId: $id) {
      name
      drugAndClinicalCandidates {
        count
        rows {
          maxClinicalStage
          drug {
            id
            name
          }
        }
      }
    }
  }' \
--variables '{"id": "EFO_1001006"}'
--output '/tmp/opentargets_result.json'
```

## Confidence Star Ratings

The Open Targets Platform assigns a **confidence level** to each credible set
based on the fine-mapping method and quality checks. These correspond to star
ratings displayed in the platform UI:

| Stars          | Confidence String (API value)                             |
| -------------- | --------------------------------------------------------- |
| ★★★★ (4 stars) | `SuSiE fine-mapped credible set with in-sample LD`        |
| ★★★ (3 stars)  | `SuSiE fine-mapped credible set with out-of-sample LD`    |
| ★★ (2 stars)   | `PICS fine-mapped credible set extracted from summary     |
:                : statistics`                                               :
| ★ (1 star)     | `PICS fine-mapped credible set based on reported top hit` |
| None           | `Unknown confidence`                                      |

When users ask about "N-star confidence", match their request to the
corresponding string in the `confidence` field of the API response.

## Tips and Common Mistakes

-   **ID Formats**:
    -   Disease IDs are typically MONDO IDs (e.g. `MONDO_0008383` for Rheumatoid
        Arthritis) or EFO IDs (e.g. `EFO_0009460`). Use the `search-disease`
        command to find the correct ID.
    -   Target IDs must be Ensembl IDs (e.g. `ENSG00000169083`), not HGNC
        symbols. If you only have a gene symbol, you may need to map it first
        using a custom GraphQL `search` query.
    -   Variant IDs are formatted as `chromosome_position_ref_alt` (e.g.,
        `1_154426264_C_T`). A `chr` prefix (e.g. `chr1_154426264_C_T`) is
        automatically stripped by the tool.
    -   Study IDs can be GWAS Catalog IDs (e.g. `GCST90204201`) or
        project-specific IDs (e.g. `FINNGEN_R12_RX_CROHN_2NDLINE`).
-   **Truncation**: The tool truncates arrays longer than `--limit` to protect
    the context window. If you see `"_truncated"`, you can run the query again
    with a higher limit if you specifically need more data, but be cautious with
    large limit values. Always use the `--output` flag to save the result to a
    file and avoid terminal output truncation.
-   **Pagination and incomplete results**: The `--page-size` option
    (default: 200) controls how many items are fetched from the API. **Always
    check the `count` field in the response and compare it to the number of
    `rows` actually returned.** If `count` > number of rows, you have incomplete
    data — either increase `--page-size` to fetch more, or inform the user that
    only a partial result set was returned. This is especially important for
    `get-l2g` without `--study-id`, which can return hundreds of credible sets.
