# Open Targets GraphQL API Guide

## Overview

The Open Targets Platform GraphQL API provides access to aggregated multi-modal
evidence from genetics (GWAS/eQTL), pathways, animal models, and clinical
trials. This data is used to rank target-disease associations, identify
druggable genes, and discover known drugs.

## Querying the API

To interact with the Open Targets API, use the provided Python script
`scripts/query_opentargets.py`. This script handles API communication,
formatting, and automatically truncates large responses to save context window
tokens.

### Built-in Commands

For common tasks, use the specialized subcommands provided by the script:

-   `get-gwas-studies <disease_id>`: Fetch GWAS studies for a disease.
-   `get-study-credible-sets <study_id>`: Fetch 95% credible sets for a study.
-   `get-qtl-credible-sets <variant_id>`: Fetch QTL credible sets for a variant.
-   `get-l2g <variant_id> [--study-id <study_id>]`: Get Locus-to-Gene (L2G)
    predictions.
-   `get-target-druggability <ensembl_id>`: Get tractability and safety data for
    a target.
-   `get-associated-targets <disease_id>`: Find target genes associated with a
    disease.
-   `get-disease-drugs <disease_id> [--min-stage <stage>]`: Find drugs and
    clinical candidates associated with a disease, optionally filtering by
    minimum clinical stage (e.g., `PHASE_3`, `APPROVAL`).
-   `get-associated-diseases <ensembl_id>`: Find diseases associated with a
    target.
-   `search-disease <query_string>`: Search for a disease to find its ID.

**Global Options:**

-   `--limit N`: Limits the number of items returned in arrays (default: 50).
-   `--page-size N`: Sets API pagination size (default: 200).

### Custom GraphQL Queries

For complex queries or fields not covered by the built-in commands, use the
`custom-query` subcommand:

```bash
uv run scripts/query_opentargets.py custom-query \
  'query targetInfo($id: String!) {
    target(ensemblId: $id) {
      approvedSymbol
      biotype
    }
  }' \
  --variables '{"id": "ENSG00000169083"}'
```

## Core Entities & Identifiers

When writing custom GraphQL queries, you will primarily interact with the
following core entities defined in the schema:

### 1. Target (Gene/Protein)

-   **Identifier:** Ensembl ID (e.g., `ENSG00000169083`). **Do not use HGNC
    symbols directly**; you must map them to Ensembl IDs first.
-   **Root Queries:** `target(ensemblId: String!)`, `targets(ensemblIds:
    [String!]!)`
-   **Key Fields:**
    -   `id`: Ensembl ID.
    -   `approvedSymbol`, `approvedName`: Standard HGNC symbol and name.
    -   `biotype`: Type of gene (e.g., protein_coding).
    -   `associatedDiseases(...)`: Target-disease associations with scores.
    -   `knownDrugs(...)`: Approved/investigational drugs targeting this gene.
    -   `tractability`: Feasibility of targeting with therapeutic modalities.

### 2. Disease (or Phenotype)

-   **Identifier:** Disease ID, typically MONDO ID (e.g., `MONDO_0008383` for
    Rheumatoid Arthritis) or EFO ID (e.g., `EFO_0009460`).
-   **Root Queries:** `disease(efoId: String!)` (accepts MONDO/EFO IDs),
    `diseases(efoIds: [String!]!)`
-   **Key Fields:**
    -   `id`: Disease ID.
    -   `name`, `description`: Disease name and summary.
    -   `synonyms`: Alternative names.
    -   `associatedTargets(...)`: Targets associated with this disease, sortable
        by score.
    -   `knownDrugs(...)`: Drugs indicated for this disease or currently in
        clinical trials.
    -   `evidences(...)`: Specific pieces of evidence supporting target-disease
        associations.

### 3. Drug (or Clinical Candidate)

-   **Identifier:** ChEMBL ID (e.g., `CHEMBL112`).
-   **Root Queries:** `drug(chemblId: String!)`, `drugs(chemblIds: [String!]!)`
-   **Key Fields:**
    -   `id`: ChEMBL ID.
    -   `name`, `drugType`: Generic name and molecule type.
    -   `maximumClinicalStage`: Highest clinical stage reached (values are
        enums, e.g., "APPROVAL", "PHASE_3", "PHASE_2", "PHASE_1", "PHASE_0").
    -   `mechanismsOfAction`: How the drug interacts with its target.
    -   `indications`: Diseases the drug is indicated for.
    -   `adverseEvents(...)`: Significant adverse events from FAERS.

### 4. Variant

-   **Identifier:** Format `CHROM_POS_REF_ALT` (e.g., `1_154426264_C_T`). Note:
    A `chr` prefix is automatically stripped by the CLI tool, but standard
    queries expect it without the prefix.
-   **Root Query:** `variant(variantId: String!)`
-   **Key Fields:**
    -   `id`: Variant ID.
    -   `chromosome`, `position`, `referenceAllele`, `alternateAllele`: Genomic
        coordinates.
    -   `rsIds`: dbSNP identifiers.
    -   `credibleSets(...)`: GWAS/molQTL credible sets containing this variant.

### 5. Study (GWAS/molQTL)

-   **Identifier:** Study ID (e.g., GWAS Catalog ID `GCST90204201` or project
    ID).
-   **Root Query:** `study(studyId: String)`
-   **Key Fields:**
    -   `id`: Study ID.
    -   `studyType`: Type of study (`gwas`, `eqtl`, `pqtl`, etc.).
    -   `traitFromSource`: The trait analysed in the study.
    -   `credibleSets(...)`: 95% credible sets for this study.

## Common Query Patterns

### Finding Drugs for a Disease

To find drugs associated with a specific disease, use the `knownDrugs` field on
the `disease` entity. This is more direct than searching for evidence records.

```graphql
query diseaseDrugs($id: String!) {
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
}
```

### Pagination

Many relation fields (like `associatedDiseases`, `evidences`, `credibleSets`)
require a `page` argument to handle large datasets.

```graphql
query getAssocDiseases($id: String!) {
  target(ensemblId: $id) {
    associatedDiseases(page: {index: 0, size: 10}) {
      count
      rows {
        score
        disease {
          id
          name
        }
      }
    }
  }
}
```

### Search and ID Mapping

If you only have a string (like a gene symbol or disease name), use the `search`
or `mapIds` queries to find the correct canonical IDs.

```graphql
query searchEntity($query: String!) {
  search(
    queryString: $query,
    entityNames: ["target", "disease"],
    page: {index: 0, size: 5}
  ) {
    hits {
      id
      entity
      name
      description
    }
  }
}
```

## Best Practices & Tips for Agents

1.  **Check the `count`:** Always check the `count` field when querying
    paginated lists (`rows`). If the total `count` is larger than the number of
    `rows` returned, you are only seeing a partial result. Increase
    `--page-size` or adjust your query's `size` parameter if more data is
    needed.
2.  **Locus-to-Gene (L2G) Nuances:** When querying L2G predictions for a variant
    without specifying a study ID, you will get predictions across **all**
    credible sets where the variant is the lead. This often returns hundreds of
    rows. Use `--study-id` to narrow it down if the user is interested in a
    specific GWAS study.
3.  **Confidence Ratings:** Open Targets assigns "star ratings" based on the
    fine-mapping method used for credible sets (e.g., 4 stars = `SuSiE
    fine-mapped credible set with in-sample LD`). Match these exact strings when
    users ask for specific confidence tiers.
4.  **Avoid Excessive Limits:** The CLI tool defaults to a limit of 50 to
    protect context windows. Start with small limits or sizes (e.g., `size: 10`)
    when exploring the schema or doing preliminary searches, then increase if
    needed.
5.  **Use Subcommands First:** Whenever possible, use the specialized
    subcommands (e.g., `get-l2g`, `get-associated-targets`) instead of writing
    custom raw GraphQL queries, as they are pre-optimized and easier to invoke.
