# ENCODE SCREEN GraphQL API Schema Reference

This document outlines the queries and types available in the ENCODE SCREEN
GraphQL API (`https://factorbook.api.wenglab.org/graphql`), as used in the
`encode-database` skill.

## Core Queries

### `cCRESCREENSearch`

Searches for candidate cis-Regulatory Elements (cCREs).

**Arguments:**

-   `assembly` (String!): The genome assembly (e.g., "grch38", "mm10").
-   `coordinates` ([GenomicRangeInput!]): List of `{chromosome, start, end}`
    objects.
-   `accessions` ([String!]): List of specific cCRE accessions.
-   `rank_ctcf_start` / `rank_ctcf_end` (Float): Range filters for CTCF z-score.
-   `cellType` (String): Filter by biosample-specific epigenetic signal.

**Returns Fields:**

-   `chrom`, `start`, `len`, `pct`
-   `ctcf_zscore`, `dnase_zscore`, `atac_zscore`, `enhancer_zscore`,
    `promoter_zscore`
-   `info { accession }`
-   `nearestgenes { gene, distance }`
-   `ctspecific { ct, ctcf_zscore, dnase_zscore, h3k4me3_zscore,`
    `h3k27ac_zscore, atac_zscore }`

### `ccREBiosampleQuery`

Retrieves biosample metadata.

**Arguments:**

-   `assembly` (String!)

**Returns Fields:**

-   `biosamples` (List):
    -   `name`, `ontology`, `lifeStage`, `sampleType`, `displayname`
    -   Experiment and file accessions for assays (DNase, H3K4me3, H3K27ac,
        CTCF, ATAC)
    -   `cCREZScores(accession: String!) { score, assay,` `experiment_accession
        }`

### `cCREQuery`

Retrieves details for a specific cCRE.

**Arguments:**

-   `assembly` (String!)
-   `accession` (String!)
-   `coordinates` (GenomicRangeInput)

**Returns Fields:**

-   `accession`, `group`, `coordinates { chromosome, start, end }`
-   `maxZ(assay: String!)`: Max Z-score for a given assay.

### `gene` / `snpQuery`

Retrieves nearby genes and SNPs.

**`gene` Arguments:** `chromosome`, `start`, `end`, `assembly`
**`snpQuery` Arguments:** `coordinates`, `assembly`, `common`

**Returns Fields:** Coordinates, transcripts, names, etc.

### `orthologQuery`

Retrieves orthologous cCREs in another assembly.

**Arguments:**

-   `assembly` (String!)
-   `accession` (String!)

**Returns Fields:**

-   `ortholog { stop, start, chromosome, accession }`

### `linkedGenesQuery`

Retrieves linked genes (e.g., via HiC, eQTLs, CRISPR).

**Arguments:**

-   `assembly` (String!)
-   `accession` ([String]!)

**Returns Fields:**

-   `gene`, `method`, `effectsize`, `assay`, `celltype`, `score`, `p_val`, etc.

### `entexQuery` / `entexActiveAnnotationsQuery`

Retrieves ENTEx data.

**`entexQuery` Arguments:** `accession` (String!)
**`entexActiveAnnotationsQuery` Arguments:** `coordinates` (GenomicRangeInput!)
**Returns Fields:**: Tissue, assay score, hap counts, allele ratio, p-values.

### `gene`

Resolves a gene name to its Ensembl ID and coordinates.

**Arguments:**

-   `assembly` (String!): The genome assembly (e.g., "grch38").
-   `name` ([String!]): List of gene symbols to look up.

**Returns Fields:**

-   `name`, `id` (Ensembl gene ID), `coordinates { start, chromosome, end }`

### `gene_quantification`

Retrieves per-experiment gene expression quantification data.

**Arguments:**

-   `assembly` (String!): The genome assembly.
-   `gene_id_prefix` ([String]): Ensembl gene ID prefixes to filter by.
-   `sortByTpm` (Boolean): If true, results are sorted by TPM descending.
-   `limit` (Int): Maximum number of results to return.

**Returns Fields:**

-   `experiment_accession`, `file_accession`, `tpm`, `fpkm`, `len`,
    `effective_len`, `expected_count`, `pme_tpm`, `pme_fpkm`

### `gene_dataset`

Retrieves biosample metadata for RNA-seq experiments.

**Arguments:**

-   `accession` ([String]): Filter by experiment accession(s).
-   `tissue`, `biosample`, `biosample_type`, `cell_compartment`,
    `assay_term_name` ([String]): Optional biosample filters.
-   `processed_assembly` (String): Assembly filter (e.g., "GRCh38").

**Returns Fields:**

-   `accession`, `biosample`, `tissue`, `biosample_type`, `cell_compartment`,
    `assay_term_name`

### GWAS Queries

Queries for Genome-Wide Association Studies data.

**`getAllGwasStudies`:** Returns study name, author, pubmed ID.
**`getSNPsforGWASStudies(study: [String!]!)`:** Returns SNPs, ldblocks, rsquare,
coordinates. **`getGWASCtEnrichmentQuery(study: String!)`:** Returns celltype
enrichment data (fc, fdr, pvalue).

## Notes

**Pagination / Limits:** If a query is too large, it may return an error. Split
the request coordinates or accessions into smaller chunks. **Composability:**
Multiple queries can be batched in a single request, but it's often more
efficient to use the provided python script abstractions unless a highly
specific custom GraphQL query is required.
