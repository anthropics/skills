# NCBI API Implementation Notes

This document provides context about the NCBI endpoints used by the
`dbsnp-database` skill.

## Endpoints

The script uses two distinct NCBI services:

### 1. Variation Services (`https://api.ncbi.nlm.nih.gov/variation/v0/`)

A RESTful API for precise variant mapping and resolution. Key endpoints:

- **`/refsnp/{rsid}`** — Returns the full RefSNP JSON record. The
  response contains a `primary_snapshot_data` object with:
  - `variant_type` — e.g. `snv`, `del`, `ins`, `delins`, `mnv`.
  - `placements_with_allele` — Genomic placements across assemblies. Each
    placement includes a `seq_id`, `is_ptlp` flag (true for top-level
    placements), and per-assembly alleles in SPDI form.
  - `allele_annotations` — Per-allele metadata including gene associations
    (`assembly_annotation[].genes[]`), clinical significance entries, and
    population frequency data.
- **`/vcf/{chrom}/{pos}/{ref}/{alt}/contextuals`** — Converts VCF coordinates
  to component-form representations. Returns `data.spdis[]` — each entry has
  `seq_id`, `position`,`deleted_sequence`, and `inserted_sequence` fields.
- **`/spdi/{spdi_string}/rsids`** — Resolves an SPDI string to its canonical
  rsID(s). Returns `data.rsids[]`.
- **`/hgvs/{hgvs_string}/contextuals`** — Converts an HGVS expression to the
  same component form. Same response shape as the VCF contextuals endpoint.

The VCF-to-rsID and HGVS-to-rsID workflows are two-step: first convert the input
to SPDI, then resolve each SPDI to rsIDs.

### 2. E-utilities (`https://eutils.ncbi.nlm.nih.gov/entrez/eutils/`)

NCBI's general-purpose Entrez search interface. The skill uses `esearch.fcgi`
with `db=snp` for regional variant searches.

#### Useful Entrez field tags for `db=snp`

- **`[CHR]`**: Filter by chromosome. Example: `7[CHR]`
- **`[CPOS]`**: GRCh38 coordinate range. Example: `117100000:117300000[CPOS]`
- **`[CPOS_GRCH37]`**: GRCh37 coordinate range.
    Example: `117100000:117300000[CPOS_GRCH37]`
- **`[GENE]`**: Filter by gene symbol. Example: `LPL[GENE]`
- **`[SCLS]`**: Filter by variant class. Example: `snp[SCLS]`
- **`[ORGN]`**: Filter by organism. Example: `human[ORGN]`
- **`[CLIN]`**: Clinical significance. Example: `pathogenic[CLIN]`

Tags are combined with `AND`. Example query:

```
7[CHR] AND 117100000:117300000[CPOS]
```

Pagination uses `retstart` (0-based offset) and `retmax` (page size).
The script automatically paginates when results exceed a single page.

## The SPDI Data Model

SPDI (Sequence-Position-Deletion-Insertion) is NCBI's canonical representation
for unambiguously defining sequence variants. It consists of four components:

- **Sequence**: RefSeq accession of the reference sequence
- **Position**: 0-based inter-residue coordinate of the change
- **Deletion**: Number of deleted bases (or the deleted sequence)
- **Insertion**: The inserted sequence (empty string for deletions)

Example: `NC_000008.11:19962212:1:` represents a single-base deletion at
position 19962213 (1-based) on chromosome 8.

SPDI is used as the intermediate representation in the VCF→rsID and HGVS→rsID
resolution workflows. You generally do not need to construct SPDI strings
manually — the Variation Services API does the conversion.

## Throttling and Rate Limits

NCBI enforces rate limits on all public endpoints:

- No API key: 3 requests/second
- With API key: 10 requests/second

The script reads the `NCBI_API_KEY` environment variable and adjusts its
internal delay accordingly. A file-lock mechanism ensures that multiple
concurrent invocations of the script collectively respect the limit.

If the limit is exceeded the NCBI server returns HTTP 429 and the script raises
a `RateLimitError` with instructions for the agent.
