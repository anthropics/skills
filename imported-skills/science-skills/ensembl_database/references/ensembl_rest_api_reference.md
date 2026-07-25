# Ensembl REST API Reference

This document provides a concise reference for the Ensembl REST API
(`https://rest.ensembl.org`). Use it to build custom queries when the
`ensembl_api.py` script does not cover a specific use case.

## General Conventions

- **Base URL:** `https://rest.ensembl.org` (GRCh38). For GRCh37:
  `https://grch37.rest.ensembl.org`
- **Content Negotiation:** Set the `Content-Type` header to control the
  response format:
    - `application/json` — structured JSON (default for most endpoints)
    - `text/plain` — raw sequence string
    - `text/x-fasta` — FASTA-formatted sequence
    - `text/x-gff3` — GFF3 annotation output
- **Rate Limit:** Max 15 requests/second. On HTTP 429, honour the
  `Retry-After` header.
- **Region Format:** `CHR:START..END:STRAND` where STRAND is `1` (forward)
  or `-1` (reverse). A hyphen (`START-END`) also works for most endpoints.
- **Query Parameter Separator:** Ensembl uses `;` (semicolon) to separate
  query parameters, e.g. `?expand=1;mane=1`. Standard `&` also works.

---

## Lookup Endpoints

### `GET /lookup/id/{id}`
Look up any Ensembl stable ID (gene, transcript, protein) and retrieve
metadata.

- **`expand`** (0/1): Include child objects (Transcript array for genes, Exon
     array for transcripts, Translation for coding transcripts)
- **`mane`** (0/1): Include MANE Select/Plus Clinical annotations on transcripts
- **`db_type`** (string): Database (default: `core`). Options: `core`,
    `otherfeatures`
- **`format`** (string): `full` (default) or `condensed`
- **`species`** (string): Override species if the ID is ambiguous

**Key response fields (Gene):**
`id`, `display_name` (symbol), `biotype`, `description`,
`seq_region_name` (chromosome), `start`, `end`, `strand`,
`assembly_name`, `Transcript[]` (when expanded).

**Key response fields (Transcript, expanded):**
`id`, `biotype`, `display_name`, `is_canonical` (0 or 1), `length`,
`MANE[]` (array with `type`: `MANE_Select` or `MANE_Plus_Clinical`),
`TSL` (Transcript Support Level object with `value`),
`Exon[]`, `Translation` (with `id`, `start`, `end`, `length`).

### `GET /lookup/symbol/{species}/{symbol}`
Resolve a gene symbol to its Ensembl stable ID.

- **`expand`** (0/1): Include child objects

Returns the same structure as `/lookup/id/`.

### `POST /lookup/id`
Batch lookup: send `{"ids": ["ENSG...", "ENST..."]}` as JSON body.
Returns a dict keyed by ID.

---

## Cross-Reference Endpoints

### `GET /xrefs/id/{id}`
Retrieve external database references for an Ensembl ID.

- **`external_db`** (string): Filter by database name (e.g. `UniProt`, `HGNC`,
    `RefSeq_mRNA`, `UCSC`, `EntrezGene`)
- **`all_levels`** (0/1): Include xrefs from parent/child features

**Response:** Array of objects with `primary_id`, `display_id`,
`db_display_name`, `dbname`, `description`, `info_type`.

### `GET /xrefs/symbol/{species}/{symbol}`
Find Ensembl IDs matching an external symbol.

### `GET /xrefs/name/{species}/{name}`
Broader search — looks up any name across all external databases.

---

## Sequence Endpoints

### `GET /sequence/id/{id}`
Fetch sequence for an Ensembl feature by stable ID.

- **`type`** (string): `genomic` (default), `cdna`, `cds`, `protein`
- **`expand_5prime`** (int): Extend N bases upstream
- **`expand_3prime`** (int): Extend N bases downstream
- **`mask`** (string): Masking: `hard` or `soft`

Set `Accept: text/x-fasta` for FASTA output, `text/plain` for raw string.

### `GET /sequence/region/{species}/{region}`
Fetch genomic DNA for a coordinate window.

- **`coord_system_version`** (string): Assembly version (e.g. `GRCh38`)
- **`expand_5prime`** (int): Extend N bases upstream
- **`expand_3prime`** (int): Extend N bases downstream
- **`mask`** (string): `hard` or `soft` repeat masking
- **`mask_feature`** (0/1): Apply feature-level masking

Region format: `CHR:START..END:STRAND` (e.g., `X:1000000..1000100:1`).

### `POST /sequence/region/{species}`
Batch: send `{"regions": ["X:1000..2000", "7:100..200"]}`.

---

## Overlap Endpoints

### `GET /overlap/region/{species}/{region}`
Find features overlapping a genomic region. This is useful for finding
genes at a locus, variants in a window, or regulatory features.

- **`feature`** (string): Feature types to return. Repeat for multiple. Values:
  `gene`, `transcript`, `cds`, `exon`, `repeat`, `simple`, `misc`, `variation`,
  `somatic_variation`, `structural_variation`, `somatic_structural_variation`,
  `constrained`, `regulatory`, `motif`, `chipseq`, `array_probe`
- **`biotype`** (string): Filter by biotype (e.g. `protein_coding`)
- **`variant_set`** (string): Short set name for variant filtering

**Example:** Find all genes and transcripts in a region:
```
/overlap/region/human/7:140424943-140624564?feature=gene;feature=transcript
```

### `GET /overlap/id/{id}`
Features that overlap with an Ensembl feature (gene, transcript, etc.).
Same `feature` parameter options as above.

### `GET /overlap/translation/{id}`
Protein features overlapping a translation. Used for domain annotations.

- **`feature`** (string): `protein_feature`, `residue_overlap`,
    `translation_exon`
- **`type`** (string): Filter by source database name (e.g. `Pfam`, `Gene3D`,
    `CDD`, `Smart`, `SuperFamily`, `PANTHER`, `Prosite_patterns`, `PRINTS`,
    `MobiDBLite`)

**Example:** Get Pfam domain annotations for a protein:
```
/overlap/translation/ENSP00000269305?feature=protein_feature;type=Pfam
```

**Response fields (protein_feature):** `type` (source DB), `id` (domain
accession), `description`, `start` (amino acid start), `end`.

---

## Comparative Genomics Endpoints

### `GET /homology/id/{species}/{id}`
Retrieve homologues (orthologs/paralogs) for a gene.

- **`type`** (string): `orthologues`, `paralogues`, `projections`, `all`
- **`target_species`** (string): Restrict to a specific target species
- **`target_taxon`** (int): Restrict by NCBI taxon ID
- **`sequence`** (string): `none`, `cdna`, `protein` — include aligned sequences

### `GET /homology/symbol/{species}/{symbol}`
Same as above, by gene symbol instead of ID.

### `GET /genetree/id/{id}`
Fetch a full gene tree by its Ensembl Compara tree ID.

### `GET /genetree/member/id/{species}/{id}`
Fetch the gene tree containing a specific gene.

---

## Variation Endpoints

### `GET /variation/{species}/{id}`
Retrieve details for a known variant (by rsID or Ensembl variation ID).

**Response fields:** `name` (rsID), `mappings[]` (with `location`,
`allele_string`, `start`, `end`, `strand`), `ancestral_allele`,
`minor_allele`, `MAF`, `clinical_significance[]`, `source`.

### `GET /variant_recoder/{species}/{id}`
Recode a variant between different formats (HGVS, VCF, SPDI, rsID).

**Response fields:** `spdi[]`, `hgvsg[]`, `hgvsc[]`, `hgvsp[]`,
`vcf_string[]`, `id[]` (rsIDs).

---

## VEP (Variant Effect Predictor) Endpoints

### `GET /vep/{species}/region/{region}/{allele}`
Predict consequences for a genomic variant.

Region format: `CHR:START-END:STRAND` (e.g., `9:21971147-21971147:1`).
Allele is the alternate allele string.

### `GET /vep/{species}/id/{id}`
Predict consequences by rsID.

### `GET /vep/{species}/hgvs/{hgvs_notation}`
Predict consequences by HGVS notation.

**Plugin parameters (append as query params):**

- `AlphaMissense=1` — AlphaMissense pathogenicity predictions
- `Conservation=1` — PhyloP conservation scores
- `DosageSensitivity=1` — Haploinsufficiency / triplosensitivity
- `LoF=loftee` — LOFTEE loss-of-function assessment
- `LOEUF=1` — Loss-of-function observed/expected upper bound fraction
- `NMD=1` — Nonsense-mediated decay prediction
- `UTRAnnotator=1` — 5'/3' UTR variant annotation
- `mutfunc=1` — Functional impact prediction
- `IntAct=1` — Protein interaction impact
- `MaveDB=1` — Multiplex assay scores
- `OpenTargets=1` — Open Targets genetics data

**Key response fields:** `most_severe_consequence`,
`transcript_consequences[]` (with `gene_symbol`, `transcript_id`,
`consequence_terms[]`, `amino_acids`, `sift_prediction`, `sift_score`,
`polyphen_prediction`, `polyphen_score`, `am_class`,
`am_pathogenicity`, `conservation`, `lof`, `loeuf`).

### `POST /vep/{species}/region`
Batch VEP: send `{"variants": ["1 100 . A T . . ."]}` in VCF-like format.

---

## Mapping Endpoints

### `GET /map/{species}/{asm_one}/{region}/{asm_two}`
Convert coordinates between assemblies (e.g., GRCh37 → GRCh38).

**Example:**
```
/map/human/GRCh37/17:43044295-43125370/GRCh38
```

**Response:** `mappings[]` with `original` and `mapped` coordinate blocks.

### `GET /map/cdna/{id}/{region}`
Map cDNA coordinates to genomic coordinates for a transcript.

### `GET /map/cds/{id}/{region}`
Map CDS coordinates to genomic coordinates.

### `GET /map/translation/{id}/{region}`
Map protein (amino acid) positions to genomic coordinates.

---

## Phenotype Endpoints

### `GET /phenotype/gene/{species}/{gene}`
Phenotype annotations for a gene (by symbol or Ensembl ID).

### `GET /phenotype/region/{species}/{region}`
Phenotype-associated variants in a genomic region.

### `GET /phenotype/term/{species}/{term}`
Find variants/genes associated with a phenotype term (ontology ID or
description string, e.g., `coffee consumption`).

---

## Linkage Disequilibrium Endpoints

### `GET /ld/{species}/{id}/{population_name}`
Compute LD for variants in a window around a variant.

- **`window_size`** (int): Window size in kb (default: 500)
- **`r2`** (float): Minimum r² threshold
- **`d_prime`** (float): Minimum D' threshold

### `GET /ld/{species}/pairwise/{id1}/{id2}`
Pairwise LD between two specific variants.

### `GET /ld/{species}/region/{region}/{population_name}`
LD for all variant pairs in a region.

Population names: e.g., `1000GENOMES:phase_3:CEU`, `1000GENOMES:phase_3:YRI`.

---

## Information Endpoints

### `GET /info/assembly/{species}`
Assembly metadata (karyotype, top-level regions, coordinate systems).

### `GET /info/assembly/{species}/{region_name}`
Details for a specific chromosome/region (length, bands).

### `GET /info/species`
List all species available in the Ensembl REST API.

### `GET /info/external_dbs/{species}`
List all external database names available for cross-references.
Useful for finding the correct `external_db` parameter value.

### `GET /info/biotypes/{species}`
List all biotype classifications for a species.

---

## Best Practices for Custom Queries

1. **Always set `Content-Type`** to `application/json` for JSON responses
   or `text/plain` / `text/x-fasta` for sequence endpoints.
2. **Use `expand=1`** on lookup endpoints to get child features in a single
   call instead of making separate requests for each transcript/exon.
3. **Prefer batch endpoints** (`POST /lookup/id`, `POST /sequence/region`)
   when querying multiple IDs or regions — this reduces the number of HTTP
   round-trips.
4. **Check `info/external_dbs`** before using the `external_db` filter on
   xrefs — the exact database name strings are case-sensitive and not
   always obvious (e.g., `UniProt_gn` not `UniProt`).
5. **Region size limits**: The `/overlap/region/` endpoint has a maximum
   region size of 5 Mb for most feature types. Split larger regions.
6. **Use `grch37.rest.ensembl.org`** as the base URL when your coordinates
   are on the GRCh37 (hg19) assembly. Most endpoints support the same
   paths on this older server.
7. **Save responses to temp files** — do not try to read large JSON
   responses into context. Use `jq` or Python one-liners to extract
   specific fields.
