# Reactome Analysis Service API Reference

Base URL: `https://reactome.org/AnalysisService`

## Database (2 endpoints)

All endpoints use **GET**.

- `/database/name` — Returns the database name
- `/database/version` — Returns the database version number

## Identifier (2 endpoints)

All endpoints use **GET**.

- `/identifier/{id}` — Analyse a single identifier across species
- `/identifier/{id}/projection` — Analyse with projection to Homo Sapiens

**Parameters:** `interactors`, `species`, `includeDisease`, `pageSize`, `page`,
`sortBy`, `order`, `resource`

## Identifiers - Batch Analysis (6 endpoints)

All endpoints use **POST**.

- `/identifiers/` — Analyse posted identifiers
- `/identifiers/projection` — Analyse with projection to Homo Sapiens
- `/identifiers/form` — Analyse identifiers from file upload
- `/identifiers/form/projection` — File upload with projection
- `/identifiers/url` — Analyse from URL
- `/identifiers/url/projection` — URL analysis with projection

**Content-Type:** `text/plain` for POST body, `multipart/form-data` for form.

**Input format:**

- One identifier per line for overrepresentation analysis
- TSV with `#header` row for expression analysis (column 1: identifiers, columns 2+: numeric values)

## Token - Result Retrieval (13 endpoints)

Endpoints use **GET** unless noted as POST.

- `/token/{token}` — Retrieve full result by token
- `/token/{token}/filter/species/{species}` — Filter result by species
- `/token/{token}/filter/pathways` — Filter by posted pathway IDs (POST)
- `/token/{token}/found/all` — Summary of found identifiers for posted pathways (POST)
- `/token/{token}/found/all/{pathway}` — Found identifiers for one pathway
- `/token/{token}/found/entities/{pathway}` — Found curated identifiers
- `/token/{token}/found/interactors/{pathway}` — Found interactors
- `/token/{token}/notFound` — List of not-found identifiers
- `/token/{token}/page/{pathway}` — Page number for a pathway
- `/token/{token}/pathways/binned` — Binned hit pathway sizes
- `/token/{token}/reactions/{pathway}` — Reaction IDs for a pathway
- `/token/{token}/reactions/pathways` — Reaction IDs for posted pathways (POST)
- `/token/{token}/resources` — Resources summary

## Download (5 endpoints)

All endpoints use **GET**.

- `/download/{token}/result.json` — Full result as JSON
- `/download/{token}/result.json.gz` — Full result as gzipped JSON
- `/download/{token}/entities/found/{resource}/{filename}.csv` — Found identifiers CSV
- `/download/{token}/entities/notfound/{filename}.csv` — Not-found identifiers CSV
- `/download/{token}/pathways/{resource}/{filename}.csv` — Hit pathways CSV

## Mapping (6 endpoints)

All endpoints use **POST**.

- `/mapping/` — Map identifiers across species
- `/mapping/projection` — Map with projection to Homo Sapiens
- `/mapping/form` — Map from file upload
- `/mapping/form/projection` — File upload with projection
- `/mapping/url` — Map from URL
- `/mapping/url/projection` — URL mapping with projection

## Import (3 endpoints)

All endpoints use **POST**.

- `/import/` — Import previously exported JSON
- `/import/form` — Import JSON via file upload
- `/import/url` — Import JSON from URL

## Report (1 endpoint)

Uses **GET**.

- `/report/{token}/{species}/{filename}.pdf` — Download PDF report

## Species Comparison (1 endpoint)

Uses **GET**.

- `/species/homoSapiens/{species}` — Compare Homo sapiens to another species

## Common Parameters

- `pageSize` (int) — Results per page
- `page` (int) — Page number (1-based)
- `sortBy` (string) — Sort field (NAME, ENTITIES_PVALUE, ENTITIES_FDR, etc.)
- `order` (string) — ASC or DESC
- `resource` (string) — TOTAL, UNIPROT, ENSEMBL, etc.
- `species` (string) — NCBI Taxon ID or species name
- `interactors` (bool) — Include interactor data
- `includeDisease` (bool) — Include disease pathways

## Supported Identifier Types

UniProt, Gene Symbol, Ensembl, EntrezGene, ChEBI, OMIM, miRBase,
GenBank/EMBL/DDBJ, RefPep, RefSeq, InterPro, Affymetrix, Agilent, Illumina,
and more.

**Total: 39 endpoints across 9 categories.**
