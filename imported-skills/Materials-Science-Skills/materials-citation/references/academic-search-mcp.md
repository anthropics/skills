# Materials Science Academic-Search MCP

This MCP is the upstream search and metadata-verification layer for `materials-citation`, `materials-reader`, and the broader materials skill bundle.

## Installed Server

- Server name: `materials-academic-search`
- Repository entry point: `plugins/materials-skills/skills/materials-citation/mcp/academic_search/server.py`
- Installed skill entry point: `$CODEX_HOME/skills/materials-citation/mcp/academic_search/server.py`
- Runtime: Python stdio JSON-RPC MCP, using `httpx` for scholarly APIs.
- Registered in: `$CODEX_HOME/config.toml`

## What It Does

- Searches scholarly sources through Crossref, PubMed, Semantic Scholar, and OpenAlex when credentials are available.
- Resolves DOI, title, year, journal, author, abstract, URL, citation count when available, and source provenance.
- Filters and labels materials journal families: CBM, CBM in Transportation, CCC, CCS, CSCM, JBE, RMPD, IJPE, and JRE.
- Classifies evidence layers for asphalt, pavement, cement, concrete, durability, sustainability, and waterborne epoxy modified emulsified asphalt.
- Builds claim-source maps and reference-gap audits before manuscript writing or review writing.
- Exports citation-matrix rows compatible with `assets/templates/citation-matrix-template.csv`.

## Public Tools

### `search_materials`

Use for first-pass paper retrieval.

Required input:

- `topic`

Optional input:

- `journal_family`: string or list, for example `["CBM", "RMPD", "IJPE"]`
- `material_domain`: `asphalt`, `cement-concrete`, or `materials`
- `evidence_layer`
- `year_range`: for example `2020-2026`
- `limit`

Output includes:

- `records`
- `query`
- `queries`
- `warnings`
- `tool_notes`

Each record includes `source_provenance`, `missing_fields`, `metadata_conflicts`, `risk_flags`, and `confidence`.

### `fetch_paper_metadata`

Use to verify one candidate paper before citing it.

Input can include:

- `doi`
- `title`
- `external_id`
- `openalex_id`
- `semantic_scholar_id`

Never invent missing DOI or metadata. If a field cannot be resolved, keep it in `missing_fields`.

### `suggest_search_queries`

Use before database searching or when building a review search strategy.

It creates evidence-aware Boolean searches for:

- bonding and interface evidence,
- FTIR/SEM/fluorescence/rheology mechanism evidence,
- moisture, aging, and service-condition durability evidence,
- storage stability and viscosity,
- waterborne epoxy curing,
- review and research-gap positioning.

### `lookup_mesh`

Use before PubMed or chemistry-adjacent searching to identify standardized MeSH terms.

Input:

- `topic`
- `limit`

Output:

- `topic`
- `mesh_terms`
- `scope_notes`
- `source`

### `build_claim_source_map`

Use when a manuscript paragraph, review subsection, or planned claim needs citations.

Output maps:

- claim,
- evidence type needed,
- evidence layer needed,
- candidate records,
- search query,
- reviewer risk flags.

### `audit_reference_gaps`

Use before writing or submitting.

It flags:

- no confirmed source mapped to the claim,
- mechanism claims without FTIR/SEM/fluorescence/rheology evidence,
- durability claims without moisture, aging, or service-condition evidence,
- figure-caption overclaim risks.

### `export_citation_matrix`

Use when moving results into the citation workflow.

Output:

- structured `rows`
- CSV text matching the existing citation matrix schema.

## Evidence Layers

For waterborne epoxy modified emulsified asphalt, separate these layers:

- `demulsification`
- `epoxy_curing`
- `storage_stability`
- `viscosity`
- `bonding_interface`
- `ftir_sem_fluorescence_rheology`
- `moisture_aging_service`
- `review_positioning`

Do not mix mechanism citations and performance citations unless the source directly supports both.

## Recommended Workflow

1. Use `suggest_search_queries` for search strategy.
2. Use `search_materials` to retrieve candidates.
3. Use `lookup_mesh` when PubMed vocabulary may improve topic wording.
4. Use `fetch_paper_metadata` to verify DOI/title/journal/year before citing.
5. Use `build_claim_source_map` to map sources to manuscript claims.
6. Use `audit_reference_gaps` before making novelty, mechanism, or durability claims.
7. Use `export_citation_matrix` and continue with `materials-citation`.
8. Use `materials-reader` for deep evidence-chain reading before writing final claims.

## Source Rules

- Crossref is used for DOI and publisher metadata.
- PubMed is used for NCBI-indexed biomedical, chemistry-adjacent, sustainability, and materials records; `lookup_mesh` uses the MeSH database.
- Semantic Scholar is used for abstracts, citation counts, and paper IDs when available.
- OpenAlex is skipped unless `OPENALEX_API_KEY` is set.
- `SEMANTIC_SCHOLAR_API_KEY` is optional.
- `MATERIALS_CONTACT_EMAIL` is optional for Crossref polite-pool requests and recommended for PubMed.
- `NCBI_API_KEY` is optional for PubMed rate-limit improvement.

## What It Does Not Do

- It does not replace deep reading.
- It does not prove novelty by itself.
- It does not invent DOI, impact factor, citation count, or paper identity.
- It does not make journal scope or submission rules safe without current official-source verification.
