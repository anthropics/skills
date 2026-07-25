# Materials Science Academic-Search MCP

Local stdio MCP server for materials science and engineering literature search across 8 academic data sources.

## Available Tools

| Tool | Description |
|---|---|
| `search_materials` | Search papers by topic with journal, material domain, and evidence-layer filters |
| `fetch_paper_metadata` | Resolve paper metadata by DOI, title, or external ID |
| `suggest_search_queries` | Generate journal-aware Boolean search queries |
| `build_claim_source_map` | Map manuscript claims to evidence type, search queries, and source candidates |
| `audit_reference_gaps` | Flag missing mechanism, performance, durability, and reviewer-safe source evidence |
| `export_citation_matrix` | Export rows compatible with the materials citation matrix template |
| `resolve_paper_ids` | Normalize DOI, PMID, PMCID, arXiv, OpenAlex, Semantic Scholar, Scopus EID, and ScienceDirect PII |
| `convert_citation_records` | Parse RIS/BibTeX/NBIB/CSV and export to RIS/BibTeX/GB/T 7714/CSL JSON/JSONL |
| `deduplicate_citation_records` | Deduplicate by DOI, external IDs, then normalized title and year |
| `get_formatted_citation` | Generate formatted citations in RIS, BibTeX, GB/T 7714, APA, Nature, or IEEE styles |
| `lookup_mesh` | Look up PubMed MeSH terms for materials or chemistry topics |
| `list_academic_sources` | List enabled and disabled academic metadata sources |

## Data Source Adapters

| Adapter | Requires API Key | Notes |
|---|---|---|
| Crossref | No (email recommended) | General-purpose scholarly metadata |
| PubMed | No (email recommended) | Biomedical, chemistry-adjacent, sustainability |
| OpenAlex | Optional (`OPENALEX_API_KEY`) | Open catalog of scholarly works |
| Semantic Scholar | Optional (`SEMANTIC_SCHOLAR_API_KEY`) | AI-powered academic search |
| arXiv | No | Preprint server for physics, math, CS |
| Scopus | Yes (`SCOPUS_API_KEY`) | Elsevier curated abstract database |
| ScienceDirect | Yes (`SCIENCEDIRECT_API_KEY`) | Elsevier full-text and metadata |
| Base (fallback) | No | Minimal metadata extraction |

## Export Formats

| Format | Use Case |
|---|---|
| RIS | Reference managers (Zotero, EndNote, Mendeley) |
| BibTeX | LaTeX / Overleaf manuscripts |
| GB/T 7714 | Chinese journal submissions |
| CSL-JSON | Programmatic citation processing |
| JSONL | Bulk data pipelines |
| APA / Nature / IEEE | Formatted citation strings via CrossRef |

## Architecture

```
server.py          — MCP stdio protocol entry point (JSON-RPC 2.0)
service.py         — Business logic layer, adapter orchestration
adapters/          — 8 academic data source adapters
domain/            — Evidence classifier, journal databases, query builders, identifiers
export/            — 5 export formats (RIS, BibTeX, GB/T 7714, CSL-JSON, JSONL)
importers/         — Citation file parsers (RIS, BibTeX, NBIB, CSV)
```

## Search Strategy

1. Use `suggest_search_queries` to generate journal-aware Boolean queries
2. Use `lookup_mesh` to check standardized MeSH terms for chemistry/materials topics
3. Use `search_materials` with `evidence_layer` filter to target specific claim types
4. Use `build_claim_source_map` to map manuscript claims to evidence sources
5. Use `audit_reference_gaps` to identify missing evidence before submission
6. Use `export_citation_matrix` to produce reviewer-ready citation audit

## Public Verification

The public GitHub package keeps the MCP server code and runtime requirements,
but does not ship the internal unit-test suite. From the repository root, run:

```powershell
python .\scripts\run_release_checks.py --json
```

## Smoke Test

```powershell
'{"jsonrpc":"2.0","id":1,"method":"tools/list","params":{}}' | python "plugins/materials-skills/skills/materials-citation/mcp/academic_search/server.py"
```

## Optional Environment Variables

- `OPENALEX_API_KEY`: enables OpenAlex searches.
- `SEMANTIC_SCHOLAR_API_KEY`: increases Semantic Scholar rate limits.
- `MATERIALS_CONTACT_EMAIL`: enables polite Crossref and PubMed E-utilities requests.
- `NCBI_API_KEY`: optional PubMed E-utilities key for higher rate limits.
- `SCOPUS_API_KEY`: enables Scopus searches.
- `SCIENCEDIRECT_API_KEY`: enables ScienceDirect searches.

## Core Rule

Treat returned papers as candidates. Use `materials-reader` for deep reading before making novelty, mechanism, or durability claims.
