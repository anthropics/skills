# materials-citation

**Version:** 1.1.0

**What it does** — The literature-screening and claim-source mapping layer for
materials manuscripts. It builds search strategies, screens candidate records
into citation matrices with explicit evidence layers and source roles, runs
reference-gap audits, normalizes scholarly identifiers (DOI/PMID), and aligns
claims to sources for CBM, CCC, JBE, RMPD, IJPE, WER-EA, asphalt, cement/
concrete, durability, and mechanism-heavy topics. Search hits and
abstract-level matches stay labeled as screening outputs until deep reading
confirms the evidence.

**Built from** — Domain screening references, an academic-search MCP, and
matrix-building scripts:

- `mcp/academic_search/` — MCP server with adapters for Crossref, PubMed,
  OpenAlex, Semantic Scholar, arXiv, Scopus, and ScienceDirect/Elsevier; domain
  classification, identifier normalization, and export to BibTeX/CSL-JSON/RIS/
  JSONL
- `references/` — 18 files: 14 domain screening-and-source-quality guides
  (WER-EA, civil, ceramics, polymers, metals, functional, nano, semiconductors,
  dielectrics/piezoelectrics, photonic/optoelectronic, nanoparticles,
  nano-thin-films, 2D-materials, nanocomposites) plus claim-citation-mapping,
  reference-gap-audit, journal-search-profiles, and academic-search-mcp
- `assets/templates/` — citation-matrix CSV and search-plan templates
- `scripts/` — `build_citation_matrix.py` and `citation_search_fallback.py`

**Key rules enforced**

- Evidence layer and source role are explicit for every citation row.
- Prefer primary research and authoritative reviews over generic web summaries.
- Separate mechanism citations from performance citations.
- Reviewer risk is flagged per claim (must-fix vs. strengthen).
- Do not invent papers, DOIs, impact factors, journal rules, or citation counts.
- Screening output is not a substitute for deep paper reading.

**Useful CLI options**

Build a citation matrix from a topic and journal family (uses MCP domain
classification):

```powershell
python plugins/materials-skills/skills/materials-citation/scripts/build_citation_matrix.py `
  --topic "waterborne epoxy modified emulsified asphalt bonding" `
  --journals CBM,JBE,RMPD,IJPE `
  --claims-file claims.txt `
  --output materials-citation-matrix.csv
```

Standalone CrossRef search when the MCP server is unavailable (stdlib only):

```powershell
python plugins/materials-skills/skills/materials-citation/scripts/citation_search_fallback.py `
  --topic "waterborne epoxy modified emulsified asphalt bonding" `
  --journals CBM,CCC,JBE,RMPD,IJPE `
  --max-per-claim 3 `
  --output materials-citation-matrix.csv
```

**Reference files**

```text
skills/materials-citation/
├── README.md
├── SKILL.md
├── manifest.yaml
├── scripts/
│   ├── build_citation_matrix.py    matrix from topic + claims (MCP domain)
│   └── citation_search_fallback.py standalone CrossRef search (no MCP)
├── assets/templates/
│   ├── citation-matrix-template.csv
│   └── search-plan-template.md
├── references/
│   ├── claim-citation-mapping.md
│   ├── reference-gap-audit.md
│   ├── journal-search-profiles.md
│   ├── academic-search-mcp.md
│   ├── wer-ea-screening-and-source-quality.md
│   ├── civil-screening-and-source-quality.md
│   ├── ceramics-screening-and-source-quality.md
│   ├── polymers-screening-and-source-quality.md
│   ├── metals-screening-and-source-quality.md
│   ├── functional-screening-and-source-quality.md
│   ├── nano-screening-and-source-quality.md
│   ├── semiconductors-screening-and-source-quality.md
│   ├── dielectrics-piezoelectrics-screening-and-source-quality.md
│   ├── photonic-optoelectronic-screening-and-source-quality.md
│   ├── nanoparticles-screening-and-source-quality.md
│   ├── nano-thin-films-screening-and-source-quality.md
│   ├── 2d-materials-screening-and-source-quality.md
│   └── nanocomposites-screening-and-source-quality.md
├── mcp/academic_search/
│   ├── server.py / service.py          MCP server and service entry
│   ├── adapters/                       crossref, pubmed, openalex, semantic_scholar,
│   │                                    arxiv, scopus, sciencedirect, elsevier_common
│   ├── domain/                         classifier, identifiers, journals, queries
│   ├── export/                         bibtex, csl_json, ris, jsonl, formats
│   ├── importers/citation_files.py     RIS/BibTeX/CSV import
└── static/fragments/
    └── domain/    asphalt, cement-concrete, materials, ceramics, thermal-insulation,
                    polymers, metals, nano, functional
```

**Validation**

- MCP smoke checks can be run directly against the local server/service when needed.
- Bundle verification:
  `python .\scripts\run_release_checks.py --json`

The public GitHub package does not ship the internal MCP unit-test suite.

## When To Use

Use `materials-citation` when the user request matches this skill's production surface and the needed inputs are available or can be explicitly marked as missing.

## Inputs

Typical inputs are the user prompt, material direction/profile, target journal or task mode when relevant, and any source text, data, figures, reviewer comments, or package artifacts needed by the skill.

## Outputs

Outputs are structured handoffs or artifacts described above in this README. Missing evidence, author input needs, and unsupported claims stay visible instead of being hidden in fluent prose.

## Example

```text
Build a citation matrix for WER-EA bonding claims targeting CBM and RMPD.
```

## Validation

Run the skill-specific scripts or tests listed above when they apply, then run the bundle gate from the repository root:

```powershell
python .\scripts\run_release_checks.py --json
```

## Boundaries

This skill does not invent experiments, citations, measurements, journal facts, private file paths, or completed actions. Time-sensitive journal or legal facts should be checked against official sources before submission or filing.
