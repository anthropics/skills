# Follow the Data

Domain-agnostic entity exploration. Don't decide the domain upfront -- follow entities to their connections.

## Core Principle

When you find an entity, explore its connections regardless of what domain they lead to. If heart failure research leads to dental microbiology via a shared pathway, chase it. The non-obvious connections are where discoveries live.

The brain doesn't know what domain it's in. It just follows entities to their connections.

## Entity Exploration Table

| When you find a... | Explore... | Using... |
|---------------------|-----------|----------|
| Gene | pathways, interactions, expression, variants, diseases | STRING, KEGG, GTEx, ClinVar, OpenTargets |
| Protein | structure, domains, binding partners, modifications | UniProt, AlphaFold, PDB, InterPro |
| Pathway | member genes, targeting drugs, related diseases | KEGG, Reactome, OpenTargets |
| Drug | targets, safety, trials, approvals, mechanism | ChEMBL, FAERS, ClinicalTrials, FDA, DailyMed |
| Disease | associated genes, drugs, trials, phenotypes | OpenTargets, HPO, ClinicalTrials, Orphanet |
| Variant | clinical significance, population frequency, drug response | ClinVar, gnomAD, CIViC, PharmGKB |
| Clinical trial | drug, disease, endpoints, status, sponsor | ClinicalTrials |
| Company | filings, pipeline, approvals, safety events | SEC EDGAR, ClinicalTrials, FDA, FAERS |
| Publication | cited entities, citing papers, related works | EuropePMC, Crossref, Semantic Scholar |

## Fallback Chains

When the primary tool for an entity type is broken or unavailable, use fallbacks:

| Entity | Primary | Fallback 1 | Fallback 2 | Last resort |
|--------|---------|------------|------------|-------------|
| Gene function | OpenTargets | KEGG | UniProt (function) | PubMed search |
| Protein info | UniProt | PDB | AlphaFold | Ensembl |
| Drug targets | ChEMBL | OpenTargets | DrugBank | PubMed search |
| Drug safety | FAERS | OpenFDA enforcement | DailyMed labels | PubMed search |
| Clinical trials | ClinicalTrials | EuropePMC (trial filter) | WHO ICTRP | WebSearch |
| Disease genes | OpenTargets | ClinVar | GWAS Catalog | DisGeNET |
| Pathways | KEGG | Reactome | WikiPathways | GO enrichment |
| PPI network | STRING | humanbase_ppi | IntAct | BioGRID |
| Literature | PubMed | OpenAlex | EuropePMC | Semantic Scholar |
| Variants | ClinVar | CIViC | gnomAD | GWAS Catalog |
| Company data | SEC EDGAR | WebSearch | Wikipedia | -- |

## The Unexpected Path Rule

If an entity connection leads somewhere you didn't expect:

1. **Follow it** -- don't filter by your assumption of what's relevant
2. **Record it** -- add to research_state.json connections with the relationship type
3. **Evaluate it** -- is this a known cross-domain link or a novel observation?
4. **Report it** -- unexpected connections get their own subsection in the report

Example: Researching metformin (diabetes drug) and finding it connects to AMPK, which connects to mTOR, which connects to cancer -- this is not noise, this is the drug repurposing signal that led to active clinical trials.
