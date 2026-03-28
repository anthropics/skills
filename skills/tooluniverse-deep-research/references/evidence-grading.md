# Evidence Grading Framework

Grade every claim by the strength of its source. Never present ungraded findings.

## Tier Definitions

| Tier | Name | Sources | Example |
|------|------|---------|---------|
| T1 | Regulatory / Curated | FDA, SEC EDGAR, ClinicalTrials.gov, FAERS, OMIM, DrugBank, ClinVar (reviewed) | "FDA approved osimertinib for EGFR+ NSCLC" |
| T2 | Peer-Reviewed | PubMed, Crossref, OpenAlex, EuropePMC (published journals) | "Phase 3 trial: 40% ORR (PMID:12345678)" |
| T3 | Preprint / Web | BioRxiv, MedRxiv, WebSearch, Wikipedia, news | "BioRxiv preprint proposes new mechanism" |
| T4 | Computational | STRING predictions, pathway inference, text-mining, similarity scores | "STRING interaction score 0.95" |

## Tool-to-Tier Mapping

| Tier | Tools |
|------|-------|
| T1 | FDA_OrangeBook_*, OpenFDA_*, FAERS_*, ClinicalTrials_*, SEC_EDGAR_*, ClinVar (reviewed), OMIM, DrugBank, DailyMed_* |
| T2 | PubMed_search_articles, Crossref_search_works, openalex_literature_search, EuropePMC_search_articles (published), SemanticScholar_*, PMC_search_papers |
| T3 | BioRxiv_*, MedRxiv_*, EuropePMC (SRC:PPR filter), WebSearch, Wikipedia_* |
| T4 | STRING_*, humanbase_ppi_analysis, KEGG_link_entries (inferred), OpenTargets (text-mining datasource), DisGeNET (text-mining score) |

## Grading Rules

1. **Convergence upgrades**: 3+ independent T2 sources confirming the same finding -- treat as T1-equivalent in the report
2. **Validation upgrades**: T4 prediction confirmed by T2 publication -- upgrade to T2
3. **Conflicts**: When sources disagree, report both tiers and note the conflict explicitly
4. **Absence is not evidence**: "No FAERS signal" means no reports filed, not that the drug is safe

## Citation Format

Every claim in the final report must include its tier and source:

- **Inline**: `[T1: ClinicalTrials_search_studies, NCT02511106]`
- **Tables**: Add `Tier` and `Source` columns
- **Prose**: "Osimertinib is FDA-approved for first-line EGFR+ NSCLC [T1: FDA_OrangeBook]"

In the Sources table at the end of the report, log every tool call:

| Tool | Query | Items | Tier | Iteration |
|------|-------|-------|------|-----------|
| PubMed_search_articles | "EGFR NSCLC treatment" | 12 | T2 | 1 |
