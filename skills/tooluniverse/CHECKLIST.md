# ToolUniverse Research Checklist

Quick reference checklist for comprehensive ToolUniverse research.

## Before Starting Research

- [ ] **Tool Discovery**: Search for ALL relevant tools using multiple queries
  - [ ] Main topic query
  - [ ] Synonym/alternative term queries
  - [ ] Database-specific queries (UniProt, ChEMBL, etc.)
  - [ ] Data type queries (expression, variants, etc.)

- [ ] **Entity Disambiguation**:
  - [ ] Resolve canonical IDs (UniProt, Ensembl, PubChem CID, EFO, etc.)
  - [ ] Collect all synonyms/aliases
  - [ ] Identify naming collisions
  - [ ] Confirm organism/species

## During Research

- [ ] **Multi-Database Coverage**:
  - [ ] Query primary database for data type
  - [ ] Query secondary/fallback databases
  - [ ] Cross-reference results

- [ ] **Multi-Hop Chains**:
  - [ ] Follow ID cross-references
  - [ ] Don't stop at first result
  - [ ] Track 5-10+ tool calls per question

- [ ] **Failure Handling**:
  - [ ] Retry failed tools (wait 2-5 seconds)
  - [ ] Try fallback tools
  - [ ] Document unavailable data

## Report Quality

- [ ] **Citation Requirements**:
  - [ ] Every fact has source attribution
  - [ ] Tool names included in citations
  - [ ] Dates/versions noted where relevant

- [ ] **Evidence Grading**:
  - [ ] T1 (★★★): Mechanistic evidence
  - [ ] T2 (★★☆): Functional evidence
  - [ ] T3 (★☆☆): Association evidence
  - [ ] T4 (☆☆☆): Mention/review evidence

- [ ] **Mandatory Completeness**:
  - [ ] All sections exist (even if "data unavailable")
  - [ ] No placeholder text remains
  - [ ] Synthesis sections included

## Quality Metrics

| Metric | Minimum | Good | Excellent |
|--------|---------|------|-----------|
| **Tool calls** | 5+ | 15-30 | 30+ |
| **Databases queried** | 2+ | 5+ | 10+ |
| **Evidence graded** | Key claims | Most claims | All claims |
| **Sources cited** | Major facts | All facts | All with links |

## Common Mistakes to Avoid

- [ ] **Don't** stop after first tool returns data
- [ ] **Don't** skip fallback when primary fails
- [ ] **Don't** forget to disambiguate before research
- [ ] **Don't** show search process (show results only)
- [ ] **Don't** leave sections empty (note "unavailable")
- [ ] **Don't** mix evidence tiers without labeling

## Quick Fallback Reference

| Tool Type | Primary → Fallback |
|-----------|-------------------|
| Literature | PubMed → EuropePMC → OpenAlex |
| Expression | GTEx → HPA |
| Protein | UniProt → Proteins API |
| Compound | PubChem → ChEMBL |
| Disease | OpenTargets → ClinVar + GWAS |
| Variants | gnomAD → ClinVar |
| Structure | PDB → AlphaFold |
