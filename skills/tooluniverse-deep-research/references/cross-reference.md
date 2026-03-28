# Cross-Reference Patterns

Finding connections between entities across databases. The value of deep research is not any single query -- it's the connections between results.

## Connection Types

| Relationship | Databases | What it means |
|-------------|-----------|---------------|
| gene -- pathway | KEGG, Reactome, WikiPathways | Gene participates in this biological process |
| gene -- disease | OpenTargets, ClinVar, GWAS | Gene is associated with disease (causal or risk) |
| drug -- target | ChEMBL, OpenTargets, DrugBank | Drug binds/modulates this protein target |
| drug -- trial | ClinicalTrials | Drug is being tested for this indication |
| drug -- safety | FAERS, OpenFDA | Adverse events reported for this drug |
| drug -- approval | FDA OrangeBook, OpenFDA | Drug approved for this indication |
| protein -- protein | STRING, humanbase, IntAct | Proteins physically or functionally interact |
| variant -- disease | ClinVar, CIViC, GWAS | Variant affects disease risk or drug response |
| variant -- drug | PharmGKB, CIViC | Variant predicts drug response |
| pathway -- drug | KEGG, Reactome + OpenTargets | Drugs targeting genes in this pathway |
| company -- drug | SEC EDGAR, ClinicalTrials | Company develops/sponsors this drug |
| publication -- entity | EuropePMC annotations, Crossref | Paper mentions/studies this entity |

## Multi-Hop Patterns

### Gene -> Pathway -> Drug (3 hops)

```
1. KEGG_link_entries(source="hsa:GENE_ID", target="pathway")  -> pathway IDs
2. KEGG_link_entries(source="PATHWAY_ID", target="drug")       -> KEGG drug IDs
3. ChEMBL or OpenTargets to get drug details
```

Use case: "What drugs target the same pathway as gene X?"

### Disease -> Gene -> Drug -> Trial (4 hops)

```
1. OpenTargets: disease -> associated genes (sorted by score)
2. OpenTargets or ChEMBL: gene -> drugs targeting it
3. ClinicalTrials: drug + disease -> active trials
4. FAERS: drug -> safety profile
```

Use case: "What treatments exist for disease X, and what's their safety profile?"

### Drug -> Target -> Pathway -> Related Diseases (4 hops)

```
1. ChEMBL: drug -> protein targets
2. KEGG_link_entries: target gene -> pathways
3. KEGG_link_entries: pathway -> linked diseases
4. OpenTargets: validate disease-gene associations
```

Use case: Drug repurposing -- "What other diseases might drug X treat?"

### Variant -> Gene -> Protein -> Interactions (3 hops)

```
1. ClinVar: variant -> gene + clinical significance
2. UniProt: gene -> protein structure + function
3. STRING: protein -> interaction partners
```

Use case: "What is the functional impact of this variant?"

## Connection Scoring

Weight each connection by:

1. **Evidence tier** -- T1 connections are stronger than T4
2. **Source count** -- Connection found in 3 databases > found in 1
3. **Directness** -- Direct relationship (drug binds target) > indirect (drug targets pathway containing gene)
4. **Recency** -- Recent publications/trials > older data

Record in research_state.json:

```json
{
  "from": "BRCA1",
  "to": "olaparib",
  "relationship": "synthetic_lethality_target",
  "via": "homologous_recombination_deficiency",
  "evidence_tier": "T1",
  "sources": ["OpenTargets", "ClinicalTrials", "FDA"],
  "hops": 2
}
```

## When to Stop Cross-Referencing

- All discovered entities have been checked against all relevant connection types
- No new entities are being discovered (convergence)
- Remaining unchecked connections are T4-only with no supporting evidence
- You've documented gaps for connections you couldn't verify
