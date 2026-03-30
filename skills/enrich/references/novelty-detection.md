# Novelty Detection

The value of `/enrich` is not fact-checking — it's finding what the original report missed. Novel insights are what make the output publishable and what land Chris consulting business.

## What Counts as Novel

A finding is novel if ALL of:

1. **Not in the original report** — the input text does not mention it
2. **Supported by evidence** — at least T2 quality from 2+ databases
3. **Non-obvious** — a domain expert reading the original wouldn't immediately think of it
4. **Actionable** — it has implications for investment, clinical development, or competitive strategy

A finding that is merely absent from the report but well-known in the field is NOT novel — it's a gap. Novel means the connection itself is unexpected or under-recognized.

## Classification

| Label | Bar | Example |
|-------|-----|---------|
| **NOVEL INSIGHT** | Cross-domain connection with T2+ evidence | "GLP-1R is expressed in hippocampus; 3 Alzheimer's trials are testing semaglutide" |
| **NOVEL IP** | Genuinely new hypothesis with multi-hop evidence chain | "Exendin-4 (Gila monster venom) → GLP-1R agonism → neuroprotection. No one has screened other reptile venoms for GLP-1R activity — this is a white space for natural product drug discovery." |
| **MARKET SIGNAL** | Business-relevant finding from regulatory/financial data | "Competitor X filed SEC 10-K showing $200M allocated to GLP-1 pipeline — direct competitive threat not mentioned in report" |
| **GAP** | Missing from report but well-known | "Report doesn't mention FAERS safety data for semaglutide — 12,000 adverse event reports exist" |

## How to Find Novel Connections

### Cast wide first

Don't search for what the report is about. Search for what it's NOT about but should be:

- If the report is about a drug, search for the drug's targets, then search for those targets in unrelated diseases
- If the report is about a disease, search for the disease's pathways, then search for natural products that modulate those pathways
- If the report is about a company, search for every drug in their pipeline, then check what OTHER companies are pursuing the same targets

### Cross-domain strategies

| Starting entity | Cross to | How |
|----------------|----------|-----|
| Drug mechanism | Natural products with same mechanism | Search compound databases for pathway modulators |
| Disease pathway | Other diseases sharing the pathway | KEGG_link_entries, OpenTargets disease associations |
| Gene target | Agricultural/plant biotech | Search for plant orthologs, crop science applications |
| Clinical trial | Competitor pipelines | ClinicalTrials by condition, SEC filings by keyword |
| Safety signal | Drug repurposing clue | FAERS adverse events that suggest off-target activity → therapeutic opportunity |
| Company pipeline | Supply chain / manufacturing | SEC filings mentioning CDMO relationships, ingredient sourcing |

### The venom → GLP-1 example

This is the kind of connection that makes a report publishable:

1. Start: semaglutide (drug for obesity)
2. Find: exendin-4 was the first GLP-1 agonist, isolated from Heloderma suspectum (Gila monster) venom
3. Search: other reptile/amphibian venoms → peptide libraries → GLP-1R binding
4. Discover: several venom peptides have incretin-like activity, none in clinical development
5. Novel IP: "Natural product GLP-1 analogs from venoms represent an unexplored drug discovery space"
6. Evidence chain: [T2: PubMed exendin-4 discovery] → [T4: STRING GLP-1R interactions] → [T1: ClinicalTrials showing no venom-derived GLP-1 trials]

## Evidence Chain Format

Every novel finding must include a traceable chain:

```
[Entity A] → [Relationship] → [Entity B] → [Relationship] → [Entity C]
Sources: [T1: tool_name, ID], [T2: tool_name, PMID:...]
Implication: [what this means commercially or clinically]
```

The chain is the proof. Without it, the insight is speculation.

## Append to Research Notes

```markdown
## Novel Findings

### NOVEL INSIGHT: GLP-1R in Alzheimer's
GLP-1R is expressed in hippocampal neurons. 3 Phase 2 trials
are testing semaglutide for cognitive decline in AD patients.
Chain: semaglutide → GLP-1R → hippocampus → neurodegeneration → AD trials
[T1: ClinicalTrials NCT04777396] [T2: PMID:31862450]
Implication: Novo Nordisk may be positioning for CNS indications.
Check SEC filings for strategic language about neurodegeneration.

### NOVEL IP: Unexplored venom-derived GLP-1 agonists
(see chain above)
Implication: white space for natural product drug discovery program.
```
