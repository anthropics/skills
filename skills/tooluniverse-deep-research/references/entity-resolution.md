# Entity Resolution

The same entity has different identifiers across databases. Resolve them before cross-referencing.

## The Problem

TP53 is one gene with many IDs:

| Database | Identifier |
|----------|-----------|
| HGNC symbol | TP53 |
| Ensembl | ENSG00000141510 |
| UniProt | P04637 |
| NCBI Gene | 7157 |
| KEGG | hsa:7157 |
| STRING | 9606.ENSP00000269305 |

Without resolving these, you can't connect a KEGG pathway result to a STRING interaction result.

## Resolution Tools

| From | To | Tool | Example |
|------|----|------|---------|
| Gene symbol | Ensembl ID | `ensembl_lookup_gene` | BRCA1 -> ENSG00000012048 |
| Ensembl ID | KEGG/UniProt | `KEGG_convert_ids` | ENSG -> hsa:672 / up:P38398 |
| Any prefix:ID | Provider URLs | `Bioregistry_resolve_reference` | uniprot:P04637 -> all providers |
| Drug name | PubChem CID | `PubChem_get_CID_by_compound_name` | aspirin -> 2244 |
| Drug name | ChEMBL ID | `ChEMBL_search_compounds` | aspirin -> CHEMBL25 |
| Disease name | EFO ID | `OSL_get_efo_id_by_disease_name` | breast cancer -> EFO_0000305 |
| Disease name | ICD/SNOMED | `icd_search_codes` / `snomed_search_concepts` | -- |
| Gene symbol | STRING ID | `STRING_get_network` | TP53 -> returns stringId |

## Resolution Strategy

1. **Start with what the user gave you** -- gene symbol, drug name, disease name
2. **Resolve to the most connected ID** -- Ensembl for genes, EFO for diseases, ChEMBL for drugs
3. **Store all IDs in the entity record** -- `ids: {"ensembl": "ENSG...", "uniprot": "P...", "kegg": "hsa:..."}`
4. **Resolve lazily** -- only convert IDs when you need them for a specific tool call

## Disambiguation

When a name is ambiguous:

| Ambiguity | Strategy |
|-----------|----------|
| ACE (gene vs inhibitor class vs ACE2) | Check query context; if unclear, ask user |
| JAK (JAK1/JAK2/JAK3/TYK2) | Search all; report which ones are relevant |
| Mercury (element vs brand vs planet) | Context: biomedical = element/toxicology |
| IL-6 (gene vs protein vs pathway) | Usually means the gene/protein; pathway = "IL-6 signaling" |

Rules:

- **Never guess silently** -- if ambiguous with no context, ask the user
- **Store the disambiguation** -- record which interpretation was chosen in research_state.json
- **Check multiple** -- when feasible, query all interpretations and let results clarify

## ID Acceptance by Major Tools

| Tool Family | Accepts |
|-------------|---------|
| OpenTargets | Ensembl gene IDs, EFO disease IDs, ChEMBL drug IDs |
| KEGG | KEGG IDs (hsa:7157), converts from/to UniProt/NCBI |
| STRING | Gene symbols, Ensembl protein IDs, with species taxon |
| ChEMBL | ChEMBL IDs, compound names, SMILES |
| UniProt | Accession numbers (P04637), gene names |
| ClinVar | Gene symbols, variant HGVS notation, rsIDs |
| PubChem | CIDs (numeric), compound names, SMILES, InChI |
| ClinicalTrials | Free-text disease/drug names, NCT IDs |
| FAERS | Drug brand/generic names (free text) |
