# General Usage Strategies

Use these strategies ONLY when no specialized skill matches the user's query. See SKILL.md routing table first.

## Core Principles

1. **Search widely** — run multiple tool discovery queries with synonyms
2. **Query multiple databases** — cross-reference across sources
3. **Multi-hop persistence** — chain 5-10 tool calls; one is rarely enough
4. **Never give up** — if a tool fails, try alternatives
5. **Comprehensive reports** — cite sources, grade evidence
6. **English-first queries** — translate to English for tools, respond in user's language

---

## Strategy 0: Clarify Before Acting

Ask clarifying questions when:
- Vague entity ("Research cancer" → which type?)
- Ambiguous name ("JAK" → JAK1/2/3? Inhibitor?)
- Unclear scope ("Look into metformin" → safety? repurposing? profile?)
- Multiple interpretations ("ACE" → gene? inhibitors? ACE2?)

Do NOT ask when specific enough: "What is the structure of EGFR kinase domain?"

Checklist: confirm **entity**, **species** (default human), **scope**, **output format**.

---

## Strategy 1: Exhaustive Tool Discovery

Run at least 6 queries in parallel:
1. Main topic: `find_tools(query="[topic]")`
2. Synonym: `find_tools(query="[synonym]")`
3. Another synonym: `find_tools(query="[synonym2]")`
4. Known database: `find_tools(query="[database name]")`
5. Data type: `find_tools(query="[data type]")`
6. Full use case: `find_tools(query="[full description]")`

**Actually RUN these**, don't just describe them.

---

## Strategy 2: Multi-Hop Tool Chains

Common patterns:

| Pattern | Flow | Example |
|---------|------|---------|
| **ID Resolution** | Name → ID → Data → Related Data | gene_name → Ensembl → UniProt → structure |
| **Cross-DB Enrichment** | Primary → Cross-reference → Enriched | drug → PubChem CID + ChEMBL ID → properties + bioactivity |
| **Network Expansion** | Seed → Connected → Details | gene → interactions → interactor diseases |
| **Literature + Data** | Annotations → Literature → Synthesis | disease → genes + drugs → papers → report |

Rules: Don't stop at first result. Follow cross-references. 5-10 calls is normal. Track all IDs.

---

## Strategy 3: Query Multiple Databases

| Data Type | Primary | Secondary | Tertiary |
|-----------|---------|-----------|----------|
| Protein info | UniProt | Proteins API | NCBI Protein |
| Gene expression | GTEx | Human Protein Atlas | ArrayExpress |
| Drug targets | ChEMBL | DGIdb | OpenTargets |
| Variants | gnomAD | ClinVar | OpenTargets |
| Literature | PubMed | Europe PMC | OpenAlex |
| Pathways | Reactome | KEGG | WikiPathways |
| Structures | RCSB PDB | PDBe | AlphaFold |
| Disease assoc. | OpenTargets | ClinVar | GWAS Catalog |

Merge: collect all, note sources, handle conflicts, prefer curated data.

---

## Strategy 3.1: Full-Text Literature Search

For body-only terms (rsIDs, figure refs, supplementary tables) that don't appear in abstracts:

1. `PMC_search_papers` — NCBI PMC indexes full text
2. `EuropePMC_search_articles` with `require_has_ft=true` + `fulltext_terms=[...]`
3. `EuropePMC_get_fulltext_snippets` — confirm term is in paper
4. `CORE_get_fulltext_snippets` — PDF scan fallback

---

## Strategy 4: Disambiguation

Before research, establish canonical IDs:
- **Genes**: Symbol → UniProt, Ensembl, NCBI Gene, ChEMBL target
- **Compounds**: Name → PubChem CID, ChEMBL ID, SMILES
- **Diseases**: Name → EFO ID, ICD-10, UMLS CUI

Gather synonyms. Detect naming collisions. Confirm species (default: human).

---

## Strategy 5: Failure Handling

```
Primary tool → fails → retry → fails → fallback #1 → fails → fallback #2 → document as unavailable
```

Common fallbacks:
- PubMed → EuropePMC → OpenAlex
- GTEx → Human Protein Atlas
- PubChem → ChEMBL → SMILES-based
- UniProt → Proteins API

Also try: synonyms, broader terms, different databases.

---

## Strategy 6: Comprehensive Reports

1. Create report structure first, then fill progressively
2. Every fact needs a source citation
3. Grade evidence: ★★★ (mechanistic) → ★★☆ (functional) → ★☆☆ (association) → ☆☆☆ (review)
4. All sections must exist, even if "data unavailable"
5. Quality target: 15-30+ tool calls, all sections filled

---

## Strategy 7: Defer to Specialized Skills

If you realize mid-research that a specialized skill matches: STOP general strategies, ROUTE to the skill.

---

## Strategy 8: Parallel Execution

Run independent queries simultaneously:
- Different databases for same entity → parallel
- Tool B needs output from Tool A → sequential

---

## Strategy 9: Completeness Check

After gathering data, ask: "What's still missing?"
- All identifiers? Core data? Context? Relationships? Variants? Evidence? Literature? Gaps documented?
- Stop when: all aspects addressed, multiple sources queried, gaps documented.

---

## Strategy 10: English-First Queries

All tool calls use English. Translate non-English input before querying. Respond in user's language.

---

## Troubleshooting

| Problem | Fix |
|---------|-----|
| Tool not found | Search synonyms via find_tools |
| Empty results | Try synonyms, alternative databases, check spelling |
| Conflicting data | Note sources, prefer curated, document conflict |
| Incomplete | Search for more tools, query more databases, expand via literature |
