# Research Loop Protocol

The iterative cycle that makes deep research work. Each pass through the loop reads the current state, identifies gaps, searches, analyzes, and updates the state.

## The Cycle

```
Read research_state.json (or initialize if first iteration)
  |
  v
Identify gaps: what entities are unresolved? what connections unchecked?
  |
  v
Plan searches: which tools, which queries? (check health first)
  |
  v
Execute: run 5-10 tool calls via grep_tools/find_tools -> get_tool_info -> execute_tool
  |
  v
Analyze: extract entities, identify connections, form hypotheses
  |
  v
Update research_state.json: add entities, connections, hypotheses, tools_used
  |
  v
Update report file: populate next section with findings
  |
  v
Check completion criteria -> if not met, continue cycle
```

## Research State Schema

File: `research_state.json` in the user's output directory (same as report).

```json
{
  "question": "Original user question",
  "started": "2026-03-28T10:00:00Z",
  "iteration": 3,
  "status": "investigating",

  "entities": {
    "genes": {
      "BRCA1": {
        "ids": {"ensembl": "ENSG00000012048", "uniprot": "P38398", "kegg": "hsa:672"},
        "source": "OpenTargets",
        "tier": "T1",
        "connections": ["homologous_recombination", "olaparib", "breast_cancer"],
        "metadata": {"score": 0.95, "description": "DNA repair protein"}
      }
    },
    "drugs": {},
    "pathways": {},
    "diseases": {},
    "variants": {},
    "companies": {},
    "trials": {}
  },

  "connections": [
    {
      "from": "BRCA1",
      "to": "olaparib",
      "relationship": "synthetic_lethality_target",
      "via": "homologous_recombination_deficiency",
      "evidence_tier": "T1",
      "sources": ["OpenTargets", "ClinicalTrials"],
      "hops": 2
    }
  ],

  "hypotheses": [
    {
      "claim": "PTEN loss may predict resistance to PARP inhibitors in BRCA1-mutant tumors",
      "status": "investigating",
      "evidence_for": ["PMID:30297858"],
      "evidence_against": [],
      "next_search": "ClinVar PTEN + FAERS olaparib"
    }
  ],

  "gaps": [
    {
      "what": "No pharmacogenomics data for olaparib",
      "why": "PharmGKB tool returned no results",
      "alternatives_tried": ["ClinVar", "PubMed"]
    }
  ],

  "tools_used": [
    {"tool": "PubMed_search_articles", "query": "BRCA1 PARP inhibitor", "result_count": 15, "tier": "T2", "iteration": 1},
    {"tool": "OpenTargets_get_associated_drugs", "query": "ENSG00000012048", "result_count": 8, "tier": "T1", "iteration": 2}
  ]
}
```

## Iteration Strategy

| Iteration | Focus | Typical tools |
|-----------|-------|---------------|
| 1 | Broad search: identify entities, get overview | PubMed, OpenTargets, OpenAlex, find_tools |
| 2 | Resolve IDs, deepen entity profiles | UniProt, Ensembl, ChEMBL, KEGG, STRING |
| 3 | Cross-reference: map connections between entities | KEGG_link_entries, ClinicalTrials, FAERS |
| 4 | Validate hypotheses, fill gaps | ClinVar, CIViC, targeted PubMed, WebSearch |
| 5+ | Synthesize: grade evidence, write report | No new tool calls; analysis and writing |

Fewer iterations for simple queries. More for complex multi-entity questions.

## Completion Criteria

Stop iterating when ALL of:

1. **Entities resolved** -- all discovered entities have at least one database ID
2. **Hypotheses resolved** -- no hypotheses in "investigating" status (all confirmed, refuted, or documented as inconclusive)
3. **Cross-references checked** -- connection types from cross-reference.md checked for all relevant entity pairs
4. **Gaps documented** -- each gap lists what was tried and why it failed
5. **Report populated** -- all sections of the output report have content (or explicit "no data found")

## Health-Aware Planning

Before each iteration, check tool availability:

```
For each planned tool call:
  1. Check ToolHealthCache().is_live(tool_name)
  2. If live -> proceed
  3. If broken -> use fallback from follow-the-data.md
  4. If unknown (no cache entry) -> try it, but have fallback ready
  5. Log tool health status in gaps if it blocked a search
```

Never skip a research dimension because a tool is broken. Use fallbacks.
