---
name: tooluniverse-deep-research
description: >-
  Iterative research agent that thinks across databases. Searches, analyzes,
  hypothesizes, cross-references, and iterates until the picture is complete.
  Produces evidence-graded reports with citations. Use for multi-hop scientific
  questions, connection mapping (gene-pathway-drug-trial), comprehensive reviews
  spanning multiple domains, or any query requiring cross-database reasoning.
  NOT for single tool lookups (/tooluniverse) or literature-only reviews
  (/tooluniverse-literature-deep-research).
---

# Deep Research

Iterative, entity-driven research across 1,900+ life-science tools. Not a tool finder -- a research agent that thinks.

## When to Use

- "Deep research on [topic]"
- "Map the connections between [X] and [Y]"
- "What connects [gene] to [disease]?"
- "Comprehensive analysis of [entity]"
- "Investigate [multi-entity question]"
- "Cross-reference [drug] with [targets/trials/safety]"
- Any question requiring data from 3+ databases
- Any question where the answer depends on connections between entities

## When NOT to Use

| Need | Use instead |
|------|-------------|
| Find a tool | /tooluniverse |
| Literature review | /tooluniverse-literature-deep-research |
| Disease profile | /tooluniverse-disease-research |
| Drug profile | /tooluniverse-drug-research |
| Target profile | /tooluniverse-target-research |
| Company intelligence | /company-research |

If the question fits neatly in one domain, use the domain skill. Use deep research when the question spans domains or requires cross-referencing.

---

## Core Workflow

### Phase 1: Parse and Plan

1. **Extract entities** from the user's question: genes, drugs, diseases, pathways, companies, variants
2. **Classify question type**: treatment landscape, connection mapping, mechanism investigation, competitive analysis, safety review
3. **Check tool health** before calling any tool:
   - `ToolHealthCache().is_live(tool_name)` -- skip broken tools, note in gaps
   - If broken, search catalog for alternatives in the same category
   - If unknown (no cache entry), try it but note the result
4. **Create output files**:
   - `research_state.json` -- working memory (see [references/research-loop.md](references/research-loop.md))
   - `{topic}_deep_research.md` -- report file initialized with template from Output Format below

### Phase 2: Search the Full Tool Ecosystem

You have 1,900+ tools. You cannot predict which ones matter. Search the catalog for every entity, call everything relevant.

**For each entity, search the catalog exhaustively**:

```
grep_tools(pattern="ENTITY_NAME")              -- tools mentioning this entity
grep_tools(pattern="ENTITY_TYPE")              -- tools for this type (gene, drug, disease...)
grep_tools(pattern="RELATED_CONCEPT")          -- broader concept (safety, pathway, trial...)
find_tools(query="natural language question")   -- semantic search catches what keywords miss
list_tools(mode="by_category")                 -- browse categories for tools search missed
```

Run MULTIPLE searches per entity with different keywords and synonyms. A drug search should hit: the drug name, "drug safety", "adverse event", "clinical trial", "drug label", "pharmacology", "drug interaction", "drug approval", etc. Each search may surface different tools.

**For every tool that comes back relevant**:

```
1. get_tool_info(tool_names="tool_name")  -- get exact parameter schema (NEVER skip)
2. execute_tool(tool_name="tool_name", arguments={...})
```

**Ordering**: Work T1 tools first (regulatory/curated sources surface in categories like `fda_drug_label`, `clinical_trials`, `opentarget`), then T2 (literature: `pubmed`, `crossref`), then T3/T4.

**The expanding frontier**: Results from tool calls reveal new entities. Each new entity triggers its own catalog search. A gene query returns drug names -> search the catalog for those drugs -> drug results mention clinical trials -> search for trial tools -> trial data names a company -> search for SEC/FDA tools. This is how you find SEC EDGAR tools when starting from a gene. You don't need to predict the path.

**Scope**: Don't count tool calls. Count coverage. Stop when:

- Every discovered entity has been searched in the catalog
- Every relevant tool returned by searches has been called
- No new entities are emerging from results

See [references/follow-the-data.md](references/follow-the-data.md) for the entity exploration table, search strategies per entity type, and fallback chains.

### Phase 3: Deepen and Cross-Reference

This is where the thinking happens.

1. **Resolve entity IDs** across databases (see [references/entity-resolution.md](references/entity-resolution.md))
2. **Map connections** between all discovered entities (see [references/cross-reference.md](references/cross-reference.md))
3. **Form hypotheses**: "Gene X is in pathway Y which is targeted by drug Z -- does Z have trials for the disease?"
4. **Validate hypotheses** with targeted searches: ClinicalTrials, FAERS, ClinVar, PubMed
5. **Follow unexpected connections** -- if the data leads somewhere surprising, chase it (see [references/follow-the-data.md](references/follow-the-data.md))

Update research_state.json after each sub-step. Update the report progressively.

### Phase 4: Synthesize

1. **Grade all evidence** using the T1-T4 framework (see [references/evidence-grading.md](references/evidence-grading.md))
2. **Resolve hypotheses**: mark each as confirmed, refuted, or inconclusive with supporting evidence
3. **Document gaps**: what couldn't be found and why
4. **Write executive summary**: 3-5 sentences capturing the key findings
5. **Finalize report**: ensure every claim is cited, every table has a Source column

---

## Output Format

Create `{topic}_deep_research.md` at the start. Populate progressively.

```markdown
# Deep Research Report: {Topic}

**Generated**: {date}
**Question**: {original user question}
**Iterations**: {N}

---

## Executive Summary

{3-5 sentences: key findings, major connections discovered, confidence level}

---

## Entity Map

| Entity | Type | Key IDs | Evidence | Source |
|--------|------|---------|----------|--------|

---

## Connections

| From | To | Relationship | Via | Tier | Source |
|------|----|-------------|-----|------|--------|

---

## Key Findings

### {Theme 1}

{Findings with inline citations: [T1: tool_name, ID]}

### {Theme 2}

...

---

## Hypotheses

| Claim | Status | Evidence For | Evidence Against |
|-------|--------|-------------|-----------------|

---

## Data Gaps

| What | Why | Alternatives Tried |
|------|-----|--------------------|

---

## Sources

| Tool | Query | Items | Tier | Iteration |
|------|-------|-------|------|-----------|
```

---

## Iteration

This skill describes one research cycle. For complex questions, iterate:

1. Run the skill once -- it performs Phase 1-4
2. Read research_state.json to see what's been found and what gaps remain
3. If gaps or unresolved hypotheses remain, continue searching
4. Each pass adds to the state file and report -- never overwrites

See [references/research-loop.md](references/research-loop.md) for the full protocol, state file schema, and completion criteria.

---

## Key Principles

1. **Domain-agnostic**: Follow entities wherever they lead. Don't pre-decide the domain.
2. **Evidence-graded**: Every claim cites its source and tier. No ungraded findings.
3. **Health-aware**: Check tool health before planning. Use fallbacks for broken tools.
4. **Hypothesis-driven**: Don't just collect data -- form and test hypotheses about connections.
5. **Progressive disclosure**: Report grows as research progresses. User sees findings, not search process.
6. **English queries**: All tool calls use English. Respond in the user's language.

---

## Reference Docs

Load these on demand when you need the detailed protocol:

| Document | When to load |
|----------|-------------|
| [references/research-loop.md](references/research-loop.md) | Starting research: state file schema, iteration strategy, completion criteria |
| [references/entity-resolution.md](references/entity-resolution.md) | Resolving entity IDs across databases, handling ambiguous names |
| [references/cross-reference.md](references/cross-reference.md) | Mapping connections between entities, multi-hop patterns |
| [references/evidence-grading.md](references/evidence-grading.md) | Grading claims, tool-to-tier mapping, citation format |
| [references/follow-the-data.md](references/follow-the-data.md) | Deciding what to explore next for each entity type, fallback chains |
