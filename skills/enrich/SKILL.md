---
name: enrich
description: >-
  Takes an existing biotech report, fact-checks every claim against 1,900+
  scientific databases, discovers novel cross-domain insights, and outputs a
  publishable Tufte-style PDF with full evidence traceability. Zero hallucination
  tolerance. Every fact traceable to its source. LLM designs the document layout,
  picks fonts, and visually inspects every page before delivery.
---

# /enrich

Paste a report. Get back a publishable, fact-checked, insight-enriched PDF.

## When to Use

- "Enrich this report" / "Make this novel" / "Improve this analysis"
- Pasted biotech/pharma report text with request to enhance
- "Fact-check and find what they missed"
- Any existing report that needs cross-domain insights and traceable evidence

## Input

The user pastes a ~500-3000 word report (company analysis, drug profile, disease review, market report, competitive landscape) and asks for enrichment.

## Workflow

Five phases. Each appends to `research_notes.md` — the brain thinks in prose, not data structures.

### Phase 1: Parse

Read the report sentence by sentence. Extract:

- **Claims**: every factual assertion
- **Entities**: genes, drugs, diseases, pathways, companies, trials, natural products
- **Relationships**: "X targets Y", "A causes B"
- **Gaps**: what the report doesn't mention but should

Append to `research_notes.md`. See [references/fact-checking.md](references/fact-checking.md).

### Phase 2: Fact-Check

Verify every claim against databases. For each:

1. Search the tool catalog for relevant databases (`grep_tools`, `find_tools`)
2. `get_tool_info` then `execute_tool` for each relevant tool
3. Verify with 2+ independent sources
4. Classify: Verified / Corrected / Unverifiable / Misleading

**Zero-tolerance**: no T3/T4-only claims presented as fact. See [references/fact-checking.md](references/fact-checking.md).

### Phase 3: Deep Research

Find what the report missed. This creates the novel value.

**First iteration: cast wide.** Don't search narrowly for the report's thesis. Search broadly — what databases even exist for these entities? What adjacent fields touch this topic? Use `find_tools` with broad concepts, `grep_tools` with entity names, `list_tools(mode="by_category")` to discover entire categories of tools. The goal is to be surprised.

**Then follow the expanding frontier**: results reveal new entities, each triggers new catalog searches. A drug leads to targets, targets lead to pathways, pathways lead to other diseases, diseases lead to trials, trials lead to companies, companies lead to SEC filings.

Hunt for cross-domain connections, market signals, mechanism overlaps, and safety gaps. See [references/novelty-detection.md](references/novelty-detection.md) for cross-domain search strategies.

### Phase 4: Classify Findings

Label each finding: VERIFIED, CORRECTED, NOVEL INSIGHT, NOVEL IP, or MARKET SIGNAL. See [references/novelty-detection.md](references/novelty-detection.md) for definitions and evidence bars.

### Phase 5: Compose PDF

Design and typeset the report. No fixed template — the content determines the layout.

**Toolchain**: `tufte-swiss.sty` + `lualatex` (NEVER pdflatex or xelatex).

```bash
cp ~/.claude/skills/tufte-swiss-typography/assets/tufte-swiss.sty ./
cp ~/.claude/skills/tufte-swiss-typography/assets/tufte-swiss-grid.lua ./
lualatex --interaction=nonstopmode report.tex
```

The LLM designs the layout, picks fonts from `fc-list`, and decides what gets callout boxes vs tables vs margin notes vs prose. Non-negotiable: asymmetric Tufte margins (text left, evidence right), margin citations with tier badges, and `lualatex` compilation.

**Visual QA loop**: Read every page of the compiled PDF as an image. Fix overlapping text, broken figures, colliding margin notes, bad page breaks. Recompile and re-inspect until every page passes.

See [references/composition.md](references/composition.md) for tufte-swiss primitives, font selection, Tufte's design principles, and visual QA checklist.

## Output

- `report.pdf` — the publishable document
- `research_notes.md` — the brain's working memory (full audit trail)

## Evidence Standards

| Tier | Sources | Reliability |
|------|---------|-------------|
| T1 | FDA, SEC, ClinicalTrials.gov, FAERS, OMIM | Regulatory / official |
| T2 | PubMed, Crossref, OpenAlex (peer-reviewed) | Validated |
| T3 | BioRxiv, MedRxiv, WebSearch, Wikipedia | Unvalidated |
| T4 | STRING, text-mining, pathway inference | Computational |

Novel insights require minimum T2. Claims presented as fact require minimum T1 or T2.

## Reference Docs

| Document | Load when |
|----------|----------|
| [references/fact-checking.md](references/fact-checking.md) | Phase 2: claim extraction, verification protocol, zero-tolerance rule |
| [references/novelty-detection.md](references/novelty-detection.md) | Phase 3-4: what counts as novel, cross-domain strategies, evidence chains |
| [references/composition.md](references/composition.md) | Phase 5: tufte-swiss primitives, font selection, layout patterns, visual QA |
