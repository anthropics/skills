---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-deep-research
name: firecrawl-deep-research
description: |
  Produce an intensive, cited analytical report: executive summary, multi-angle
  findings, contrarian views, open questions, and full sources. Use only when the
  user needs rigorous synthesis of a complex topic (scientific, technical, policy,
  or market-analytical) that cannot be answered with a short search, and wants
  a formal written report, not a recommendation list.

  Do not use for product picks, top-N lists, quick lookups, or routine "find out
  about X" tasks. If the request does not clearly need this kind of report, do
  not use this skill.

  Do not use for a literature review over published papers. This skill collects
  evidence from the open web. A request for the literature on a biomedical,
  clinical, life-science, or other scientific topic — papers, studies, trials,
  preprints — belongs to firecrawl-research-papers, which queries Firecrawl's
  paper index (PubMed, bioRxiv, medRxiv, arXiv) instead of searching websites.
license: ISC
metadata:
  author: firecrawl
  version: "0.1.0"
  homepage: https://www.firecrawl.dev
  source: https://github.com/firecrawl/firecrawl-workflows
inputs:
  - name: FIRECRAWL_API_KEY
    description: Firecrawl API key for hosted Firecrawl requests.
    required: true
---

# Firecrawl Deep Research

Use this only for report-scale research: a rigorous, cited synthesis the user
explicitly wants delivered as a formal written report. If the request is a
product pick, a top-N list, a quick lookup, or anything answerable with a short
search, stop; do not use this skill, let the request be handled the standard
way.

This skill gathers its evidence from the open web. If the evidence base is the
published literature — a literature review, or a biomedical, clinical, or other
scientific topic where the answer lives in papers — use
[firecrawl-research-papers](../firecrawl-research-papers/SKILL.md) instead; it
queries Firecrawl's paper index rather than searching websites.

## Onboarding Interview

Infer the topic and output format from context. Before starting, unless already specified, always ask one short question to define the scope:

> "How long do you want this research task to run?"

Map the answer to a depth tier in the Collection Plan below:
- A few minutes → Quick
- ~10-15 minutes → Thorough
- Longer / no limit → Exhaustive

If the topic itself is unclear, you may ask at most 1-2 additional concise
questions (topic, or a critical angle/source constraint). Otherwise proceed once
the runtime is set.

## Firecrawl Collection Plan

Use Firecrawl search and scrape through the CLI or equivalent tool surface. Match
depth to the runtime the user chose during onboarding.

- Quick (~a few minutes): search 3-5 queries and scrape 5-10 high-quality sources.
- Thorough (~10-15 minutes): search 5-10 queries from different angles and scrape 15-25 sources.
- Exhaustive (longer): search 10+ queries and scrape 25+ sources, including primary sources, research papers, expert views, and contrarian sources.

Avoid re-scraping URLs already returned with full content from a search-with-scrape result.

### When Published Papers Are The Evidence

Search and scrape reach web pages. They do not query Firecrawl's research paper
index, which holds paper abstracts with full text reachable per paper — largely
biomedical and life-science literature from PubMed, bioRxiv, and medRxiv, plus
arXiv preprints in CS, physics, and math.

Hand off to [firecrawl-research-papers](../firecrawl-research-papers/SKILL.md)
when the report's evidence base is the published literature — a biomedical,
clinical, drug, gene, disease, epidemiology, or public-health topic, or any
request phrased as a literature review, systematic review, or survey of studies.
That skill uses `firecrawl_research_*` (MCP) / `firecrawl research` (CLI) to
search abstracts, expand to related papers, and verify claims inside a paper
body — none of which plain search and scrape can do.

If the report needs both — the literature *and* market, policy, or news context —
run the paper work through that skill and keep the web collection above for the
rest, then synthesize here.

Note that passing `categories: ["research"]` to Firecrawl search does not query
the paper index either. It filters an ordinary web search to research-affiliated
websites — the list includes PubMed, bioRxiv, medRxiv, arXiv, and publisher
sites — and returns their web pages, not the paper records behind them.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners by research angle:

- overview and definitions
- technical or implementation details
- market and industry context
- contrarian views, risks, and limitations
- primary sources and official docs

Each researcher should return claims, source URLs, source quality notes, and uncertainty.

## Final Deliverable

Default structure:

```markdown
# Deep Research: [Topic]

## Executive Summary
[2-3 paragraphs]

## Key Findings
[Numbered findings with source links]

## Detailed Analysis
[Themes, evidence, and synthesis]

## Contrarian Views And Risks
[Counterarguments, limitations, failure modes]

## Open Questions
[What remains uncertain]

## Sources
[Every URL used with a one-line note]

## Rerun Inputs
workflow: firecrawl-deep-research
topic: [topic]
depth: [quick/thorough/exhaustive]
output: [markdown/json/brief]
```

## Quality Bar

- Cite sources for factual claims.
- Prefer primary sources when available.
- Flag uncertainty and conflicting evidence.
- Synthesize instead of listing scrape summaries.
