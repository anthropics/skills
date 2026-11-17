---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-research-papers
name: firecrawl-research-papers
description: Find and synthesize research papers, whitepapers, PDFs, technical reports, and academic sources with Firecrawl Research, using semantic paper search, related-paper expansion, and in-body verification over Firecrawl's paper index — largely biomedical and life-science literature from PubMed, bioRxiv, and medRxiv, plus arXiv preprints in CS, physics, and math. Use when the user wants a literature review, systematic review, survey of studies, paper summary, research landscape, or sourced synthesis from scholarly and industry publications, including clinical, drug, gene, disease, epidemiology, and public-health topics. Prefer this over a general web-research workflow whenever the evidence base is published papers rather than web pages.
license: ISC
metadata:
  author: firecrawl
  version: "0.1.0"
  homepage: https://www.firecrawl.dev
  source: https://github.com/firecrawl/firecrawl-workflows
inputs:
  - name: FIRECRAWL_API_KEY
    description: Firecrawl API key for hosted Firecrawl Research, CLI, MCP, or equivalent tool requests.
    required: true
---

# Firecrawl Research Papers

Use this to create a sourced literature review.

## Onboarding Interview

Infer the topic, source constraints, target count, and output format from context. If the topic is clear, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the topic, target paper count, or required venue/date/method constraints.

## Firecrawl Collection Plan

Use Firecrawl Research through the CLI, MCP, or equivalent Firecrawl tool
surface as the primary path for paper discovery and verification. Fall back to
general Firecrawl search and scrape for whitepapers, technical reports,
research blogs, leaderboards, or facts outside the paper corpus.

What the paper index holds: paper abstracts, with full text reachable per
paper. Its largest share is biomedical and life-science literature — PubMed
journal articles plus bioRxiv and medRxiv preprints — so clinical, drug, gene,
disease, epidemiology, and public-health questions are in scope. arXiv
preprints cover computer science, physics, and mathematics. Coverage outside
those sources is thinner, and the web tools below are the fallback there.

Core tools:

- MCP: `firecrawl_research_search_papers(query, k?)`
  CLI: `firecrawl research search-papers <query> [--k <number>]`
  Semantic search over paper abstracts. Start here for most paper-finding
  queries, and retry with alternate framing when results are thin or too
  narrow.
- MCP: `firecrawl_research_related_papers(seed_ids, intent, mode?, k?)`
  CLI: `firecrawl research related-papers <seedIds...> --intent <intent> [--mode <similar|citers|references>] [--k <number>]`
  Expand from strong seed papers into similar work, citing papers, or
  references. Use this to find the relevant paper family, not just the first
  matching result.
- MCP: `firecrawl_research_inspect_paper(id)`
  CLI: `firecrawl research inspect-paper <id>`
  Fetch canonical metadata for a candidate paper: title, abstract, authors,
  categories, source ids, and dates.
- MCP: `firecrawl_research_read_paper(id, question)`
  CLI: `firecrawl research read-paper <id> --question <question>`
  Verify a specific claim or constraint inside one paper, such as method,
  reported score, benchmark, affiliation, comparison, or limitation.
- MCP: `firecrawl_search(query)` / `firecrawl_scrape(url)`
  CLI: `firecrawl search <query>` / `firecrawl scrape <url>`
  Use for web-only context: benchmark leaderboards, rankings, reports,
  whitepapers, research blogs, and source pages outside the paper index.

Not the paper index, despite the name: passing `categories: ["research"]` to
`firecrawl_search` (CLI `firecrawl search <query> --categories research`)
filters an ordinary web search to research-affiliated websites — the list
includes PubMed, bioRxiv, medRxiv, arXiv, and publisher sites — and returns
page results from them. It reaches those sites' web pages; what it does not do
is query their paper records in the index above, so there is no abstract
search, no related-paper or citation-graph expansion, no canonical paper
metadata, and no in-body passages. Use it when a web search is what you want
and those sites should be weighted in the same call; use the
`firecrawl_research_*` tools for paper work.

Match the approach to the query:

- Single named paper: run one paper search, then inspect or read the paper if
  metadata or body verification is needed.
- Paper by description, method, or topic family: search for strong anchors,
  then expand with related papers and keep close neighbors.
- Enumeration queries, such as papers that do a task or benchmark a method:
  search multiple framings, expand several strong anchors, and re-seed from
  newly found relevant papers.
- Papers that use or exhibit a property: start from the defining paper or
  strongest anchor, expand via similar, citers, or references, and use
  read-paper to verify the property.
- Superlatives and leaderboards: use general web search or scrape to find the
  ranking, then map top entries back to papers with paper search.
- Author, organization, venue, date, or methodology constraints: verify with
  inspect-paper metadata or read-paper before keeping a candidate.

Target source types:

- biomedical and life-science literature from PubMed, with bioRxiv and medRxiv
  preprints for work that has not appeared in a journal yet
- arXiv preprints in computer science, physics, and mathematics
- academic papers from university sites and ACM/IEEE pages where accessible
- industry reports and whitepapers
- company research blogs
- technical articles and conference summaries

Principles:

- When in doubt, include the relevant paper family rather than only the single
  best result.
- Use related-paper expansion to avoid stopping at one strong hit.
- Use read-paper to verify load-bearing constraints, not to summarize every
  candidate.
- Drop only clearly off-topic papers.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners:

- Academic Papers researcher
- Biomedical and Life Sciences researcher, for PubMed journal articles and
  bioRxiv/medRxiv preprints on a clinical, drug, gene, disease, epidemiology,
  or public-health topic
- Industry Reports researcher
- Technical Articles researcher
- Synthesis and citation reviewer

Split by source or sub-topic, not by tool. Give each researcher the same paper
tools and let the topic decide which part of the corpus answers.

## Final Deliverable

```markdown
# Literature Review: [Topic]

## Abstract
[2-3 paragraph summary]

## Key Papers
[Title, authors, source URL, key findings, methodology, relevance]

## Themes And Consensus
[What sources agree on]

## Open Questions And Debates
[Disagreements and unresolved questions]

## Emerging Trends
[Recent developments]

## Sources
[Organized by paper/report/article]

## Rerun Inputs
workflow: firecrawl-research-papers
topic: [topic]
target_count: [number]
output: [markdown/brief]
```

## Quality Bar

- Every major claim should trace to a source.
- Note inaccessible or failed PDFs.
- Distinguish peer-reviewed work from blogs and vendor reports.
