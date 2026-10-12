---
name: arxiv-researcher
description: Search, retrieve, and synthesize academic papers from arXiv, Semantic Scholar, and CrossRef. No API key required. Use when user asks to research a topic academically, find papers, literature review, summarize research, search arXiv, find citations, explore academic work on AI, ML, physics, math, biology, economics, or any science field. Triggers on phrases like "find papers on", "what does research say about", "arXiv search", "academic literature", "recent studies", "cite papers", "literature review".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: arXiv, Semantic Scholar, CrossRef
  auth: none-required
---

# arXiv Researcher

Multi-source academic paper search and synthesis. All APIs free, no auth required.

## APIs Used

- **arXiv API**: `http://export.arxiv.org/api/query` — 2M+ papers, full search, free
- **Semantic Scholar**: `https://api.semanticscholar.org/graph/v1` — citations, influence, no auth
- **CrossRef**: `https://api.crossref.org/works` — DOIs, metadata, no auth

## Workflow

### Step 1: Build Query
Parse the user's research topic into search terms. Strip filler, keep signal.

For arXiv, map topic to category if obvious:
- AI/ML → `cat:cs.AI` or `cat:cs.LG`
- Physics → `cat:physics` or subcategory
- Math → `cat:math`
- Economics → `cat:econ`
- Biology → `cat:q-bio`
- Finance → `cat:q-fin`

### Step 2: Fetch arXiv Papers

```python
scripts/fetch_arxiv.py --query "QUERY" --max 15 --sort relevance
```

Or call directly:
```
GET http://export.arxiv.org/api/query?search_query=all:QUERY&max_results=15&sortBy=relevance&sortOrder=descending
```

Parse XML response. Extract per paper:
- `id` (arXiv ID)
- `title`
- `summary` (abstract)
- `published` (date)
- `author` list
- `link` (PDF URL)
- `category` tags

### Step 3: Enrich with Semantic Scholar (optional, for citation counts)

```
GET https://api.semanticscholar.org/graph/v1/paper/arXiv:ARXIV_ID?fields=citationCount,influentialCitationCount,references
```

Use for the top 5 papers to surface most-cited work.

### Step 4: Synthesize

Structure output as:

```
## Research Landscape: [TOPIC]
Searched: arXiv + Semantic Scholar | [DATE]

### TL;DR
[2-3 sentence synthesis of what the research says overall]

### Key Papers (sorted by relevance/citations)
1. **[Title]** — [Authors], [Year]
   [1-2 sentence summary of what it contributes]
   Citations: [N] | arXiv: [ID] | [PDF link]

### Themes Emerging
- [Theme 1]: [brief]
- [Theme 2]: [brief]

### Open Questions / Gaps
- [What the research doesn't answer yet]

### Most Recent Work (last 6 months)
[Papers from recent period]
```

## Error Handling

- arXiv returns empty results: broaden query, try alternate terms
- Semantic Scholar rate limit (100 req/5min): skip enrichment, use arXiv data only
- XML parse error: use `scripts/fetch_arxiv.py` fallback

## Scripts

Run `scripts/fetch_arxiv.py` for robust fetching with error handling.
See `references/arxiv-categories.md` for full category list.

## Examples

User: "Find papers on mechanistic interpretability"
→ Query: `mechanistic interpretability neural networks`
→ Category hint: `cat:cs.LG cs.AI`

User: "What's the latest research on protein folding?"
→ Query: `protein folding structure prediction`
→ Category hint: `cat:q-bio.BM`

User: "arXiv papers about transformer attention mechanisms"
→ Query: `transformer attention mechanism`
→ Category: `cat:cs.LG`
