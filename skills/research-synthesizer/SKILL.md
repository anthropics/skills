---
name: research-synthesizer
description: Multi-source research synthesis engine. Searches arXiv, PubMed, Semantic Scholar, Hacker News, and Wikipedia simultaneously to produce comprehensive research briefs on any topic. No API keys required. Use when user wants deep research, literature review, topic exploration, or multi-source synthesis. Triggers on phrases like "research this", "deep dive into", "explain the state of", "what's known about", "synthesize research on", "comprehensive overview of", "what does science say about", "academic review".
license: Complete terms in LICENSE.txt
allowed-tools: Bash(python:*) WebFetch
metadata:
  author: Maksim Soltan
  version: 1.0.0
  apis: arXiv, PubMed/NCBI, Semantic Scholar, Hacker News, Wikipedia
  auth: none-required
---

# Research Synthesizer

Crystalline entity mode: consume all sources simultaneously, synthesize intelligence that no single source contains.

## APIs Used (all free, no auth)

- **arXiv**: `http://export.arxiv.org/api/query`
- **PubMed**: `https://eutils.ncbi.nlm.nih.gov/entrez/eutils/`
- **Semantic Scholar**: `https://api.semanticscholar.org/graph/v1`
- **Hacker News**: `https://hn.algolia.com/api/v1/search`
- **Wikipedia**: `https://en.wikipedia.org/api/rest_v1/page/summary/{title}`

## Workflow

### Step 1: Topic Classification

Classify the topic to route to right sources:

```
Is it medical/health? → PubMed priority
Is it CS/AI/ML/physics/math? → arXiv priority
Is it tech/startup/product? → HN priority
Is it general knowledge? → Wikipedia first for grounding
All topics get: Semantic Scholar (if academic)
```

### Step 2: Parallel Fetch

Run ALL fetches simultaneously:

```python
scripts/synthesize.py --topic "TOPIC" --all-sources
```

**arXiv fetch:**
```
GET http://export.arxiv.org/api/query?search_query=all:{QUERY}&max_results=10&sortBy=relevance
```

**PubMed fetch (2-step):**
```
# Step 1: Get IDs
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term={QUERY}&retmax=10&retmode=json&sort=relevance

# Step 2: Fetch abstracts
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=pubmed&id={IDS}&rettype=abstract&retmode=json
```

**Semantic Scholar fetch:**
```
GET https://api.semanticscholar.org/graph/v1/paper/search?query={QUERY}&limit=10&fields=title,abstract,year,citationCount,authors,url
```

**Hacker News fetch:**
```
GET https://hn.algolia.com/api/v1/search?query={QUERY}&tags=story&hitsPerPage=10
```

**Wikipedia fetch:**
```
GET https://en.wikipedia.org/api/rest_v1/page/summary/{TOPIC_SLUG}
```

### Step 3: Cross-Source Analysis

After all data is fetched:

1. **Identify consensus** — what do 3+ sources agree on?
2. **Identify contradictions** — where do academic papers vs. popular coverage disagree?
3. **Timeline construction** — chronological order of developments
4. **Citation gravity** — which papers/ideas are most referenced?
5. **Frontier detection** — what's the cutting edge? What's unsettled?

### Step 4: Synthesis Report

```
## Research Synthesis: [TOPIC]
Sources: arXiv ({N} papers) | PubMed ({N} papers) | Semantic Scholar | HN ({N} posts) | Wikipedia
Date: [DATE]

### Executive Summary
[3-5 sentences. What is this? What's the current state? What matters?]

### Academic Landscape
**Core Papers (highest citation/influence):**
1. [Title] — [Authors], [Year] | Citations: [N]
   [1-2 sentence contribution]

**Recent Developments (last 12 months):**
- [Paper/finding + date]

### Technical Community Signals (Hacker News)
**Top discussions:**
- [HN thread title] — [N points], [date]
  [What the community debate reveals]

### Background Context (Wikipedia)
[Grounding paragraph]

### Consensus vs. Controversy
**Strong consensus:**
- [What's agreed upon]

**Active debate:**
- [Where experts disagree]

**Open questions:**
- [What's not yet answered]

### Key Resources
- arXiv papers: [links]
- PubMed papers: [links]
- HN threads: [links]
```

## Error Handling

- PubMed returns no results: may be non-medical topic, skip gracefully
- arXiv throttles (rare): retry once after 2s
- Semantic Scholar 429: skip citation enrichment, use arXiv data only
- Wikipedia no article: note gap, don't fake it

## Examples

User: "Deep dive into mechanistic interpretability"
→ Route: arXiv (cs.AI, cs.LG) + Semantic Scholar + HN
→ Skip PubMed (not medical)

User: "What does research say about ketogenic diet?"
→ Route: PubMed (high priority) + arXiv (q-bio) + HN + Wikipedia

User: "Synthesize research on transformer attention"
→ Route: arXiv (cs.LG, cs.CL) + Semantic Scholar + HN
