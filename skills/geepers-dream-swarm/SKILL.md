---
name: dream-swarm
description: Launch parallel multi-domain search workflows using the Dream Swarm orchestrator. Use when (1) searching across multiple data sources simultaneously, (2) aggregating information from APIs, databases, and web sources, (3) comparing findings across domains, (4) rapid parallel data gathering. Requires the MCP server to be running.
license: MIT
---

# Dream Swarm Search Skill

Launch parallel multi-agent search workflows across multiple domains.

## Architecture: Parallel Domain Agents

```
              ┌────────────────────────┐
              │     SEARCH QUERY       │
              │  "AI safety research"  │
              └───────────┬────────────┘
                          │
        ┌─────────────────┼─────────────────┐
        │                 │                 │
   ┌────▼────┐       ┌────▼────┐       ┌────▼────┐
   │  arXiv  │       │ GitHub  │       │  News   │
   │  Agent  │       │  Agent  │       │  Agent  │
   └────┬────┘       └────┬────┘       └────┬────┘
        │                 │                 │
        └─────────────────┼─────────────────┘
                          │
              ┌───────────▼───────────┐
              │    AGGREGATOR         │
              │  Dedupe & Synthesize  │
              └───────────────────────┘
```

## When to Use

- **Multi-source search** across different APIs
- **Comparative analysis** from diverse sources
- **Rapid information gathering** with parallelization
- **Fact-checking** against multiple sources
- **Research aggregation** from academic + news + code

## Available Domains (17 sources)

| Domain | Description | Example Query |
|--------|-------------|---------------|
| `arxiv` | Academic papers | "quantum computing" |
| `github` | Code repositories | "react components" |
| `news` | Recent articles | "AI regulation 2024" |
| `wikipedia` | Encyclopedia | "machine learning" |
| `pubmed` | Medical literature | "CRISPR therapy" |
| `semantic_scholar` | Academic index | "transformer architectures" |
| `census` | US demographics | "population density" |
| `nasa` | Space/Earth data | "mars rover" |
| `youtube` | Video content | "tutorial python" |
| `weather` | Forecasts | "Seattle forecast" |
| `openlibrary` | Book metadata | "science fiction" |
| `fec` | Campaign finance | "2024 donations" |
| `judiciary` | Court records | "antitrust case" |
| `archive` | Wayback Machine | "historical websites" |
| `finance` | Market data | "AAPL stock" |
| `mal` | Anime database | "studio ghibli" |
| `wolfram` | Computation | "integral sin(x)" |

## Scripts

### Start Search Workflow
```bash
scripts/swarm-search.py "AI safety research" --domains arxiv github news
scripts/swarm-search.py "climate change" --agents 10 --parallel 5
scripts/swarm-search.py "quantum computing" --all-domains
```

### Check Search Status
```bash
scripts/swarm-status.py workflow-xyz789
scripts/swarm-status.py workflow-xyz789 --results
```

## Configuration Options

| Parameter | Default | Description |
|-----------|---------|-------------|
| `--domains` | arxiv,news | Comma-separated domain list |
| `--agents` | 5 | Number of parallel agents (1-20) |
| `--parallel` | 3 | Max concurrent domain searches (1-10) |
| `--provider` | xai | LLM provider for synthesis |
| `--max-results` | 10 | Results per domain |
| `--stream` | false | Enable SSE streaming |
| `--output` | stdout | Output format (stdout, json, markdown) |

## Example Workflows

### Academic + Code Search
```bash
scripts/swarm-search.py "WebAssembly optimization" \
  --domains arxiv,github,semantic_scholar \
  --agents 6 --parallel 3
```

### News + Social Monitoring
```bash
scripts/swarm-search.py "AI regulation policy" \
  --domains news,wikipedia,youtube \
  --agents 5 --output markdown
```

### Comprehensive Research
```bash
scripts/swarm-search.py "CRISPR gene therapy" \
  --domains arxiv,pubmed,news,wikipedia \
  --agents 8 --parallel 4 --stream
```

## Output Structure

```json
{
  "task_id": "swarm-xyz789",
  "status": "completed",
  "results": {
    "arxiv": [
      {"title": "...", "url": "...", "abstract": "..."}
    ],
    "github": [
      {"name": "...", "url": "...", "description": "..."}
    ],
    "news": [
      {"title": "...", "url": "...", "source": "..."}
    ]
  },
  "synthesis": {
    "summary": "...",
    "key_themes": [...],
    "cross_domain_insights": [...]
  },
  "metadata": {
    "domains_searched": 3,
    "total_results": 24,
    "execution_time": 12.5
  }
}
```

## Advantages over Dream Cascade

| Aspect | Dream Swarm | Dream Cascade |
|--------|-------------|---------------|
| **Speed** | Faster (parallel) | Slower (hierarchical) |
| **Depth** | Broad coverage | Deep analysis |
| **Use case** | Data gathering | Research synthesis |
| **Agent count** | Many simple agents | Fewer complex agents |
| **Cost** | Lower | Higher |

## Prerequisites

- MCP server running on port 5060
- Valid API keys for data sources
- Python 3.10+ with requests library

## Troubleshooting

**"Domain not available"**: Check API key configured for that domain

**"Rate limited"**: Reduce `--parallel` count

**"No results"**: Try broader query or different domains

## Related Skills

- **dream-cascade** - Hierarchical deep research
- **data-fetch** - Single domain direct access
- **code-quality** - Code-specific searches
