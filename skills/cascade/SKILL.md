---
name: cascade
description: Hierarchical 3-tier multi-agent synthesis pattern for comprehensive research. Use when (1) launching comprehensive research workflows, (2) synthesizing complex topics from multiple sources, (3) creating executive summaries from parallel research, or (4) managing multi-tier synthesis pipelines. The Cascade pattern uses Belter workers → Drummer synthesis → Camina executive layers.
license: MIT
---

# Cascade Research Orchestration

Toolkit for executing multi-agent AI research workflows using hierarchical and parallel orchestration patterns.

## Helper Scripts Available

- `scripts/research.py` - Launch Dream Cascade research workflows
- `scripts/search.py` - Launch Dream Swarm multi-domain search
- `scripts/status.py` - Check workflow status and results
- `scripts/providers.py` - List available LLM providers and data sources

**Always run scripts with `--help` first** to see usage.

## Orchestration Patterns

### Dream Cascade (Hierarchical Research)

```
┌──────────────────────────────────────────────┐
│           Tier 1: Belter Workers              │
│  (8+ parallel agents doing initial research)  │
└──────────────────┬───────────────────────────┘
                   │
┌──────────────────▼───────────────────────────┐
│           Tier 2: Drummer Synthesis           │
│  (Mid-level agents synthesizing groups)       │
└──────────────────┬───────────────────────────┘
                   │
┌──────────────────▼───────────────────────────┐
│           Tier 3: Camina Executive            │
│  (Final synthesis and executive summary)      │
└──────────────────────────────────────────────┘
```

**Use Cases**:
- Comprehensive literature reviews
- Academic research synthesis
- Market analysis with expert summary
- Strategic planning with multiple perspectives

### Dream Swarm (Parallel Search)

```
┌──────────────────────────────────────────────┐
│                Search Query                   │
└──────────┬───────────────────┬───────────────┘
           │                   │
    ┌──────▼──────┐     ┌──────▼──────┐
    │ Text Agent  │     │ News Agent  │
    └─────────────┘     └─────────────┘
    ┌─────────────┐     ┌─────────────┐
    │Image Agent  │     │Academic Agent│
    └─────────────┘     └─────────────┘
    ┌─────────────┐     ┌─────────────┐
    │Video Agent  │     │Social Agent │
    └──────┬──────┘     └──────┬──────┘
           │                   │
    ┌──────▼───────────────────▼──────┐
    │       Aggregated Results         │
    └──────────────────────────────────┘
```

**Use Cases**:
- Multi-source information gathering
- Comparative analysis across domains
- Trend discovery and analysis
- Content discovery with synthesis

## Quick Start

### Research Workflow
```bash
# Launch comprehensive research
python scripts/research.py "Analyze the current state of quantum computing applications"

# With specific agent count and provider
python scripts/research.py "Market analysis for electric vehicles" \
  --agents 12 --provider anthropic

# Get status of running workflow
python scripts/status.py research_abc123

# Save results to file
python scripts/research.py "Topic" --output results.md
```

### Multi-Domain Search
```bash
# Launch parallel search
python scripts/search.py "climate change mitigation strategies"

# Restrict to specific domains
python scripts/search.py "AI safety research" \
  --domains academic,news,technical

# With more agents for broader coverage
python scripts/search.py "renewable energy innovations" --agents 8
```

## LLM Providers

12 supported providers (use with `--provider`):

| Provider | Models | Capabilities |
|----------|--------|--------------|
| xai (default) | Grok-3, Aurora | Chat, Vision, Image Gen |
| anthropic | Claude 3.5 | Chat, Vision |
| openai | GPT-4, DALL-E | Chat, Vision, Image, Embeddings |
| mistral | Pixtral | Chat, Vision, Embeddings |
| gemini | Gemini 2.0 | Chat, Vision, Embeddings |
| perplexity | Sonar Pro | Chat, Vision |
| cohere | Command | Chat, Embeddings |
| groq | Llama 3 | Chat (fast inference) |
| huggingface | Various | Chat, Vision, Image, Embeddings |
| ollama | Local | Chat, Vision (no API key) |
| elevenlabs | - | Text-to-Speech |
| manus | - | Chat, Agent profiles |

## Data Sources

17 integrated data sources (used automatically during research):

| Source | Type | Data |
|--------|------|------|
| arxiv | Academic | Papers, preprints |
| semantic_scholar | Academic | Paper metadata, citations |
| pubmed | Academic | Medical/biology research |
| wikipedia | Encyclopedia | Articles, structured data |
| github | Code | Repositories, users, issues |
| news | Current | Headlines, articles |
| youtube | Video | Video search, metadata |
| nasa | Science | Space, astronomy data |
| weather | Real-time | Forecasts, conditions |
| census | Demographics | Census Bureau data |
| finance | Markets | Stocks, economic data |
| wolfram | Computation | Knowledge engine |
| archive | Historical | Internet Archive (Wayback) |

## Workflow Management

### Status Checking
```bash
# Check status
python scripts/status.py research_abc123

# Returns:
# {
#   "status": "running|completed|failed|cancelled",
#   "progress": 65,
#   "agents_completed": 5,
#   "total_agents": 8,
#   "execution_time": 45.2,
#   "estimated_cost": 0.05
# }
```

### Cancellation
```bash
# Cancel running workflow
python scripts/status.py research_abc123 --cancel
```

### Results Retrieval
```bash
# Get full results (when completed)
python scripts/status.py research_abc123 --results

# Save to file
python scripts/status.py research_abc123 --results --output report.md
```

## Configuration

### Environment Variables
```bash
# Default provider
export DREAM_DEFAULT_PROVIDER=xai

# Default model
export DREAM_DEFAULT_MODEL=grok-3

# Enable document generation
export DREAM_GENERATE_DOCS=true

# Document formats
export DREAM_DOC_FORMATS=markdown,pdf
```

### Common Options
```bash
--provider, -p    LLM provider (default: xai)
--model, -m       Specific model override
--agents, -n      Number of worker agents
--output, -o      Save results to file
--format, -f      Output format (json, markdown, text)
--verbose, -v     Show detailed progress
--no-synthesis    Skip synthesis stages (Cascade only)
```

## Output Formats

### Markdown Report (default)
```markdown
# Research Report: [Topic]

## Executive Summary
[Camina synthesis output]

## Key Findings
[Drummer synthesis sections]

## Detailed Analysis
[Individual Belter results organized by theme]

## Sources & Citations
[Collected references]

## Metadata
- Agents: 8
- Execution time: 2m 34s
- Estimated cost: $0.05
```

### JSON (structured)
```json
{
  "task_id": "research_abc123",
  "topic": "...",
  "status": "completed",
  "executive_summary": "...",
  "sections": [...],
  "citations": [...],
  "metadata": {
    "agents": 8,
    "execution_time": 154.2,
    "total_tokens": 45000,
    "estimated_cost": 0.05
  }
}
```

## Best Practices

1. **Agent Count**: 6-10 agents for most research tasks, 12+ for comprehensive analysis
2. **Provider Selection**: Use `xai` for speed, `anthropic` for quality, `ollama` for cost-free local
3. **Synthesis Stages**: Keep both enabled for best results; disable for raw data gathering
4. **Domain Filtering**: Use `--domains` in Swarm to focus search scope
5. **Cost Management**: Monitor with `--verbose`, use `--no-synthesis` for cheaper runs

## Integration with MCP

If MCP server is running (port 5060), scripts communicate via the MCP protocol for advanced features:
- Streaming progress updates
- Real-time cost tracking
- Webhook notifications
- Persistent result storage

Start MCP server:
```bash
sm start mcp-orchestrator
# Or: python /home/coolhand/shared/mcp/start.sh
```

## Troubleshooting

**"Provider not available"**: Check API key in `~/.env` or `~/API_KEYS.md`

**"Timeout during synthesis"**: Increase timeout with `--timeout 600`

**"Rate limited"**: Reduce `--agents` count or switch provider

**"MCP not connected"**: Check `sm status mcp-orchestrator`, start if needed

## Reference Files

- **examples/** - Sample workflow configurations:
  - `research_workflow.yaml` - Research task template
  - `search_domains.yaml` - Domain-specific search configs
