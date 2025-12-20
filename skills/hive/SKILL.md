---
name: hive
description: Tool module library for AI agent systems with search, research, generation, and data tools. Use when (1) building custom tool modules for agents, (2) adding web search/image search capabilities, (3) integrating academic research APIs, (4) creating image generation tools, (5) adding finance/data tools, or (6) building domain-specific agent toolkits.
license: MIT
---

# Hive Tool Modules

Library of tool modules for AI agent systems. Each module provides specialized capabilities that agents can invoke during task execution.

## Helper Scripts Available

- `scripts/search.py` - Web, image, and map search tools
- `scripts/research.py` - Academic research (arXiv, PubMed, Semantic Scholar)
- `scripts/generate.py` - Image generation (xAI Aurora, DALL-E)
- `scripts/create_module.py` - Generate new tool module from template
- `scripts/list_tools.py` - List all tools with schemas

**Always run scripts with `--help` first** to see usage.

## Available Modules

| Module | Tools | Description |
|--------|-------|-------------|
| search | web_search, image_search, map_search | Multi-provider web search |
| research | arxiv_search, pubmed_search, scholar_search | Academic paper discovery |
| gen | generate_image, edit_image | AI image generation |
| finance | stock_quote, market_data, company_info | Financial data |
| data | fetch_json, parse_csv, transform_data | Data operations |
| news | headlines, article_search | News aggregation |
| chat | llm_query, summarize | LLM integration |
| executor | run_code, shell_command | Code execution |

## Quick Start

### Web Search
```bash
# Search the web
python scripts/search.py "latest AI developments"

# Image search
python scripts/search.py "neural network diagram" --type image

# With specific provider
python scripts/search.py "query" --provider brave
```

### Academic Research
```bash
# Search arXiv
python scripts/research.py "transformer attention mechanisms" --source arxiv

# PubMed search
python scripts/research.py "CRISPR applications" --source pubmed

# Multi-source
python scripts/research.py "quantum computing" --source all
```

### Image Generation
```bash
# Generate with xAI Aurora
python scripts/generate.py "A futuristic city at sunset"

# With DALL-E
python scripts/generate.py "prompt" --provider openai

# Custom size
python scripts/generate.py "prompt" --size 1024x1024
```

## Tool Schema Format

Tools use OpenAI function-calling format:

```json
{
  "name": "web_search",
  "description": "Search the web for information",
  "parameters": {
    "type": "object",
    "properties": {
      "query": {
        "type": "string",
        "description": "Search query"
      },
      "num_results": {
        "type": "integer",
        "description": "Number of results to return",
        "default": 10
      }
    },
    "required": ["query"]
  }
}
```

## Creating Custom Modules

### Module Template
```bash
# Generate new module from template
python scripts/create_module.py my_module

# Creates: hive/swarm_my_module.py
```

### Module Structure
```python
from core.core_module_base import SwarmModuleBase

class MyModule(SwarmModuleBase):
    name = "my_module"
    display_name = "My Module"
    description = "Custom tools for specific domain"

    def initialize(self):
        self.tool_schemas = [
            {
                "name": "my_tool",
                "description": "Does something useful",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "input": {"type": "string"}
                    },
                    "required": ["input"]
                }
            }
        ]

    def handle_my_tool(self, arguments, config=None):
        input_val = arguments.get("input")
        # Implementation
        return {"result": f"Processed: {input_val}"}
```

### Handler Requirements

1. **Accept both arguments and config**: Even if config unused
2. **Return structured data**: Dict with clear result keys
3. **Handle errors gracefully**: Return error dict instead of raising
4. **Include type information**: Use schemas with proper types

## Search Providers

### Web Search
| Provider | Features | API Key Env |
|----------|----------|-------------|
| brave | General web, API-based | BRAVE_API_KEY |
| tavily | AI-optimized, structured | TAVILY_API_KEY |
| serpapi | Google results proxy | SERPAPI_API_KEY |
| google | Direct Google API | GOOGLE_API_KEY |

### Image Search
| Provider | Features | API Key Env |
|----------|----------|-------------|
| brave | General images | BRAVE_API_KEY |
| google | Google Images | GOOGLE_API_KEY |

## Research Sources

| Source | Coverage | Features |
|--------|----------|----------|
| arXiv | Preprints | Full text, citations |
| PubMed | Medical/Bio | Abstracts, MeSH terms |
| Semantic Scholar | All fields | Citations, embeddings |
| CrossRef | DOI metadata | Citation counts |

## Image Generation

| Provider | Model | Capabilities |
|----------|-------|--------------|
| xai | Aurora | High quality, artistic |
| openai | DALL-E 3 | Photorealistic, text |
| stability | SDXL | Fast, customizable |
| huggingface | Various | Open models |

## Output Formats

### Tool Results
```json
{
  "tool": "web_search",
  "status": "success",
  "results": [
    {
      "title": "Result Title",
      "url": "https://...",
      "snippet": "Description..."
    }
  ],
  "metadata": {
    "provider": "brave",
    "query": "original query",
    "num_results": 10
  }
}
```

### Error Format
```json
{
  "tool": "web_search",
  "status": "error",
  "error": "Rate limit exceeded",
  "retry_after": 60
}
```

## Configuration

### Environment Variables
```bash
# Search providers
export BRAVE_API_KEY=your-key
export TAVILY_API_KEY=your-key
export SERPAPI_API_KEY=your-key

# Image generation
export XAI_API_KEY=your-key
export OPENAI_API_KEY=your-key

# Research APIs
export SEMANTIC_SCHOLAR_API_KEY=your-key
```

### Module Configuration
```yaml
# config/modules.yaml
search:
  default_provider: brave
  max_results: 10
  timeout: 30

research:
  sources: [arxiv, semantic_scholar]
  max_papers: 20

gen:
  default_provider: xai
  default_size: 1024x1024
```

## Best Practices

1. **Provider Fallback**: Configure multiple providers for reliability
2. **Rate Limiting**: Respect API limits, use delays between calls
3. **Caching**: Cache results to reduce API costs
4. **Error Handling**: Always return structured errors, never raise uncaught
5. **Schemas**: Keep schemas accurate and up-to-date
6. **Testing**: Test modules standalone with `--test` flag

## Integration

Hive modules integrate with Swarm agents automatically:

```python
# Modules auto-register when imported
from hive import swarm_search, swarm_research

# Agent discovers available tools
agent.discover_tools()

# Tools available for agent use
agent.query("Search for recent papers on transformers")
```

## Troubleshooting

**"Module not found"**: Check module file exists in hive/ directory

**"Tool schema invalid"**: Validate JSON schema structure

**"API rate limited"**: Reduce request frequency, use caching

**"Provider unavailable"**: Check API key, try fallback provider
