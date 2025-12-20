---
name: swarm
description: Unified modular AI agent system with dynamic tool discovery and multi-provider support. Use when (1) building agentic AI workflows, (2) orchestrating multi-step task execution, (3) creating conversational agents with tool use, (4) managing multi-provider LLM interactions, or (5) building custom AI assistants with specialized tools.
license: MIT
---

# Swarm Multi-Agent System

Modular AI agent framework for building conversational agents with dynamic tool discovery, multi-provider support, and streaming responses.

## Helper Scripts Available

- `scripts/agent.py` - Run an interactive agent session with tool access
- `scripts/task.py` - Execute predefined tasks with streaming output
- `scripts/list_tools.py` - List all available tools and modules
- `scripts/providers.py` - List available LLM providers and test connectivity

**Always run scripts with `--help` first** to see usage.

## Architecture

```
┌──────────────────────────────────────────────────┐
│                 Swarm Agent                      │
│  (Conversation memory, tool execution, routing)  │
└──────────────────┬───────────────────────────────┘
                   │
┌──────────────────▼───────────────────────────────┐
│              Tool Registry                        │
│  (Dynamic discovery, schema management)           │
└──────────────────┬───────────────────────────────┘
                   │
┌──────────────────▼───────────────────────────────┐
│               Hive Modules                        │
│  search | research | gen | finance | data | ...   │
└──────────────────────────────────────────────────┘
```

## Quick Start

### Interactive Agent
```bash
# Start interactive agent session
python scripts/agent.py

# With specific provider
python scripts/agent.py --provider anthropic

# With tool filtering
python scripts/agent.py --tools search,research
```

### Task Execution
```bash
# Run a predefined task
python scripts/task.py research_deep "Analyze quantum computing trends"

# List available tasks
python scripts/task.py --list

# With output file
python scripts/task.py business_planner "Tech startup" --output plan.md
```

### Tool Discovery
```bash
# List all available tools
python scripts/list_tools.py

# Filter by module
python scripts/list_tools.py --module search

# Show tool schemas
python scripts/list_tools.py --schemas
```

## LLM Providers

| Provider | Models | Capabilities |
|----------|--------|--------------|
| xai (default) | Grok-3 | Chat, Vision, Image Gen |
| anthropic | Claude 3.5 | Chat, Vision, Tool Use |
| openai | GPT-4 | Chat, Vision, Function Calling |
| mistral | Mistral Large | Chat, Tool Use |
| gemini | Gemini 2.0 | Chat, Vision, Multimodal |
| perplexity | Sonar Pro | Chat, Search Integration |
| cohere | Command R+ | Chat, RAG |
| groq | Llama 3 | Fast Chat |

## Agent Features

### Conversation Memory
```bash
# Agent maintains context across interactions
python scripts/agent.py

> What's the weather in Tokyo?
[Uses weather tool]

> And how about New York?
[Remembers previous context]
```

### Tool Chaining
```bash
# Agent can chain multiple tools
python scripts/task.py "Research AI safety, then generate an infographic"

# Tools executed:
# 1. research_papers → Find relevant papers
# 2. synthesize → Summarize findings
# 3. generate_image → Create infographic
```

### Streaming Responses
```bash
# Real-time streaming output
python scripts/agent.py --stream

# Shows incremental token output and tool execution status
```

## Configuration

### Environment Variables
```bash
# Primary provider key
export XAI_API_KEY=your-key-here

# Additional providers (optional)
export ANTHROPIC_API_KEY=your-key-here
export OPENAI_API_KEY=your-key-here

# Default settings
export SWARM_DEFAULT_PROVIDER=xai
export SWARM_DEFAULT_MODEL=grok-3
export SWARM_MAX_CYCLES=10
```

### Common Options
```bash
--provider, -p    LLM provider (default: xai)
--model, -m       Specific model override
--tools, -t       Comma-separated list of tool modules to enable
--stream          Enable streaming output
--verbose, -v     Show detailed execution info
--max-cycles, -c  Maximum tool execution cycles (default: 10)
```

## Task Configuration

Tasks can be predefined in YAML:

```yaml
# swarm_tasks.yaml
tasks:
  research_deep:
    description: "Deep research with academic sources"
    tools: [search, research, synthesize]
    max_cycles: 15
    system_prompt: "You are a thorough researcher..."

  business_planner:
    description: "Business plan generation"
    tools: [search, finance, generate]
    artifacts: [plan.md, projections.xlsx]
```

## Output Formats

### Interactive (default)
Real-time conversation with tool execution feedback.

### Streaming JSON
```json
{"status": "thinking", "content": "Processing query..."}
{"status": "tool_call", "tool": "web_search", "args": {"query": "..."}}
{"status": "tool_result", "result": {...}}
{"status": "complete", "response": "Based on my research..."}
```

### Artifact Generation
```bash
python scripts/task.py report "Topic" --artifact-dir ./results

# Creates:
# ./results/report.md
# ./results/sources.json
# ./results/metadata.json
```

## Best Practices

1. **Provider Selection**: Use `xai` for general tasks, `anthropic` for complex reasoning
2. **Tool Scoping**: Limit tools with `--tools` for focused tasks
3. **Cycle Limits**: Set appropriate `--max-cycles` to prevent runaway execution
4. **Streaming**: Enable `--stream` for long-running tasks to see progress
5. **Memory Management**: Use `--new-session` to start fresh when switching topics

## Integration with Hive

The Swarm agent loads tool modules from the Hive system. See the `hive` skill for:
- Creating custom tool modules
- Tool schema definitions
- Handler implementations
- Module registration

## Troubleshooting

**"No tools available"**: Check that hive modules are accessible and properly registered

**"Provider not available"**: Verify API key in environment

**"Max cycles exceeded"**: Increase `--max-cycles` or simplify the task

**"Tool execution failed"**: Check `--verbose` output for specific errors
