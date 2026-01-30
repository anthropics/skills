---
name: agents-sdk-open-responses
description: |
  Build agent workflows using the OpenAI Agents SDK with Responses API and Open Responses.
  Supports local model execution via Ollama, LiteLLM, and custom routers for flexible
  agent orchestration and tool execution.
license: Complete terms in LICENSE.txt
---

# Agents SDK with Open Responses

## When to Use

Use this skill when:

- Building agent workflows using the OpenAI Agents SDK
- Integrating Agents SDK with Open Responses for multi-provider support
- Running agents locally with Ollama, LiteLLM, or other local inference engines
- Implementing tool execution pipelines within agent loops
- Creating custom routing between cloud and local models in agent workflows

---

## Concepts

### Agents SDK Overview

The OpenAI Agents SDK provides primitives for building agent systems:

- **Agent**: Core entity with instructions, tools, and model configuration
- **Runner**: Executes agent loops with automatic tool calling
- **Handoffs**: Transfer control between specialized agents
- **Guardrails**: Input/output validation and safety checks

### Integration with Open Responses

Open Responses extends the Agents SDK by:

- Enabling local model backends (Ollama, LiteLLM)
- Providing unified routing across providers
- Supporting custom inference endpoints
- Maintaining Responses API compatibility

---

## Instructions

### Step 1: Set Up the Agents SDK

```bash
pip install openai-agents
```

### Step 2: Configure Open Responses Backend

Create a configuration for your Open Responses router:

```python
# config.py
from dataclasses import dataclass

@dataclass
class OpenResponsesConfig:
    base_url: str = "http://localhost:8080/v1"
    default_model: str = "local/llama3.2"
    api_key: str = "local-key"  # For local servers

    # Provider-specific settings
    ollama_url: str = "http://localhost:11434"
    litellm_url: str = "http://localhost:4000"
```

### Step 3: Create an Agent with Open Responses

```python
# agent.py
from agents import Agent, Runner
from openai import OpenAI
from config import OpenResponsesConfig

config = OpenResponsesConfig()

# Create client pointing to Open Responses server
client = OpenAI(
    base_url=config.base_url,
    api_key=config.api_key,
)

# Define agent with local model
research_agent = Agent(
    name="Research Assistant",
    instructions="""You are a helpful research assistant.
    Use available tools to find and synthesize information.
    Always cite your sources.""",
    model=config.default_model,
    tools=[web_search_tool, document_reader_tool],
)
```

### Step 4: Implement Custom Tools

```python
# tools.py
from agents import function_tool

@function_tool
def web_search(query: str, max_results: int = 5) -> str:
    """Search the web for information.

    Args:
        query: Search query string
        max_results: Maximum number of results to return
    """
    # Implementation
    results = perform_search(query, max_results)
    return format_results(results)

@function_tool
def document_reader(path: str, page: int | None = None) -> str:
    """Read content from a document.

    Args:
        path: Path to the document
        page: Optional specific page number
    """
    # Implementation
    content = read_document(path, page)
    return content
```

### Step 5: Run the Agent Loop

```python
# runner.py
from agents import Runner
from agent import research_agent, client

async def run_research_task(task: str) -> str:
    runner = Runner(
        agent=research_agent,
        client=client,
    )

    result = await runner.run(task)
    return result.final_output

# Example usage
async def main():
    response = await run_research_task(
        "Research the latest developments in MCP protocol and summarize key features"
    )
    print(response)
```

### Step 6: Configure Local Model Routing

Set up your Open Responses server to route to local models:

```yaml
# open-responses-config.yaml
server:
  host: "0.0.0.0"
  port: 8080

providers:
  ollama:
    enabled: true
    base_url: "http://localhost:11434"
    models:
      - name: "llama3.2"
        context_length: 128000
      - name: "codellama"
        context_length: 16384

  litellm:
    enabled: true
    base_url: "http://localhost:4000"
    models:
      - name: "gpt-4o-mini"
        provider: "openai"
      - name: "claude-sonnet"
        provider: "anthropic"

routing:
  default_provider: "ollama"
  model_mapping:
    "local/*": "ollama"
    "cloud/*": "litellm"
```

### Step 7: Implement Agent Handoffs

```python
# handoffs.py
from agents import Agent, handoff

# Specialized agents
code_agent = Agent(
    name="Code Expert",
    instructions="You specialize in writing and reviewing code.",
    model="local/codellama",
    tools=[code_executor, linter],
)

research_agent = Agent(
    name="Research Expert",
    instructions="You specialize in research and analysis.",
    model="local/llama3.2",
    tools=[web_search, document_reader],
)

# Main orchestrator with handoffs
orchestrator = Agent(
    name="Orchestrator",
    instructions="""Route tasks to appropriate specialists:
    - Code tasks → Code Expert
    - Research tasks → Research Expert""",
    model="local/llama3.2",
    handoffs=[
        handoff(code_agent, "For code-related tasks"),
        handoff(research_agent, "For research tasks"),
    ],
)
```

### Step 8: Add Guardrails

```python
# guardrails.py
from agents import input_guardrail, output_guardrail, GuardrailResult

@input_guardrail
async def validate_input(input_text: str) -> GuardrailResult:
    """Validate user input before processing."""
    if len(input_text) > 10000:
        return GuardrailResult(
            passed=False,
            message="Input too long. Please limit to 10000 characters."
        )
    return GuardrailResult(passed=True)

@output_guardrail
async def validate_output(output: str) -> GuardrailResult:
    """Validate agent output before returning."""
    # Check for sensitive content, validate format, etc.
    return GuardrailResult(passed=True)
```

---

## Local Development Setup

### With Ollama

```bash
# Install Ollama
curl -fsSL https://ollama.com/install.sh | sh

# Pull models
ollama pull llama3.2
ollama pull codellama

# Verify API
curl http://localhost:11434/api/tags
```

### With LiteLLM

```bash
# Install LiteLLM
pip install litellm[proxy]

# Start proxy
litellm --config litellm_config.yaml --port 4000
```

---

## Additional Resources

- **`reference/`** — Agents SDK API documentation, Open Responses schemas
- **`scripts/`** — Setup scripts, example agent configurations, test utilities

Use these resources to accelerate your agent development workflow.
