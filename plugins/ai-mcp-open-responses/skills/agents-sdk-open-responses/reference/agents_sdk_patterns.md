# OpenAI Agents SDK Patterns Reference

## Overview

The OpenAI Agents SDK provides primitives for building agentic workflows with tool execution, handoffs, and guardrails. This reference covers integration with Open Responses for multi-provider support.

---

## Core Concepts

### Agent Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                              Agent                                       │
├─────────────────────────────────────────────────────────────────────────┤
│  name: string              │  Unique identifier for the agent           │
│  instructions: string      │  System prompt defining behavior           │
│  model: string             │  Model identifier (provider/model)         │
│  tools: Tool[]             │  Available function tools                  │
│  handoffs: Handoff[]       │  Agents this agent can delegate to         │
│  guardrails: Guardrail[]   │  Input/output validation functions         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Execution Flow

```
User Input
    │
    ▼
┌─────────────────┐
│  Input Guards   │──────▶ Reject if validation fails
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│     Agent       │
│  (LLM + Tools)  │
└────────┬────────┘
         │
    ┌────┴────┐
    │         │
    ▼         ▼
┌───────┐ ┌────────┐
│ Tool  │ │Handoff │
│ Call  │ │ Agent  │
└───┬───┘ └────┬───┘
    │          │
    └────┬─────┘
         │
         ▼
┌─────────────────┐
│  Output Guards  │──────▶ Reject if validation fails
└────────┬────────┘
         │
         ▼
    Final Output
```

---

## Agent Definition

### Basic Agent

```python
from agents import Agent

research_agent = Agent(
    name="Research Assistant",
    instructions="""You are a research assistant specializing in technical topics.

Your responsibilities:
1. Search for relevant information using available tools
2. Synthesize findings into clear, accurate summaries
3. Always cite sources when providing information
4. Ask clarifying questions when the request is ambiguous

Guidelines:
- Be thorough but concise
- Distinguish between facts and opinions
- Acknowledge uncertainty when appropriate""",
    model="openai/gpt-4o",
    tools=[web_search, document_reader, note_taker],
)
```

### Agent with Structured Output

```python
from agents import Agent
from pydantic import BaseModel

class ResearchResult(BaseModel):
    summary: str
    key_findings: list[str]
    sources: list[str]
    confidence: float

research_agent = Agent(
    name="Research Agent",
    instructions="Conduct thorough research and return structured results.",
    model="openai/gpt-4o",
    output_type=ResearchResult,
)
```

---

## Tool Definitions

### Function Tool

```python
from agents import function_tool
from pydantic import Field

@function_tool
def web_search(
    query: str = Field(..., description="Search query"),
    max_results: int = Field(5, ge=1, le=20, description="Maximum results")
) -> str:
    """Search the web for information.

    Returns formatted search results with titles, snippets, and URLs.
    """
    results = perform_search(query, max_results)
    return format_results(results)


@function_tool
def calculate(
    expression: str = Field(..., description="Mathematical expression to evaluate")
) -> str:
    """Evaluate a mathematical expression.

    Supports basic arithmetic, exponents, and common functions.
    Examples: "2 + 2", "sqrt(16)", "sin(pi/4)"
    """
    try:
        result = safe_eval(expression)
        return f"{expression} = {result}"
    except Exception as e:
        return f"Error evaluating expression: {e}"
```

### Tool with Context

```python
from agents import function_tool, RunContext

@function_tool
def get_user_data(
    ctx: RunContext,
    user_id: str = Field(..., description="User ID to look up")
) -> str:
    """Retrieve data for a specific user.

    Requires authentication context.
    """
    # Access context for auth, logging, etc.
    auth_token = ctx.get("auth_token")
    if not auth_token:
        return "Error: Authentication required"

    data = fetch_user(user_id, auth_token)
    return json.dumps(data)
```

---

## Handoffs

### Basic Handoff

```python
from agents import Agent, handoff

# Specialist agents
code_agent = Agent(
    name="Code Expert",
    instructions="You write and review code. Use precise, technical language.",
    model="openai/gpt-4o",
    tools=[code_executor, linter, formatter],
)

docs_agent = Agent(
    name="Documentation Expert",
    instructions="You write clear, comprehensive documentation.",
    model="anthropic/claude-sonnet-4-20250514",
    tools=[markdown_formatter, example_generator],
)

# Orchestrator with handoffs
orchestrator = Agent(
    name="Project Assistant",
    instructions="""You coordinate project tasks.

Route requests to specialists:
- Code tasks → Code Expert
- Documentation → Documentation Expert
- General questions → Handle yourself""",
    model="openai/gpt-4o",
    handoffs=[
        handoff(code_agent, "For coding tasks and code review"),
        handoff(docs_agent, "For documentation writing"),
    ],
)
```

### Conditional Handoff

```python
from agents import handoff

def should_handoff_to_code(context: dict) -> bool:
    """Determine if task requires code expertise."""
    keywords = ["code", "function", "debug", "implement", "refactor"]
    user_input = context.get("user_input", "").lower()
    return any(kw in user_input for kw in keywords)

orchestrator = Agent(
    name="Coordinator",
    instructions="Route tasks appropriately.",
    handoffs=[
        handoff(
            code_agent,
            "For code-related tasks",
            condition=should_handoff_to_code
        ),
    ],
)
```

---

## Guardrails

### Input Guardrail

```python
from agents import input_guardrail, GuardrailResult

@input_guardrail
async def validate_input(input_text: str) -> GuardrailResult:
    """Validate user input before processing."""

    # Length check
    if len(input_text) > 10000:
        return GuardrailResult(
            passed=False,
            message="Input too long. Please limit to 10,000 characters."
        )

    # Content policy check
    if contains_prohibited_content(input_text):
        return GuardrailResult(
            passed=False,
            message="Input contains prohibited content."
        )

    # PII detection
    pii_detected = detect_pii(input_text)
    if pii_detected:
        return GuardrailResult(
            passed=True,
            message=f"Warning: PII detected ({pii_detected}). Proceeding with caution.",
            metadata={"pii_types": pii_detected}
        )

    return GuardrailResult(passed=True)
```

### Output Guardrail

```python
from agents import output_guardrail, GuardrailResult

@output_guardrail
async def validate_output(output: str) -> GuardrailResult:
    """Validate agent output before returning to user."""

    # Check for hallucination markers
    if contains_uncertain_claims(output):
        return GuardrailResult(
            passed=True,
            message="Output may contain uncertain claims. Added disclaimer.",
            modified_output=output + "\n\n*Note: Some information may require verification.*"
        )

    # Format validation
    if not is_valid_format(output):
        return GuardrailResult(
            passed=False,
            message="Output format invalid. Regenerating..."
        )

    return GuardrailResult(passed=True)
```

---

## Runner Configuration

### Basic Runner

```python
from agents import Runner
from openai import AsyncOpenAI

# Create client pointing to Open Responses
client = AsyncOpenAI(
    base_url="http://localhost:8080/v1",
    api_key="local-key",
)

async def run_agent(task: str) -> str:
    runner = Runner(
        agent=research_agent,
        client=client,
    )

    result = await runner.run(task)
    return result.final_output
```

### Runner with Configuration

```python
from agents import Runner, RunConfig

config = RunConfig(
    max_turns=10,           # Maximum conversation turns
    max_tool_calls=50,      # Maximum tool invocations
    timeout=300,            # Timeout in seconds
    parallel_tool_calls=True,
    tracing_enabled=True,
)

async def run_with_config(task: str) -> str:
    runner = Runner(
        agent=research_agent,
        client=client,
        config=config,
    )

    result = await runner.run(task)

    # Access execution trace
    for turn in result.trace:
        print(f"Turn {turn.index}: {turn.agent_name}")
        for tool_call in turn.tool_calls:
            print(f"  - {tool_call.name}({tool_call.args})")

    return result.final_output
```

---

## Open Responses Integration

### Custom Model Provider

```python
from agents import Agent, Runner
from openai import AsyncOpenAI

# Open Responses with Ollama
ollama_client = AsyncOpenAI(
    base_url="http://localhost:8080/v1",
    api_key="local-key",
)

local_agent = Agent(
    name="Local Assistant",
    instructions="You are a helpful assistant running on local hardware.",
    model="local/llama3.2",  # Routed to Ollama
)

# Open Responses with fallback
async def run_with_fallback(task: str) -> str:
    """Run agent with automatic fallback on failure."""

    try:
        runner = Runner(agent=local_agent, client=ollama_client)
        return await runner.run(task)
    except Exception as e:
        # Fallback to cloud
        cloud_client = AsyncOpenAI()
        cloud_agent = Agent(
            name="Cloud Assistant",
            instructions=local_agent.instructions,
            model="openai/gpt-4o-mini",
        )
        runner = Runner(agent=cloud_agent, client=cloud_client)
        return await runner.run(task)
```

### Multi-Model Agent

```python
# Use different models for different capabilities
fast_model = "openai/gpt-4o-mini"
smart_model = "anthropic/claude-sonnet-4-20250514"
code_model = "local/codellama"

router_agent = Agent(
    name="Router",
    model=fast_model,
    instructions="Route requests to appropriate specialists.",
    handoffs=[
        handoff(
            Agent(name="Analyst", model=smart_model, ...),
            "For complex analysis"
        ),
        handoff(
            Agent(name="Coder", model=code_model, ...),
            "For code generation"
        ),
    ],
)
```

---

## Best Practices

### 1. Agent Design

- Keep instructions focused and specific
- Use clear boundaries for responsibilities
- Include examples in instructions when helpful

### 2. Tool Design

- Make tool descriptions comprehensive
- Include parameter constraints in Field definitions
- Return structured, parseable outputs

### 3. Error Handling

- Use guardrails for validation
- Implement graceful degradation
- Log execution traces for debugging

### 4. Performance

- Use appropriate models for task complexity
- Enable parallel tool calls when possible
- Set reasonable timeouts and limits
