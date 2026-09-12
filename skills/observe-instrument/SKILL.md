---
name: observe-instrument
license: Apache-2.0
description: >
  Use this skill when the user wants to add observability, tracing, or monitoring to a Python AI agent
  using the Observe SDK (ioa-observe-sdk). Trigger for requests like "instrument my agent", "add observability
  to this agent", "add tracing to my LangGraph / LlamaIndex / Python agent", "integrate the Observe SDK",
  "add observe decorators", or "make my agent observable". Also trigger when the user asks to add
  @agent, @tool, @graph, or @workflow decorators from the ioa_observe package to existing code.
---

# Observe SDK Instrumentation Skill

Instrument Python AI agents with the [Observe SDK](https://github.com/agntcy/observe) (`ioa-observe-sdk`).
The SDK emits OpenTelemetry traces, metrics, and logs from agents, tools, and workflows.

## Step 1 — Read and Understand the Target Code

Read the file(s) the user wants to instrument. Identify:

- **Framework**: LlamaIndex, LangGraph, raw Python, or other
- **Agents**: Classes or functions that orchestrate other calls (agent nodes, workflow classes)
- **Tools**: Functions called by agents to perform specific tasks (multiply, search, etc.)
- **Graphs/Workflows**: Top-level orchestration objects (AgentWorkflow, CompiledStateGraph, etc.)
- **Entry point**: Where `main()` or the primary invocation happens
- **Async vs sync**: Whether the code is async (`async def`) or sync

## Step 2 — Add the Dependency

Add `ioa-observe-sdk` to the project's dependency file. Check which one exists:

**pyproject.toml** (uv/poetry):
```toml
[project]
dependencies = [
    "ioa-observe-sdk",
    ...
]
```

**requirements.txt**:
```
ioa-observe-sdk
```

If neither exists, note that the user should install with:
```bash
pip install ioa-observe-sdk
# or
uv add ioa-observe-sdk
```

## Step 3 — Add Imports

At the top of the target file, after existing imports, add:

```python
from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import agent, tool, graph, workflow  # use only what's needed
from ioa_observe.sdk.tracing import session_start
```

Only import the decorators you actually use. Common combinations:
- LlamaIndex agents: `agent, tool, graph`
- LangGraph graphs: `agent, task, workflow`
- Simple agents: `agent, tool`

## Step 4 — Initialize Observe

Add `Observe.init()` near the top of the file, after imports and env loading, before any agent/tool definitions:

```python
import os
from dotenv import load_dotenv  # add if not present

load_dotenv()

Observe.init(
    app_name="your_service_name",  # use the project/agent name
    api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318")
)
```

**`app_name`**: Use the agent/service name in snake_case (e.g., `"math_agent_service"`, `"research_workflow"`).

**Environment**: Make sure `.env` has (or add to it):
```
OTLP_HTTP_ENDPOINT=http://localhost:4318
```

## Step 5 — Apply Decorators

### Tool functions → `@tool`

Apply to any function an agent calls to perform a discrete action:

```python
@tool(name="multiply")
def multiply(a: float, b: float) -> float:
    """Multiply two numbers"""
    return a * b
```

Rules:
- Use `name=` matching the function name (snake_case)
- Apply BEFORE any framework-specific decorators (e.g., LangGraph `@tool`)
- Works on both sync and async functions

### Agent classes → `@graph` + `@agent`

For classes that wrap a framework workflow (LlamaIndex, LangGraph, etc.), stack both decorators:

```python
@graph(name="my_agent_graph")
@agent(name="my_agent")
class MyAgentWorkflow:
    def __init__(self, tools, llm, system_prompt):
        self.workflow = AgentWorkflow.from_tools_or_functions(...)

    async def run(self, user_msg: str):
        return await self.workflow.run(user_msg=user_msg)

    def get_workflow(self):
        """Return underlying workflow for topology detection"""
        return self.workflow
```

**Important**: `@graph` goes ABOVE `@agent` (outer first). Add `get_workflow()` if it doesn't exist — the SDK uses it to capture the agent graph topology.

### Agent functions → `@agent`

For function-based agents (e.g., LangGraph node functions):

```python
@agent(name="research_agent")
async def research_node(state: AgentState) -> dict:
    ...
```

### Workflow functions → `@workflow`

For orchestration functions that coordinate multiple agents:

```python
@workflow(name="multi_agent_workflow")
async def run_pipeline(input: str) -> str:
    ...
```

### Task functions → `@task`

For discrete processing steps within a workflow:

```python
@task(name="process_results")
def process(data: dict) -> dict:
    ...
```

## Step 6 — Add Session Tracking

Add `session_start()` at the invocation point in `main()` (or equivalent):

**Async main**:
```python
async def main():
    session_start()  # call before running the agent
    result = await my_agent.run(user_msg="...")
    print(result)
```

**Sync main with context manager** (recommended for workflows):
```python
def main():
    with session_start() as session_id:
        result = my_agent.run(input="...")
    print(result)
```

Use the plain `session_start()` call (not context manager) for async entry points where session boundaries aren't clearly scoped.

## Step 7 — Verify and Summarize

After making changes:

1. Show the user a summary of what was changed:
   - Which decorators were added and to what
   - Where `Observe.init()` was placed
   - What dependency was added

2. Note any framework-specific caveats:
   - **LlamaIndex**: The `@graph` + `@agent` combo on the workflow class captures topology via `get_workflow()`
   - **LangGraph**: Individual node functions get `@agent` or `@task`; the compiled graph gets `@graph`
   - **Async**: `session_start()` without context manager works well in async code

3. Remind the user to set the env var:
   ```bash
   export OTLP_HTTP_ENDPOINT=http://localhost:4318
   # or add to .env
   ```

---

## Framework Quick Reference

### LlamaIndex AgentWorkflow

```python
from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import tool, agent, graph
from ioa_observe.sdk.tracing import session_start
import os

Observe.init("my_service", api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318"))

@tool(name="my_tool")
def my_tool(x: float) -> float:
    return x * 2

@graph(name="my_agent_graph")
@agent(name="my_agent")
class MyAgent:
    def __init__(self, tools, llm, system_prompt):
        self.workflow = AgentWorkflow.from_tools_or_functions(tools, llm=llm, system_prompt=system_prompt)

    async def run(self, user_msg: str):
        return await self.workflow.run(user_msg=user_msg)

    def get_workflow(self):
        return self.workflow

async def main():
    session_start()
    agent = MyAgent(tools=[my_tool], llm=llm, system_prompt="You are a helpful agent.")
    result = await agent.run(user_msg="...")
    print(result)
```

### LangGraph

```python
from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import agent, task, workflow
from ioa_observe.sdk.tracing import session_start
import os

Observe.init("my_service", api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318"))

@agent(name="my_node")
def my_node(state: State) -> dict:
    ...

@workflow(name="my_graph")
def build_graph() -> CompiledStateGraph:
    ...

def main():
    with session_start() as session_id:
        result = graph.invoke({"input": "..."})
```

### Raw Python Agent / OpenAI SDK

```python
from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import agent, tool
from ioa_observe.sdk.tracing import session_start
import os

Observe.init("my_service", api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318"))

@tool(name="get_order_status")
def get_order_status(order_id: str) -> str:
    ...

@agent(name="support_agent")
def run_support_agent(user_message: str) -> str:
    # openai client calls are auto-instrumented by Observe.init()
    ...

def main():
    session_start()
    while True:
        user_input = input("You: ")
        result = run_support_agent(user_input)
        print(result)
```

**Note**: `Observe.init()` automatically instruments all `openai` client calls via OTel. You only need `@tool` and `@agent` for your own functions.

### CrewAI

```python
from ioa_observe.sdk import Observe
from ioa_observe.sdk.decorators import tool, workflow
from ioa_observe.sdk.tracing import session_start
import os

Observe.init("my_crew", api_endpoint=os.getenv("OTLP_HTTP_ENDPOINT", "http://localhost:4318"))

@tool(name="search_topic")
@crewai_tool("search_topic")  # crewai @tool goes above ioa_observe @tool
def search_topic(query: str) -> str:
    ...

@workflow(name="research_crew")
def run_crew(topic: str) -> str:
    crew = Crew(agents=[...], tasks=[...], process=Process.sequential)
    return crew.kickoff()

def main():
    session_start()
    result = run_crew("my topic")
```

**Note**: CrewAI's internal agent execution is auto-instrumented by `Observe.init()`. Apply `@workflow` to the function that kicks off the crew, and `@tool` to custom tool functions.

### Multi-Agent Systems

Multi-agent systems have multiple cooperating agents. The key rules:

- Each agent node/function gets its own `@agent` decorator
- The top-level orchestrator/supervisor gets `@workflow`
- `session_start()` is called **once** at the entry point — all agents share the same `TraceId`
- `@graph` goes on the graph builder (LangGraph)
- Do NOT call `session_start()` inside individual agent functions

**LangGraph supervisor pattern:**
```python
from ioa_observe.sdk.decorators import agent, graph, workflow
from ioa_observe.sdk.decorators import tool as observe_tool

@observe_tool(name="search_web")
@langchain_tool
def search_web(query: str) -> str: ...

@agent(name="supervisor")
def supervisor_node(state): ...

@agent(name="researcher")
def research_node(state): ...

@agent(name="writer")
def write_node(state): ...

@graph(name="multi_agent_graph")
def build_graph(): ...

def main():
    session_start()
    build_graph().stream({"messages": [...]})
```

**LlamaIndex multi-agent:**
```python
from ioa_observe.sdk.decorators import agent, graph, workflow

@graph(name="research_agent_graph")
@agent(name="research_agent")
class ResearchAgent:
    def get_workflow(self): return self.workflow

@graph(name="writing_agent_graph")
@agent(name="writing_agent")
class WritingAgent:
    def get_workflow(self): return self.workflow

@workflow(name="multi_agent_pipeline")
async def run_pipeline(topic: str) -> str: ...

async def main():
    session_start()
    await run_pipeline("...")
```

**CrewAI multi-crew pipeline:**
```python
from ioa_observe.sdk.decorators import tool, workflow

@workflow(name="research_crew")
def run_research_crew(topic: str) -> str:
    crew = Crew(agents=[researcher, analyst], ...)
    return crew.kickoff()

@workflow(name="publishing_crew")
def run_publishing_crew(research: str) -> str:
    crew = Crew(agents=[editor, publisher], ...)
    return crew.kickoff()

@workflow(name="pipeline")
def run_pipeline(topic: str) -> str:
    research = run_research_crew(topic)
    return run_publishing_crew(str(research))

def main():
    session_start()
    run_pipeline("...")
```

**OpenAI SDK multi-agent:**
```python
from ioa_observe.sdk.decorators import agent, tool, workflow

@agent(name="research_agent")
def run_research_agent(topic: str) -> str: ...

@agent(name="writing_agent")
def run_writing_agent(research: str) -> str: ...

@workflow(name="orchestrator")
def run_orchestrator(topic: str) -> str:
    research = run_research_agent(topic)
    return run_writing_agent(research)

def main():
    session_start()
    run_orchestrator("...")
```

---

## What NOT to Do

- Don't add `@agent` to every function — only to orchestration-level functions
- Don't add `@tool` to helper utilities that aren't agent-callable tools
- Don't add `@graph` without `@agent` on workflow wrapper classes
- Don't call `Observe.init()` more than once
- Don't import unused decorators
- Don't add `session_start()` inside loops — once per top-level invocation
