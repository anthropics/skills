---
name: langgraph
description: "Build multi-agent AI applications with LangGraph. TRIGGER when: code imports `langgraph`, `StateGraph`, `MessagesState`, or user asks about LangGraph graphs, agent nodes, ToolNode, conditional edges, checkpointers, or multi-agent architectures. DO NOT TRIGGER when: code uses other orchestration frameworks (CrewAI, AutoGen, plain LangChain), or for general LLM/ML tasks."
---

# Building Multi-Agent Applications with LangGraph

This skill helps you design and implement LangGraph-based agent systems. It covers state management, graph construction, multi-agent routing, tool execution, and persistence.

---

## Quick Start

```python
from langgraph.graph import StateGraph, START, END, MessagesState
from langgraph.prebuilt import ToolNode
from langchain_core.messages import SystemMessage

# 1. Define state
class State(MessagesState):
    agent_type: str  # add custom fields on top of messages

# 2. Define an agent node
def my_agent(state: State) -> dict:
    llm_with_tools = llm.bind_tools(tools)
    response = llm_with_tools.invoke([SystemMessage(content="You are...")] + state["messages"])
    return {"messages": [response]}

# 3. Routing function
def should_continue(state: State):
    last = state["messages"][-1]
    return "tools" if getattr(last, "tool_calls", None) else END

# 4. Build and compile
builder = StateGraph(State)
builder.add_node("agent", my_agent)
builder.add_node("tools", ToolNode(tools))
builder.add_edge(START, "agent")
builder.add_conditional_edges("agent", should_continue, ["tools", END])
builder.add_edge("tools", "agent")
graph = builder.compile()
```

---

## Core Concepts

### State

Always extend `MessagesState` for conversational agents — it provides the `messages` list with built-in message append reducer:

```python
from langgraph.graph import MessagesState
from typing import Literal

AgentType = Literal["simple", "analyst", "researcher"]

class State(MessagesState):
    """Extend MessagesState with routing metadata."""
    agent_type: AgentType
    context: dict | None  # any extra fields your graph needs
```

**Key rules:**
- `messages` uses an append reducer automatically — returning `{"messages": [new_msg]}` appends, not replaces.
- Custom fields (like `agent_type`) are last-write-wins by default.
- Define state in one place (`state.py`) and import everywhere — never redefine it.

### Nodes

Each node is a Python function that takes `State` and returns a dict of state updates:

```python
def agent_node(state: State) -> dict:
    response = llm.invoke(state["messages"])
    return {"messages": [response]}  # appended to messages list
```

For specialist agents with their own LLM, use a lazy singleton pattern to avoid re-initializing the model on every call:

```python
_llm = None

def _get_llm():
    global _llm
    if _llm is None:
        _llm = ChatOpenAI(model="gpt-4o").bind_tools(AGENT_TOOLS)
    return _llm

def specialist_agent(state: State) -> dict:
    response = _get_llm().invoke(
        [SystemMessage(content=SYSTEM_PROMPT)] + list(state["messages"])
    )
    return {"messages": [response]}
```

### Edges and Routing

**Static edge:** always goes from A to B.
```python
builder.add_edge("tools", "agent")
```

**Conditional edge:** function decides next node at runtime.
```python
def route(state: State) -> str:
    return "tools" if getattr(state["messages"][-1], "tool_calls", None) else END

builder.add_conditional_edges("agent", route, ["tools", END])
```

**Multi-destination routing:** route to one of several nodes.
```python
def route_after_router(state: State) -> AgentType:
    return state["agent_type"]  # "simple" | "analyst" | "researcher"

builder.add_conditional_edges(
    "router",
    route_after_router,
    ["simple", "analyst", "researcher"],  # explicit allowlist
)
```

### ToolNode

Use `ToolNode` from `langgraph.prebuilt` for automatic tool dispatch — it reads `tool_calls` from the last message and executes each tool:

```python
from langgraph.prebuilt import ToolNode

all_tools = list({t.name: t for t in (TOOLS_A + TOOLS_B)}.values())  # deduplicate by name
tools_node = ToolNode(all_tools)
builder.add_node("tools", tools_node)
```

After `ToolNode` executes, route back to the originating agent:

```python
def route_after_tools(state: State) -> AgentType:
    return state["agent_type"]  # return to whichever agent called the tools

builder.add_conditional_edges("tools", route_after_tools, ["simple", "analyst", "researcher"])
```

---

## Multi-Agent Pattern

For systems with multiple specialist agents, use a router node that classifies intent and sets `agent_type`:

```python
# router.py
from pydantic import BaseModel, Field

class IntentOutput(BaseModel):
    agent_type: AgentType = Field(description="Which specialist handles this query")
    query_type: str = Field(description="Category of the request")

def intent_router(state: State) -> dict:
    """LLM-based intent classification node."""
    router_llm = base_llm.with_structured_output(IntentOutput)
    result = router_llm.invoke([SystemMessage(content=ROUTER_PROMPT)] + list(state["messages"]))
    return {
        "agent_type": result.agent_type,
        "context": {"query_type": result.query_type},
    }
```

**Graph wiring:**
```
START → router → [simple | analyst | researcher]
                       ↓ (tool_calls)
                     tools
                       ↓ (route_after_tools)
              [simple | analyst | researcher]
                       ↓ (no tool_calls)
                      END
```

**Handling greetings / short-circuit responses from the router:**

```python
def intent_router(state: State) -> dict:
    result = router_llm.invoke(messages)
    if result.is_greeting:
        # Short-circuit: inject a canned reply and mark agent_type
        return {
            "agent_type": "simple",
            "messages": [AIMessage(content="Hello! How can I help?")],
        }
    return {"agent_type": result.agent_type}
```

---

## Persistence (Checkpointers)

### MemorySaver (in-process, dev/testing)

```python
from langgraph.checkpoint.memory import MemorySaver

graph = builder.compile(checkpointer=MemorySaver())

# Invoke with a thread_id for per-conversation history
result = graph.invoke(
    {"messages": [HumanMessage(content="Hello")]},
    config={"configurable": {"thread_id": "user-123"}},
)
```

### Dual-mode compilation (local vs platform)

When running under LangGraph Platform, the runtime injects its own checkpointer. Build the graph without one at module level, and provide a separate factory for local use:

```python
def _build_graph(checkpointer=None):
    # ... build logic ...
    return builder.compile(checkpointer=checkpointer, name="my-graph")

def build_graph_with_memory():
    """Use for local FastAPI; LangGraph Platform injects its own checkpointer."""
    return _build_graph(checkpointer=MemorySaver())

# Module-level graph for langgraph dev / LangGraph Platform
graph = _build_graph()
```

---

## Response Normalization

Some LLMs (e.g., Gemini 2.5 thinking models) return `content` as a list of parts including thinking blocks. Normalize before storing in state:

```python
from langchain_core.messages import AIMessage, BaseMessage

def flatten_response(response: BaseMessage) -> BaseMessage:
    """Collapse multi-part content (thinking models) to a single string."""
    if isinstance(response.content, str):
        return response
    if isinstance(response.content, list):
        text_parts = []
        for part in response.content:
            if isinstance(part, dict):
                if part.get("type") in ("thinking", "redacted_thinking"):
                    continue  # skip internal reasoning blocks
                text = part.get("text", "")
            else:
                text = part
            if isinstance(text, str) and text.strip():
                text_parts.append(text.strip())
        return AIMessage(
            content=" ".join(text_parts),
            tool_calls=getattr(response, "tool_calls", []) or [],
            response_metadata=getattr(response, "response_metadata", {}),
        )
    return response
```

Use it in every agent node:
```python
response = flatten_response(_get_llm().invoke(messages))
return {"messages": [response]}
```

---

## Tools

Define tools with the `@tool` decorator from LangChain:

```python
from langchain_core.tools import tool

@tool
def get_stock_price(symbol: str) -> str:
    """Fetch the current price for a stock symbol."""
    # implementation
    return f"{symbol}: ₹1234.56"
```

Group tools per agent tier and deduplicate across a shared `ToolNode`:

```python
SIMPLE_TOOLS = [get_price, get_news]
ANALYST_TOOLS = [get_price, get_financials, get_charts]

_ALL_TOOLS = list({t.name: t for t in SIMPLE_TOOLS + ANALYST_TOOLS}.values())
tools_node = ToolNode(_ALL_TOOLS)
```

---

## Common Patterns

### Limiting conversation history sent to LLM

```python
MAX_HISTORY = 10

def agent_node(state: State) -> dict:
    recent = list(state["messages"])[-MAX_HISTORY:]
    response = llm.invoke([SystemMessage(content=PROMPT)] + recent)
    return {"messages": [response]}
```

### Error handling in router

```python
def intent_router(state: State) -> dict:
    try:
        result = router_llm.invoke(messages)
        return {"agent_type": result.agent_type}
    except Exception as e:
        logger.error("Router failed, defaulting: %s", e)
        return {"agent_type": "simple"}  # safe fallback
```

### Streaming graph output

```python
for chunk in graph.stream(
    {"messages": [HumanMessage(content=query)]},
    config={"configurable": {"thread_id": thread_id}},
    stream_mode="values",
):
    last_msg = chunk["messages"][-1]
    if hasattr(last_msg, "content") and last_msg.content:
        print(last_msg.content)
```

---

## Project Structure

```
src/
  agent/
    state.py          # State, AgentType, QueryType — single source of truth
    graph.py          # StateGraph assembly and compilation
    router.py         # Intent router node + route_after_intent()
    prompts.py        # System prompt factories per agent
    tools.py          # Shared tools
    agents/
      simple.py       # Fast agent + SIMPLE_TOOLS list
      analyst.py      # Analyst agent + ANALYST_TOOLS list
    __init__.py       # Re-export agents and tool lists
```

---

## Key Imports Reference

```python
# Graph
from langgraph.graph import StateGraph, START, END, MessagesState
from langgraph.graph.state import CompiledStateGraph
from langgraph.prebuilt import ToolNode
from langgraph.checkpoint.memory import MemorySaver
from langgraph.checkpoint.base import BaseCheckpointSaver

# LangChain core
from langchain_core.messages import AIMessage, HumanMessage, SystemMessage, BaseMessage
from langchain_core.tools import tool, BaseTool
from langchain_core.runnables import Runnable

# Structured output
from pydantic import BaseModel, Field
```

---

## Pitfalls to Avoid

- **Don't redefine State** in multiple files — import from a single `state.py`.
- **Don't forget the allowlist** in `add_conditional_edges` when routing to multiple named nodes — LangGraph validates against it.
- **Don't call `builder.compile()` twice** — compile once and reuse the graph.
- **Don't return the full messages list** from a node — only return new messages; the reducer appends them.
- **Deduplicate tools** by name before passing to `ToolNode` to avoid duplicate tool call errors.
- **Don't initialize LLMs at import time** — use lazy singletons so the API key is read at runtime.
- **Pass `name=` to `builder.compile()`** — it labels the graph in LangGraph Studio traces.
