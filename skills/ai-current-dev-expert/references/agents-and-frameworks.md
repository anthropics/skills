# AI Agents and Frameworks (2025-2026)

## LangGraph: Production Multi-Agent Architecture

LangGraph is the production standard for stateful multi-agent workflows. It models agent behavior as a directed graph where nodes are functions (or LLM calls) and edges are transitions between them.

**Core concepts**:
- **State**: A typed dictionary shared across all nodes in the graph
- **Nodes**: Functions that read and write state (LLM calls, tool executions, human checkpoints)
- **Edges**: Connections between nodes, including conditional edges based on state
- **Checkpoints**: Persistent state snapshots enabling pause/resume and human-in-the-loop

**Key architectural patterns**:

### Supervisor Pattern
A supervisor LLM routes tasks to specialized sub-agents based on their capabilities. Each sub-agent maintains its own scratchpad; supervisor orchestrates communication and delegation. Best for: customer service (routing to billing, technical, or escalation agents), code review (routing to security, style, and correctness agents).

```python
from langgraph.graph import StateGraph, END

def supervisor(state):
    # Supervisor decides which agent to call next
    next_agent = llm.invoke(f"Given task: {state['task']}, route to: {', '.join(agents)}")
    return {"next": next_agent.content}

graph = StateGraph(AgentState)
graph.add_node("supervisor", supervisor)
graph.add_node("researcher", researcher_agent)
graph.add_node("writer", writer_agent)
graph.add_conditional_edges("supervisor", lambda s: s["next"], 
                            {"researcher": "researcher", "writer": "writer", END: END})
```

### Scatter-Gather Pattern
Distribute subtasks to multiple agents in parallel, then consolidate results. LangGraph supports parallel execution via `Send` API. Best for: parallel web searches, multi-perspective analysis, ensemble approaches.

### Human-in-the-Loop with Checkpoints
```python
from langgraph.checkpoint.memory import MemorySaver

checkpointer = MemorySaver()  # Use PostgresSaver for production
graph = workflow.compile(checkpointer=checkpointer, interrupt_before=["risky_action"])

# First run — pauses at "risky_action"
result = graph.invoke(inputs, config={"configurable": {"thread_id": "1"}})

# Human reviews, then resume
graph.invoke(None, config={"configurable": {"thread_id": "1"}})
```

**When to use LangGraph vs. direct API**:
- Use LangGraph: multi-step workflows with conditional branching, stateful agents across multiple turns, human-in-the-loop checkpoints, parallel execution
- Use direct API + tool runner: simple single-agent loops, you want full control of the loop logic, adding a framework adds more complexity than value

---

## CrewAI: Role-Based Multi-Agent Collaboration

CrewAI simplifies multi-agent coordination through a role/task/crew abstraction. Better than LangGraph when the coordination pattern is fixed and role-based rather than dynamic.

**When to use CrewAI over LangGraph**:
- Fixed collaboration patterns (researcher → writer → editor)
- Roles are stable and well-defined
- You want faster setup than LangGraph's graph modeling

**CrewAI vs. LangGraph**:
- CrewAI: Higher-level, faster to prototype, less flexible
- LangGraph: More control, handles complex conditional flows, better for production

---

## Model Context Protocol (MCP)

MCP (Anthropic, Nov 2024 → Linux Foundation 2025) is the universal standard for connecting AI applications to external tools. Adopted by OpenAI, Google DeepMind, and Microsoft within months.

**What MCP provides**:
- **Tools**: Functions the model can call (search, database queries, API calls)
- **Resources**: Data the model can read (file contents, database records)
- **Prompts**: Reusable prompt templates

**Transports**:
- **Streamable HTTP**: Remote servers, stateless JSON. Simpler to scale. Use for production.
- **stdio**: Local tools, same machine. Use for CLI tools and local development.

**Building an MCP server (TypeScript — recommended)**:
```typescript
import { McpServer } from "@modelcontextprotocol/sdk/server/mcp.js";
import { z } from "zod";

const server = new McpServer({ name: "my-tools", version: "1.0.0" });

server.registerTool("search_database", {
  description: "Search the product database by query",
  inputSchema: z.object({ query: z.string(), limit: z.number().optional() }),
  annotations: { readOnlyHint: true }
}, async ({ query, limit = 10 }) => {
  const results = await db.search(query, limit);
  return { content: [{ type: "text", text: JSON.stringify(results) }] };
});
```

**MCP security**: Prompt injection via MCP tool results is OWASP Top 10 AI risk #1. Sanitize all external data before returning to the model. Don't trust tool result content as instructions.

**When to build MCP vs. tool use directly**: Build MCP when you want the tools to work across multiple AI applications (Claude Code + Claude Desktop + your app). Use direct tool use when tools are application-specific.

---

## Agent Memory Architecture

Production agents need persistent memory — not just a long context window. Use this four-tier architecture:

### Tier 1: Working Memory (in-context)
The active context window. Session-bound. For Claude: up to 1M tokens. Use prompt caching to reduce costs on stable portions.

### Tier 2: Episodic Memory (conversation history)
Prior interactions across sessions. Storage: vector DB (for semantic search across history) + relational DB (for ground truth/timestamps). Retrieval: semantic similarity to find relevant past conversations.

Implementation: on session end, embed the conversation summary and store with metadata (user ID, timestamp, topic tags). On session start, retrieve top-K relevant past interactions.

### Tier 3: Semantic Memory (factual knowledge)
Facts, entity relationships, domain knowledge. Storage: vector DB for similarity search; knowledge graph for relationship traversal. This is where RAG knowledge bases live.

### Tier 4: Procedural Memory (skills/workflows)
Stored prompts, code templates, tool-use patterns that worked well. Retrieved and injected as few-shot examples when similar tasks arise.

**Key insight**: External memory is not a workaround for limited context windows — it's the correct architectural choice for agents that need knowledge that persists across sessions and scales beyond any context window.

**Production storage**: PostgreSQL + pgvector for a unified database covering episodic, semantic, and procedural memory. Redis for session working memory cache.

---

## Tool Design Best Practices

**Tool granularity**: Prefer comprehensive API coverage over high-level workflow tools. Workflow tools are convenient but limit agent flexibility. The agent can compose basic tools; it can't decompose an overly broad workflow tool.

**Tool naming**: Use consistent prefixes with action-oriented names: `github_create_issue`, `github_list_repos`, `github_search_code`. The model uses names and descriptions to select tools — clarity matters.

**Tool descriptions**: Include what the tool does, when to use it, what it returns, and limitations. The description is the primary tool-selection signal.

**Error messages**: Return actionable errors with specific next steps. Don't just say "Error: invalid input." Say "Error: date format must be YYYY-MM-DD. Received: 01/15/2025."

**Idempotency**: Mark destructive tools with `destructiveHint: true`. Mark read-only tools with `readOnlyHint: true`. This allows the agent and user to make informed decisions about which actions need confirmation.

**Pagination**: For tools that return lists, always support pagination parameters. Return metadata about total results. Agents that can't paginate will miss data or blow up context windows.

---

## Agentic Design Principles

### Start minimal
Don't build an agent when a simple pipeline works. Agents are more expensive, harder to debug, and can fail in non-deterministic ways. Use the simplest architecture that meets requirements:
1. Single LLM call
2. LLM call + structured output
3. Pipeline (fixed sequence of LLM calls)
4. Agent (model decides trajectory)

### Tool surface design
Bash tool + good file system access beats many specialized tools for code agents. Give agents broad, composable primitives rather than many narrow tools.

### Context editing vs. compaction vs. external memory
- Context editing (removing irrelevant messages): Manually curate what stays in context
- Compaction (server-side summarization): Automatic; use for long conversations
- External memory (vector DB retrieval): For knowledge that needs to persist across sessions

### Fail fast and visibly
Agents that silently do the wrong thing are worse than agents that fail loudly. Add assertions, output validation, and explicit error returns. Never let an agent silently continue after a failed tool call.
