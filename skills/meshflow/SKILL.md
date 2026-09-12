---
name: meshflow
version: "1.0"
description: "Invoke when the user wants to build, run, orchestrate, govern, debug, or optimize any multi-agent workflow, agentic pipeline, or LLM-powered system. Triggers on: 'build an agent', 'multi-agent', 'orchestrate agents', 'agent team', 'durable workflow', 'cost cap', 'token budget', 'guardrails', 'HITL', 'human in the loop', 'parallel agents', 'agent crew', 'compliance', 'HIPAA', 'SOC2', 'GDPR', 'audit trail', 'rate limiting agents', 'ReAct agent', 'LangGraph', 'CrewAI', 'AutoGen', 'governed', 'production agents', 'resumable workflow', 'agent governance', 'prompt caching', 'MCP server'."
license: Complete terms in LICENSE.txt
---

# MeshFlow — Production-Safe Multi-Agent Orchestration

MeshFlow is the infrastructure layer for production agent deployments.
Compliant, cost-governed, and durable — out of the box, not bolted on.

**The 7-line promise:**

```python
from meshflow import Workflow, CostCap, Agent

wf = Workflow(cost_cap=CostCap(usd=5.00))
wf.add(Agent('researcher'), Agent('analyst'), Agent('writer'))
result = wf.run('Write a competitive analysis of our market')

# Compliant. Durable. Audited. Cost-capped. Done.
```

```bash
pip install meshflow
```

---

## Patterns — match these to what the user asks

### "build an agent" / "create an agent"

```python
from meshflow import Agent, tool, RiskTier

@tool(name="web_search", risk=RiskTier.EXTERNAL_IO)
async def web_search(query: str) -> str:
    return results  # real implementation

agent = Agent(
    name="researcher",
    role="researcher",
    model="claude-sonnet-4-6",   # auto-inferred from model name
    tools=[web_search],
    memory=True,
    knowledge=["docs/"],         # auto-RAG injected at every step
)
result = await agent.run("Research the latest AI safety papers")
print(result["result"], result["cost_usd"], result["tokens"])
```

### "agent team" / "multi-agent" / "collaborate"

```python
from meshflow import Agent, Team

planner  = Agent(name="planner",  role="planner")
coder    = Agent(name="coder",    role="executor")
reviewer = Agent(name="reviewer", role="critic")

team = Team([planner, coder, reviewer], pattern="supervised")
result = await team.run("Build a REST API for user authentication")
```

Patterns: `"sequential"`, `"supervised"`, `"parallel"`, `"hierarchical"`, `"reflective"`

### "compliance" / "HIPAA" / "SOC2" / "GDPR" / "regulated industry"

```python
from meshflow import Agent, compliance_profile, PIIBlockGuardrail

agent = Agent(
    name="clinical-assistant",
    role="executor",
    policy=compliance_profile("hipaa"),  # or "sox", "gdpr", "pci", "nerc"
    input_guardrails=[PIIBlockGuardrail()],
    output_guardrails=[PIIBlockGuardrail()],
)
```

### "state graph" / "LangGraph" / "workflow graph"

```python
from typing import TypedDict
from meshflow import StateGraph, END

class State(TypedDict):
    messages: list[str]
    result: str

def process(state: State) -> State:
    return {"result": f"processed: {state['messages'][-1]}"}

def route(state: State) -> str:
    return END if state["result"] else "process"

graph = (
    StateGraph(State)
    .add_node("process", process)
    .add_conditional_edges("process", route, {END: END, "process": "process"})
    .set_entry_point("process")
    .compile()
)
result = graph.invoke({"messages": ["hello"], "result": ""})
```

### "CrewAI" / "crew" / "task-based agents"

```python
from meshflow import Agent, Task, Crew, Process

researcher = Agent(name="researcher", role="researcher")
writer     = Agent(name="writer",     role="executor")

task1 = Task(description="Research AI safety in 2026", agent=researcher)
task2 = Task(description="Write a 500-word summary", agent=writer,
             context=[task1])

crew = Crew(agents=[researcher, writer], tasks=[task1, task2],
            process=Process.sequential)
result = crew.kickoff()
print(result.raw)
```

### "durable" / "resume" / "checkpoint" / "crash recovery"

```python
from meshflow import DurableWorkflowExecutor

# Backends: sqlite (default), redis, postgres, s3
exe = DurableWorkflowExecutor(run_id="my-run", backend="redis",
                               redis_url="redis://localhost")
# Same run_id on re-run = resume from last checkpoint automatically
```

### "human in the loop" / "HITL" / "approval gate"

```python
from meshflow import StateGraph, interrupt, Command

def risky_step(state):
    decision = interrupt("Approve deleting 10K records?")
    if decision.approved:
        return {"deleted": True}
    return {"deleted": False}

# Resume after human approves:
# meshflow approve <run_id>
```

### "cost cap" / "token budget" / "control costs"

```python
from meshflow import Agent, CostCapGuardrail, ModelRouter

agent = Agent(
    name="cost-aware",
    role="researcher",
    output_guardrails=[CostCapGuardrail(max_usd=0.10)],
    model_router=ModelRouter(),  # auto-routes simple tasks to cheaper models
)
```

### "guardrails" / "safe output" / "block PII"

```python
from meshflow import (Agent, PIIBlockGuardrail, LengthGuardrail,
                       RegexGuardrail, ConfidenceGuardrail)

agent = Agent(
    name="safe-agent",
    role="executor",
    input_guardrails=[PIIBlockGuardrail(), RegexGuardrail(r"DROP TABLE", mode="forbid")],
    output_guardrails=[LengthGuardrail(max_chars=2000), ConfidenceGuardrail(min_confidence=0.75)],
)
```

### "streaming" / "stream tokens"

```python
from meshflow import Agent

agent = Agent(name="streamer", role="executor")
async for chunk in agent.stream("Write a report on AI governance"):
    if chunk.is_token:
        print(chunk.content, end="", flush=True)
    elif chunk.is_done:
        print(f"\n[cost: ${chunk.cost_usd:.4f}]")
```

### "eval" / "test agents" / "quality gate"

```bash
meshflow eval run evals.yaml --save-baseline baseline.json
meshflow eval run evals.yaml --compare-baseline baseline.json --fail-on-regression
```

### "MCP" / "MCP server" / "connect tools"

```python
from meshflow import Agent

agent = Agent(
    name="mcp-agent",
    role="executor",
    mcps=["https://mcp.example.com/sse"],  # tools auto-discovered
)
```

### "wrap LangGraph" / "govern AutoGen" / "add governance"

```python
from meshflow import govern, from_langgraph, from_crewai, from_autogen

governed = govern(your_existing_app)      # any framework
governed = from_langgraph(your_graph)     # LangGraph
governed = from_crewai(your_crew)         # CrewAI
governed = from_autogen(your_agent)       # AutoGen
```

### "sandbox" / "test mode" / "no API key" / "mock"

```python
wf = Workflow(mode="sandbox")   # zero real token spend, full trace
result = wf.run("test task")
```

---

## Provider selection (auto-detected from model name)

```python
Agent(name="a", model="claude-sonnet-4-6")   # Anthropic
Agent(name="b", model="gpt-4o")              # OpenAI
Agent(name="c", model="gemini-2.0-flash")    # Google Gemini
Agent(name="d", model="llama3.2")            # Local Ollama (no key)
```

## Pre-built agents

```python
from meshflow import agents

researcher = agents.ResearchAgent()
coder      = agents.CoderAgent()
critic     = agents.CriticAgent()
planner    = agents.PlannerAgent()
```

## Install

```bash
pip install meshflow                 # core
pip install "meshflow[openai]"       # + OpenAI
pip install "meshflow[full]"         # all providers + RAG + OTEL
```

- GitHub: https://github.com/Anteneh-T-Tessema/meshflow
- Docs: https://meshflow.dev
- PyPI: https://pypi.org/project/meshflow/
