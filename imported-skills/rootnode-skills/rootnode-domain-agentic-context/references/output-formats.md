# Output Formats — Agentic & Context Engineering

Complete output format specifications for agent system deliverables. Each format is an `<output_format>` block ready to paste into the output layer of a Claude prompt.

## Table of Contents

1. [Agent System Prompt](#agent-system-prompt) — Complete, deployable system prompt for an AI agent
2. [Tool Definition Specification](#tool-definition-specification) — Tool definitions formatted for API integration
3. [Agent Architecture Blueprint](#agent-architecture-blueprint) — Comprehensive agent system design document
4. [Context Management Plan](#context-management-plan) — Context engineering specification for multi-turn agents

---

## Agent System Prompt

**Use when:** The deliverable is a complete, ready-to-deploy system prompt for an AI agent. This format produces the artifact that goes directly into an LLM API call's system prompt field or a Claude Project's Custom Instructions.

```xml
<output_format>
Produce a complete agent system prompt with these sections, in this order:

**Agent Identity & Mission** (2-3 sentences): Who this agent is, what it does, and the boundaries of its role. Written entirely as imperatives — "You are..." and "You do..." — not descriptions of what the agent is capable of. End with one sentence on what is explicitly outside this agent's scope.

**Behavioral Constraints** (bulleted imperatives): Hard rules the agent must follow. What it must never do. When it must escalate to a human. What requires user confirmation before acting. What information it must never fabricate. These are the safety rails — they override all other instructions. Order by severity: safety constraints first, then scope constraints, then quality constraints.

**Tool Usage Instructions** (per-tool): For each tool, specify: when to use it, when not to use it (if confusion with another tool is likely), any preference ordering when multiple tools could work, and how to interpret its responses. This section references the tool definitions but adds behavioral guidance that the tool descriptions alone do not capture.

**Context Management Instructions**: How the agent should handle long conversations — when to summarize prior context, how to handle conflicting information from different turns, what to do when a user references something from much earlier in the conversation, and how to manage its own context window if it is operating in an agentic loop.

**Error Handling Instructions**: What to do when tools fail (with specific recovery strategies, not just "try again"). What to do when the user's request is ambiguous. What to do when the agent is uncertain about the right approach. What to do when the task exceeds its capabilities. The default for any unspecified situation should be conservative — acknowledge, explain what it can determine, and ask for guidance.

**Output Standards**: How the agent communicates with the user — tone, format, default length, when to show its reasoning vs. just show results, when to ask for confirmation vs. proceed independently, and how to handle situations where it has partial information.

Scale length to agent complexity. A simple tool-using assistant: 500-800 words. A complex autonomous agent: 1500-2500 words. Every instruction must direct behavior — remove anything that describes capabilities without specifying what to do with them.
</output_format>
```

**Watch for length inflation:** Claude tends to produce verbose agent system prompts. Every sentence must direct behavior. If a sentence describes a capability without specifying what to do with it, remove it.

---

## Tool Definition Specification

**Use when:** The deliverable is a complete set of tool definitions for an agent, formatted for direct integration into an API tool-use configuration. The tool definitions are the Agent-Computer Interface — they determine whether the agent can effectively use its tools.

```xml
<output_format>
Produce a complete tool definition specification with these sections:

**Tool Inventory** (table): Name, one-line purpose, usage frequency estimate (core vs. supplementary), and namespace grouping for each tool. Core tools are used in most interactions; supplementary tools handle edge cases or specific sub-tasks.

**Per-Tool Definition** (for each tool):
- Name: Following namespace conventions if tools group logically (e.g., 'kb_search', 'kb_get_article', 'ticket_create', 'ticket_update')
- Description: Written for LLM consumption — what it does, when to use it, when not to use it, what success looks like. Instruction-like, not documentation-like.
- Parameter schema: Each parameter with type, description (self-documenting names, natural-language enums), and required/optional status. Minimize parameter count.
- Return format: What the agent receives back, with field descriptions for any non-obvious fields. Design for token efficiency — return only what the agent needs for its next decision.
- Error responses: Each anticipated error with a plain-language description and a recovery instruction the agent can follow.
- Usage examples: 1-2 representative scenarios showing the tool call and expected result. Include one error scenario for tools where errors are common.

**Tool Interaction Map**: Which tools are commonly used together, which tools' outputs feed into other tools' inputs, and any ordering constraints. Presented as a concise dependency description, not an exhaustive matrix.

**Disambiguation Guide**: For any tools with overlapping purposes, explicit guidance on which tool to choose under what conditions. This section is written as system prompt instructions — it goes into the agent's system prompt, not the tool definitions themselves.

Scale to tool count. Approximately 150-300 words per tool definition, plus the inventory and interaction map.
</output_format>
```

**Watch for bloated tool responses:** Claude designs tool response schemas that include every field the API returns. Each token in a tool response consumes attention budget. Include only the fields the agent needs for its next decision.

---

## Agent Architecture Blueprint

**Use when:** The deliverable is a comprehensive design document for an agent system — the specification that a developer uses to implement and maintain the agent. This is the highest-level agentic output, combining system prompt design, tool design, context architecture, and evaluation criteria into a single document.

```xml
<output_format>
Produce a comprehensive agent architecture blueprint with these sections:

**System Overview** (1-2 paragraphs): What the agent does, who uses it, and what problem it solves. Written for a developer who needs to build and maintain this system, not for a business audience.

**Architecture Decision** (1 paragraph): Whether this is a single agent, a workflow, or a multi-agent system, and why. References the decomposition analysis — what alternatives were considered and why they were rejected.

**Component Specification**: For each component (LLM, tools, retrieval system, memory/state management, orchestration layer if multi-agent):
- What it does in this system
- What technology or service implements it
- How it interfaces with other components
- What its failure modes are

**Context Architecture** (1-2 paragraphs + structured summary): What information the agent sees at each step, how it is populated, and how it is managed across turns. Include the zone breakdown (persistent, session-scoped, turn-scoped, ephemeral) with approximate token budgets. Specify the compaction and overflow strategies.

**System Prompt** (complete or detailed outline): Either the full system prompt ready for deployment, or a detailed structural outline with key instructions specified and sections marked for customization.

**Tool Definitions** (complete or summary): Either the full tool definitions, or a summary table with the most critical tools fully specified and others outlined.

**Failure Modes & Recovery** (structured list): Top 5-10 failure modes with: detection mechanism, recovery strategy, and escalation criteria. Ordered by frequency × impact.

**Evaluation Criteria**: How to measure whether the agent is working — specific metrics (task completion rate, tool-use accuracy, escalation rate, average tool calls per task, token consumption per task, user satisfaction if applicable) with target thresholds where possible.

**Known Limitations** (bulleted): What this agent cannot do, where it will fail, and what users should not expect from it. Honest limitations prevent over-reliance and scope creep.

Total length: 1500-3000 words depending on system complexity.
</output_format>
```

**Watch for over-engineering:** Claude produces architecture blueprints that propose unnecessary components. Every component must justify its existence. If a component's failure modes section is longer than its value-add description, that is a signal the complexity is not worth the cost.

---

## Context Management Plan

**Use when:** The deliverable is the context engineering specification for an agent — how information enters, persists in, and exits the context window across turns. This is the operational companion to the Context Window Architecture reasoning approach — the reasoning produces the design decisions, this format structures them into an implementable specification.

```xml
<output_format>
Produce a context management plan with these sections:

**Context Zones** (table): Each zone of the context window with:
- Zone name and purpose
- Persistence class (permanent, session, turn, ephemeral)
- Approximate token budget (normal and peak)
- Content examples
- Management strategy (static, refreshed, retrieved, summarized)

**Population Strategy**: How each zone gets its content:
- Permanent zones: What is hardcoded in the system prompt vs. injected at session start
- Session zones: What triggers loading (user authentication, task selection, preference retrieval)
- Turn zones: What tools or retrieval mechanisms supply the content, and what triggers them
- How just-in-time retrieval is balanced against pre-loaded context — what is always present vs. fetched on demand, and why

**Overflow Protocol**: What happens when the total context approaches the window limit:
- Pruning priority order (what gets evicted first, second, third)
- Compaction strategy for conversation history (what is preserved: decisions, open issues, key facts; what is discarded: verbose exchanges, superseded information, consumed tool results)
- Structured note-taking mechanism if the agent runs long-horizon tasks (what the agent writes to external state, when, and how it reads it back after compaction)
- Inviolable content that must never be pruned regardless of window pressure

**Turn Lifecycle**: What happens to the context at each turn — a step-by-step walkthrough of a representative 3-5 turn interaction showing: what is added to the context, what is updated, what is pruned, and what is summarized. This makes the abstract architecture concrete.

**Token Budget** (table): Estimated token allocation per zone under normal conditions and peak conditions, summing to the target model's context window size minus generation headroom (at least 20%).

Total length: 800-1500 words.
</output_format>
```

**Watch for missing implementation detail:** Claude produces context plans that describe what should happen without specifying how. For each management strategy, the plan must specify the implementation mechanism — what code, prompt, or system process enforces the policy. A context architecture without implementation mechanisms is a wish list, not a design.
