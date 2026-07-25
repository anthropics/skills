# Reasoning Approaches — Agentic & Context Engineering

Complete reasoning specifications for agent system design. Each approach is a `<reasoning>` block ready to paste into the reasoning layer of a Claude prompt.

## Table of Contents

1. [Agent vs. Workflow Decomposition](#agent-vs-workflow-decomposition) — Deciding whether to build an agent, workflow, or single prompt
2. [Tool Interface Design (ACI Design)](#tool-interface-design-aci-design) — Designing tool definitions optimized for LLM consumption
3. [Context Window Architecture](#context-window-architecture) — Designing information management across turns
4. [Failure Mode & Recovery Design](#failure-mode--recovery-design) — Anticipating failures and designing recovery strategies
5. [Multi-Agent Coordination](#multi-agent-coordination) — Designing coordination protocols for multi-agent systems

---

## Agent vs. Workflow Decomposition

**Use when:** You need to decide whether a task requires an autonomous agent, a structured workflow with LLM steps, or a single well-crafted prompt. This is the first reasoning step for any agentic project — getting it wrong is the most expensive mistake in agent design.

```xml
<reasoning>
Decompose the architecture decision as follows:
1. Characterize the task's variability: Is the sequence of steps predictable (workflow), or does it depend on intermediate results (agent)? If the steps are always the same regardless of input, an agent adds complexity without benefit — use a workflow.
2. Assess the decision density: How many decisions must the LLM make per task completion? One or two decisions can be handled by a workflow with conditional branches. Dozens of interdependent decisions where the right choice depends on context that emerges mid-execution may need agent autonomy.
3. Evaluate the error tolerance: What happens when the LLM makes a wrong decision? In low-stakes or easily reversible contexts, agent autonomy is acceptable. In high-stakes or irreversible contexts, structured workflows with human checkpoints are safer.
4. Consider the tool landscape: How many tools does the system need, and does the right tool depend on context that only emerges mid-execution? Many tools with context-dependent selection favor agents. Few tools with predictable usage favor workflows.
5. Apply the simplicity test: Could a single prompt with well-structured context accomplish this? If yes, start there. Could a two-step prompt chain accomplish this? If yes, use that. Could a deterministic workflow with LLM steps at defined points accomplish this? If yes, use that. Reach for an autonomous agent only when simpler architectures demonstrably fail — when the task requires the LLM to dynamically decide its next action based on results it cannot predict in advance.
6. Recommend the simplest architecture that meets the task's requirements. State what specific increase in task complexity or variability would justify moving to the next level of sophistication.
</reasoning>
```

**Watch for:** Claude gravitates toward recommending agents because they are more interesting to design. Step 5 directly counters this, but if the output still defaults to agent recommendations for tasks that could be workflows, add: *"A well-designed workflow outperforms a poorly designed agent in reliability, cost, and latency. Recommend an agent only if you can articulate what specific capability the agent needs that a workflow with conditional branches cannot provide."*

---

## Tool Interface Design (ACI Design)

**Use when:** You are designing the tool definitions that an agent will use — the descriptions, parameter schemas, examples, error responses, and documentation that the LLM reads when deciding how to use a tool. Tool quality is one of the three most important factors in agent performance, alongside system prompt design and evaluation. Tool definitions are not API documentation for developers — they are behavioral instructions for an LLM.

```xml
<reasoning>
Design the tool interface as follows:
1. Define each tool's purpose in a single sentence. If the purpose cannot be stated in one sentence, the tool may be doing too much — consider splitting it. If two tools have purposes that a human engineer could not reliably distinguish, the LLM will confuse them — either merge them, differentiate their descriptions more sharply, or add explicit routing guidance in the system prompt.
2. Design the parameter schema with the LLM as the primary consumer. Parameter names should be self-documenting (use 'customer_email' not 'email', 'search_query' not 'q'). Enum values should use natural language, not codes ('high_priority' not '1'). Required vs. optional parameters should reflect actual usage patterns, not the underlying API's full capability surface. Minimize the parameter count — every parameter is a decision the LLM must make correctly.
3. Write the tool description as if explaining to a competent colleague who has never used this tool. Include: what it does, when to use it (and when not to), what a successful result looks like, and what common errors mean. Use namespace prefixes when tools group logically (e.g., 'calendar_list_events', 'calendar_create_event') so the LLM can infer tool relationships from naming alone.
4. Design error responses that the LLM can act on. "Error 500" tells the LLM nothing. "The user's calendar is not connected — ask the user to connect their calendar before retrying" tells it exactly what to do. Every error response should include: what went wrong, whether retrying would help, and what the agent should do instead.
5. Design tool responses for token efficiency. Return only the fields the agent needs for its next decision, not the full API response. If a tool returns paginated results, include the total count and clear pagination instructions. If a tool returns large data, provide a summary with the option to retrieve details — do not dump the full payload into the context window.
6. Add usage examples for tools with complex parameter interactions. Show the tool call and the expected result for 2-3 representative scenarios, including at least one error scenario. Assess the total tool surface: can the LLM reliably distinguish between all available tools? If the tool count exceeds 10-15, consider whether some tools should be dynamically loaded based on context rather than always present.
</reasoning>
```

**Watch for:** Claude writes tool descriptions optimized for human developers rather than LLM consumption. Tool descriptions for agents need to be instruction-like, not documentation-like. If descriptions read like API reference docs, add: *"Write tool descriptions as instructions to the agent, not documentation for developers. Replace 'This endpoint returns...' with 'Use this tool when you need to...'"*

Claude also designs tools with bloated response schemas. Every token in a tool response consumes attention budget. If tool responses include large data structures, add: *"For each tool response field, justify why the agent needs it for its next decision. Remove any field the agent does not act on."*

---

## Context Window Architecture

**Use when:** You are designing how information is organized, prioritized, and managed within an agent's context window across multiple turns. This treats the context window as the scarce resource it is and designs for the mechanical reality that LLM attention degrades as context grows.

```xml
<reasoning>
Design the context architecture as follows:
1. Map the information types the agent needs: system instructions, task-specific context, user history, retrieved knowledge, tool results, conversation history, and any domain-specific state. For each type, estimate the token footprint under normal and peak conditions.
2. Classify each information type by persistence: always present (system prompt, core tool definitions), session-scoped (user preferences, current task, active goals), turn-scoped (tool results, retrieved documents, intermediate calculations), or ephemeral (superseded state, consumed intermediate results). Persistence class determines management strategy.
3. Design the context layout following primacy-recency principles: persistent instructions at the top of the context (highest attention weight at the start), dynamic state in the middle, most recent conversation and task state at the bottom near the generation point (highest attention weight at the end). Information in the middle of a long context receives the least attention — place the least critical dynamic content there.
4. Design the retrieval strategy. Pre-load information that is small, frequently needed, and stable (identity, constraints, core tool definitions). Use just-in-time retrieval via tools for information that is large, infrequently needed, or changes often (documents, database records, historical data). For the boundary cases, choose based on the cost of a wrong retrieval decision vs. the cost of persistent context consumption. Consider a hybrid approach: maintain lightweight references (file paths, query templates, record IDs) in persistent context, and retrieve full content on demand.
5. Design the overflow plan for when the context approaches the window limit. Specify the compaction strategy: what gets summarized (conversation history is typically first — preserve decisions, open issues, and key facts; discard verbose back-and-forth), what gets evicted (tool results from completed subtasks, retrieved documents that have been synthesized), and what must never be pruned (system instructions, active constraints, current task state). If the agent runs long-horizon tasks, design a structured note-taking mechanism where the agent writes key state to an external store and reads it back after compaction.
6. Estimate the total token budget under peak conditions and verify it fits within the target model's context window with at least 20% headroom for the agent's own generation. If it does not fit, identify which zone to shrink and what capability is sacrificed.
</reasoning>
```

**Watch for:** Claude designs context architectures with no mechanism for actually implementing the token management. If the design describes what should happen but not how (what code manages compaction, what prompt drives summarization, what trigger fires retrieval), add: *"For each context management decision, specify the implementation mechanism — not just the policy but how it is enforced."*

Claude also underestimates the token cost of tool definitions. In systems with many tools, tool definitions themselves consume significant context before any conversation begins. If the design does not account for tool definition tokens, add: *"Include tool definitions in your token budget. Each tool definition typically consumes 200-500 tokens. A system with 15 tools may use 3,000-7,500 tokens on tool definitions alone."*

---

## Failure Mode & Recovery Design

**Use when:** You need to anticipate how an agent will fail and design recovery mechanisms into the system prompt and tool definitions. Agent systems fail constantly and in ways less visible than traditional software failures — the agent does not crash, it simply makes a wrong decision and continues confidently.

```xml
<reasoning>
Design the failure architecture as follows:
1. Enumerate the failure categories for this agent: tool failures (API errors, timeouts, unexpected responses, rate limits), context failures (missing information, stale data, context overflow, conflicting information from different sources), reasoning failures (wrong tool selection, incorrect interpretation of results, hallucinated actions, over-commitment to a failing approach), and boundary failures (attempting actions outside scope, failing to escalate when required, providing answers outside its knowledge, making commitments it cannot fulfill).
2. For each failure category, identify the 2-3 most likely specific failure modes given this agent's task domain and tool landscape. Prioritize by frequency × impact — a failure that happens often with moderate impact matters more than a catastrophic failure that is extremely rare.
3. For each failure mode, design the recovery instruction that will appear in the system prompt: What should the agent do when this happens? Options include: retry with modified parameters (appropriate for transient tool errors), escalate to a human (appropriate for ambiguous situations with high stakes), ask the user for clarification (appropriate for ambiguous inputs), fall back to a simpler approach (appropriate when a complex strategy is failing), acknowledge uncertainty and state what it does know (appropriate when information is incomplete), or halt and explain (appropriate for boundary violations). Not all failures are retry-able — design at least three distinct recovery strategies across your failure modes.
4. Design detection mechanisms: How does the agent know it has failed? Explicit error responses from tools are easy to detect. Silent failures — wrong answers that look plausible, gradual context corruption from accumulated stale data, hallucinated actions that happen to succeed — are hard. For high-stakes decisions, design verification steps: have the agent check its work, cross-reference with a second source, or confirm with the user before acting.
5. Design the escalation ladder: What failures does the agent handle autonomously (transient errors, minor ambiguity)? What failures require user confirmation before proceeding (irreversible actions, high-cost decisions)? What failures require human takeover (safety-critical situations, repeated failures on the same task, situations outside the agent's defined scope)? These boundaries must be explicit in the system prompt — do not leave escalation decisions to the agent's judgment.
</reasoning>
```

**Watch for:** Claude designs recovery mechanisms that are overly optimistic — "retry the tool call" as the universal solution. Some failures cannot be retried (irreversible actions already taken), some should not be retried (the fundamental approach is wrong), and some require different strategies entirely (ambiguous user input). If recovery instructions cluster around retry logic, add: *"Design at least three distinct recovery strategies across your failure modes. For each, explain why retrying would not work and what the agent should do instead."*

Claude also designs only for failures it can name in advance. The most dangerous agent failures are unanticipated. Always include a catch-all instruction: what should the agent do when something unexpected happens that matches no defined failure mode? The default should be conservative — acknowledge the situation, state what it knows, and ask for guidance rather than improvising.

---

## Multi-Agent Coordination

**Use when:** The system involves multiple agents that need to share information, divide work, or hand off tasks. This is the most complex reasoning approach and should be used only after Agent vs. Workflow Decomposition has established that multi-agent architecture is genuinely necessary. Most systems that appear to need multiple persistent agents can be better served by a single orchestrator that spawns temporary sub-agents for parallel work.

```xml
<reasoning>
Design the coordination architecture as follows:
1. Define each agent's responsibility boundary: what tasks does it own, what information does it produce, and what decisions is it authorized to make? Boundaries should be non-overlapping — if two agents could plausibly handle the same input, the routing will be unreliable. Each agent should have a clear, one-sentence mission that an engineer could use to determine whether any given task belongs to that agent.
2. Design the coordination protocol: How do agents communicate? Through a shared context managed by an orchestrator? Through explicit message-passing with defined schemas? Through a shared state store that agents read from and write to? The simpler the protocol, the more reliable the system. An orchestrator pattern (one lead agent delegates to specialist sub-agents and synthesizes results) is almost always more reliable than peer-to-peer communication between autonomous agents.
3. Design the information contract between agents: When Agent A hands off to Agent B, what information must be included? In what format? At what fidelity? The handoff specification is the API contract of multi-agent systems. Specify it with the same rigor you would apply to an API schema — vague handoffs produce vague results. Include: task description, relevant context, constraints, expected output format, and what to do if the sub-task cannot be completed.
4. Identify the coordination failure modes: What happens when agents produce conflicting results? When one agent blocks on another? When the orchestrator routes incorrectly? When a sub-agent exceeds its token budget or time limit and returns a partial result? Design resolution mechanisms for each — the orchestrator must have explicit instructions for handling coordination breakdowns.
5. Assess whether the multi-agent architecture is still justified. If the coordination overhead (handoff latency, context duplication across agents, failure modes from routing and synthesis) exceeds the benefit of specialization, a single more capable agent with better tools may outperform the multi-agent system. A single orchestrator that spawns temporary sub-agents for parallel retrieval or analysis — then synthesizes their results — is almost always simpler and more reliable than persistent separate agents with peer-to-peer communication. Justify why this system requires the proposed architecture rather than a simpler alternative.
</reasoning>
```

**Watch for:** Claude designs sophisticated multi-agent systems because they are architecturally interesting. This is the strongest form of complexity bias in agent design. If the multi-agent design could be replaced by a single agent with sub-agent spawning for parallelization, that is almost always the better design. Add: *"Justify why this requires persistent separate agents rather than a single orchestrator that spawns temporary sub-agents for parallel work. The coordination overhead of persistent multi-agent systems — context duplication, routing failures, conflicting outputs, handoff latency — is substantial."*
