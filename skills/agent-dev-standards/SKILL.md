---
name: agent-dev-standards
description: "Agent development quality standards and engineering guardrails. Use when Codex is: (1) Developing or modifying an Agent (code-reviewer, rag-bot, coding-agent, etc.), (2) Designing agent prompts, tool schemas, or function calling logic, (3) Setting up agent evaluation, tracing, or CI pipelines, (4) Reviewing agent code quality or enforcing development standards, (5) Defining agent registry entries, versioning, or deployment configurations. Not for: general AI Coding tool usage (Claude Code/Codex/Cursor), pure RAG pipeline without agent logic, or non-agent LLM applications."
---

# Agent Development Standards

Enforceable engineering standards for building production-grade Agents. This skill embeds knowledge from the LLM application optimization and Agent engineering series into actionable rules.

## Core Principles

Every Agent must pass a 6-pillar gate before considered production-ready:

| Pillar | Principle | Fail if |
|--------|-----------|---------|
| Prompt Management | Every prompt is a versioned file, not inline code | No front-matter or version |
| Agent Registry | Every agent has a registry entry | No registry or stale dependency |
| Tool Calling | Every tool has a typed schema + error recovery | Tools without error handling |
| Evaluation | Every agent has a golden test suite | No evaluation before release |
| Observability | Every agent emits spans and cost tags | No tracing or cost attribution |
| Safety | Every agent has injection protection | No input validation or permission model |

## Workflow: Agent Development Lifecycle

### Phase 1: Design

1. **Define intent**: What business problem does this agent solve? Single-responsibility per agent.
2. **Registry entry**: Create agent entry with metadata (name, version, dependencies, prompt refs).
3. **Prompt design**: Write system prompt as a .md file with front-matter (see references/prompt-management.md).
4. **Tool schema**: Define tool schemas with typed parameters and error recovery paths (see references/tool-calling.md).

### Phase 2: Implement

5. **Prompt to code binding**: Use a loader that reads prompts from files, not f-strings.
6. **Tool implementation**: Each tool must handle: success, partial success, retryable failure, terminal failure.
7. **Tracing integration**: Agent must emit spans for each LLM call and tool call (see references/agent-observability.md).
8. **Cost tagging**: Every LLM call tagged with agent_name, prompt_version, tool_name.

### Phase 3: Validate

9. **Golden test suite**: Minimum 10 golden cases covering happy path, edge cases, and failure modes (see references/evaluation.md).
10. **CI gate**: Golden tests run on every prompt/tool change. Block if score drops below threshold.
11. **Safety scan**: Check for prompt injection surfaces, tool permission leaks, data exposure (see references/safety.md).

### Phase 4: Release

12. **Registry update**: Bump version, update dependency graph.
13. **Changelog**: Record what changed (prompt, tool, threshold) and why.
14. **Cost baseline**: Record baseline cost per invocation before release.

## Gate Checklist (Must-Pass)

Before any agent code enters production, verify:

- [ ] Prompt file exists with front-matter (version, description, author)
- [ ] Prompt version is referenced in registry entry
- [ ] All tool schemas have description and typed parameters
- [ ] All tools have error handling (retry, fallback, or abort)
- [ ] Agent registry entry exists and dependencies are up-to-date
- [ ] Golden test suite exists and passes with score >= 80%
- [ ] Tracing spans are emitted for every LLM and tool call
- [ ] Cost tags are attached to every LLM call
- [ ] Input validation exists (no raw user input in system prompt)
- [ ] Tool permissions are least-privilege 
- [ ] Degradation detection metrics are configured and baseline recorded

## Phase 5: Monitor

15. **Degradation detection**: Monitor cache hit rate, error rate, cost per call over time. Alert if any metric drops 20% below baseline (see references/agent-observability.md).
16. **Incident response**: When degradation detected, freeze prompt version, roll back to last known good version, and trigger golden test suite. See references/incident-response.md.

## Reference Files

Load these when deeper guidance is needed:

- references/prompt-management.md -- Front-matter schema, versioning strategy, caching optimization
- references/agent-registry.md -- Registry schema, dependency tracking, impact analysis
- references/tool-calling.md -- Tool schema design, error recovery patterns, orchestration
- references/evaluation.md -- Evaluation dimensions, golden test structure, CI integration
- references/safety.md -- Injection prevention, permission model, data isolation
- references/agent-observability.md -- Span design, trace model, cost attribution, degradation detection
- references/incident-response.md -- Freeze, rollback, and golden test trigger during production incidents 

## Validation Script

```
python scripts/validate_agent_standards.py <agent-project-dir>
```

Checks: prompt files exist with front-matter, registry entry exists, tool schemas have error handling, golden tests exist, tracing calls present.
