---
name: agent-architecture-audit
description: Audit the architecture and health of any AI agent system. Use when diagnosing why a wrapped agent behaves worse than the base model, investigating agent hallucinations, tool-use failures, memory contamination, or hidden prompt conflicts. Produces a structured JSON report with severity-ranked findings and a code-first fix plan.
license: Apache-2.0
---

# Agent Architecture Audit

Audit the architecture and health of any AI agent system.

**The base model rarely fails. The wrapper architecture corrupts good answers into bad behavior.**

When an AI agent (coding assistant, autonomous agent, chatbot with tools, or wrapped LLM) produces broken, hallucinated, or degraded output, the failure is almost never the model itself. It is the orchestration — the system prompt, memory layer, tool routing, hidden repair loops, and rendering pipeline — that corrupts good answers.

## When to Use This Skill

Use this skill when:

- A wrapped agent behaves worse than the base model via direct API
- The agent hallucinates, skips required tools, or reuses stale context
- "Must use tool X" is in the prompt but the model answers without calling it
- Old topics leak into new conversations across sessions
- Internal logs show correct answers but users see broken output
- Hidden retry/fallback agents silently mutate responses
- Cost spikes with no visible output (runaway loops)

## The 12-Layer Stack

Every agent system has these layers. Any of them can corrupt the answer:

| # | Layer | What Goes Wrong |
|---|-------|----------------|
| 1 | System prompt | Conflicting instructions, instruction bloat |
| 2 | Session history | Stale context from previous turns |
| 3 | Long-term memory | Pollution across sessions |
| 4 | Distillation | Compressed artifacts re-entering as pseudo-facts |
| 5 | Active recall | Redundant re-summary layers wasting context |
| 6 | Tool selection | Wrong tool routing, model skips required tools |
| 7 | Tool execution | Hallucinated execution — claims to call but doesn't |
| 8 | Tool interpretation | Misread or ignored tool output |
| 9 | Answer shaping | Format corruption in final response |
| 10 | Platform rendering | UI/API/CLI mutates valid answers |
| 11 | Hidden repair loops | Silent fallback/retry agents running second LLM pass |
| 12 | Persistence | Expired state or cached artifacts reused as live evidence |

## Audit Process

### Phase 1: Intake — What Does the User Report?

Capture symptoms in `agent_check_scope.json`:

```json
{
  "target_name": "agent or system being audited",
  "user_symptoms": ["what the user reports is wrong"],
  "symptom_severity": "critical|high|medium|low",
  "audit_scope": "what part of the stack to focus on"
}
```

### Phase 2: Evidence Collection

Gather whatever evidence is available from the system:

- **System prompts** — all layers of instructions, from base to wrapper to fallback
- **Tool definitions** — how tools are declared (prompt text vs code-enforced)
- **Memory configuration** — what gets persisted, how it's retrieved, freshness rules
- **Agent loop code** — the orchestration loop, tool routing, error handling, retry logic
- **Output pipeline** — how answers are shaped, formatted, or transformed before delivery

Collect into `evidence_pack.json`.

### Phase 3: Code-Level Anti-Pattern Scan

Run these grep-searchable patterns against any agent codebase or prompt collection:

```bash
# 1. Hardcoded secrets
rg "sk-[A-Za-z0-9]{20,}|ghp_[A-Za-z0-9]{36}|AKIA[0-9A-Z]{16}" --type md --type json --type yaml

# 2. Tool requirements in prompt only (no code gate)
rg "must.*tool|required.*call|always.*use.*tool" --type md --type txt

# 3. Hidden LLM calls outside main agent loop
rg "completion|chat\.create|messages\.create|llm\.invoke" --type py --type ts

# 4. Unrestricted code execution
rg "exec\(|eval\(|subprocess\.(run|Popen)|os\.system\(" --type py -n

# 5. Memory admission without user priority
rg "memory.*admit|long.*term.*update|persist.*memory" --type py --type ts

# 6. Missing error handling on agent paths
rg "while.*agent|for.*turn|agent.*loop" --type py --type ts -A 3 | rg -v "max_|limit|break"

# 7. Output mutation in delivery layer
rg "mutate.*response|rewrite.*output|transform.*answer" --type py --type ts

# 8. Unbounded memory/context growth
rg "add.*memory|upsert.*vector|append.*context" --type py --type ts -A 3 | rg -v "max_|limit|ttl|trim"

# 9. Missing observability (absence check)
rg "langsmith|langfuse|opentelemetry|callback|tracer" --type py --type ts

# 10. State mutators without upstream validation
rg "file.*write|db.*insert|vector.*upsert" --type py --type ts -B 5 | rg -v "validate|guard|filter"
```

### Phase 4: Failure Mapping

For each failure found, document in `failure_map.json`:

```json
{
  "failures": [
    {
      "id": 1,
      "severity": "critical|high|medium|low",
      "layer": "which of the 12 layers",
      "title": "what went wrong",
      "mechanism": "how it happens",
      "evidence": ["file:line or prompt excerpt"]
    }
  ]
}
```

### Phase 5: Report Generation

Produce `agent_check_report.json`:

```json
{
  "schema_version": "oh-my-agent-check.report.v1",
  "target_name": "agent name",
  "overall_health": "critical_risk|high_risk|medium_risk|low_risk",
  "findings": [
    {
      "severity": "critical|high|medium|low",
      "title": "short description",
      "layer": "which stack layer",
      "mechanism": "how it corrupts the answer",
      "evidence_refs": ["file:line or prompt"],
      "recommended_fix": "what to change",
      "fix_type": "code_enforced|prompt_only|architectural"
    }
  ],
  "ordered_fix_plan": [
    { "order": 1, "goal": "first thing to fix", "why_now": "why this comes first" }
  ]
}
```

## Audit Playbooks

Choose the closest playbook based on symptoms:

### wrapper-regression
When the base model works fine but the wrapped agent is worse.
Focus: system prompt conflicts, duplicated context, hidden formatting layers.

### memory-contamination
When old topics bleed into new conversations.
Focus: same-session artifact reentry, stale session reuse, weak memory admission.

### tool-discipline
When the agent skips required tools or hallucinates execution.
Focus: code-enforced vs prompt-enforced tool requirements, skip paths.

### rendering-transport
When internal answer is correct but delivery is broken.
Focus: transport payload assumptions, platform-layer mutations.

### hidden-agent-layers
When silent repair/retry/summarize loops run without contracts.
Focus: hidden repair agents, second-pass LLM calls, maintenance-worker synthesis.

### code-execution-safety
When the agent uses exec/eval/shell without sandboxing.
Focus: resource limits, input validation, isolation.

### memory-growth-hazard
When memory/context grows without limits.
Focus: size limits, TTL, retention policies.

### observability-gap
When there is no tracing or debugging capability.
Focus: add logging, cost metrics, session replay.

### state-mutator-safety
When the agent writes to files/DBs without validation.
Focus: upstream validation, guard nodes, rollback.

## Severity Model

| Level | Meaning |
|-------|---------|
| `critical` | Agent can confidently produce wrong operational behavior |
| `high` | Agent frequently degrades correctness or stability |
| `medium` | Correctness usually survives but output is fragile or wasteful |
| `low` | Mostly cosmetic or maintainability issues |

## Fix Strategy

Default fix order (code-first, not prompt-first):

1. **Code-gate tool requirements** — enforce in code, not just prompt text
2. **Remove or narrow hidden repair agents** — make fallback explicit with contracts
3. **Reduce context duplication** — same info through prompt + history + memory + distillation
4. **Tighten memory admission** — user corrections > agent assertions
5. **Tighten distillation triggers** — don't compress what shouldn't be compressed
6. **Reduce rendering mutation** — pass-through, don't transform
7. **Convert to typed JSON envelopes** — structured internal flow, not freeform prose

## Anti-Patterns to Avoid

- ❌ Saying "the model is weak" without falsifying the wrapper first
- ❌ Saying "memory is bad" without showing the contamination path
- ❌ Letting a clean current state erase a dirty historical incident
- ❌ Treating markdown prose as a trustworthy internal protocol
- ❌ Accepting "must use tool" in prompt text when code never enforces it
