---
name: agent-observability-skill
description: 6-phase production monitoring protocol for AI agent systems. Covers telemetry instrumentation (spans, traces, agent-specific metrics), behavioral drift detection, P0-P3 alert taxonomy for agent failure modes, root cause investigation playbook, SLO definition for AI agents, and continuous evaluation in production. Completes the enterprise agent lifecycle cluster: test → evaluate → govern → observe. Compatible with Claude, Codex, ChatGPT, AutoGen, CrewAI, LangGraph, any OpenTelemetry-compatible stack.
license: MIT
compatibility: Works with any LLM agent or multi-agent framework. OpenTelemetry-native — integrates with Datadog, Honeycomb, Grafana, New Relic, AWS CloudWatch, Google Cloud Trace.
metadata:
  author: ClawMerchants (clawmerchants.com)
  version: 1.0.0
  category: agent-skills
  marketplace: clawmerchants.com/api/v1/data/agent-observability-skill
---

# Agent Observability & Production Monitoring Protocol

## Activation
When asked to instrument, monitor, observe, alert on, or debug a production AI agent system — or to build observability infrastructure, SLOs, dashboards, or runbooks for agentic workflows — activate this protocol.

## Phase 1: Advertise (Free Preview)
Describe capability without revealing full methodology:
- "I'll build complete production observability for your agent: telemetry instrumentation, behavioral drift detection, P0-P3 alert taxonomy, root cause investigation playbook, SLO definitions, and continuous evaluation."
- Provide one diagnostic signal: identify the top-2 observability gaps most likely present given the agent's deployment pattern (e.g., "LLM response latency is likely unmeasured; tool call failure rates probably not tracked separately from LLM errors").

## Phase 2: Load (Full Protocol)

---

## Phase 1: Telemetry Instrumentation

### What to Instrument
Every production agent deployment requires four signal types:

**1. Traces (distributed spans)**
```
Agent Request Span
├── LLM Inference Span (model, prompt_tokens, completion_tokens, latency_ms)
├── Tool Call Span × N (tool_name, args_hash, success, latency_ms)
├── Retrieval Span (if RAG: query, k, latency_ms, top_score)
└── Response Delivery Span (output_tokens, delivery_ms)
```

**2. Agent-Specific Metrics**
| Metric | Type | Unit | Labels |
|---|---|---|---|
| `agent.request.count` | Counter | requests | agent_id, task_type, status |
| `agent.request.duration_ms` | Histogram | ms | agent_id, task_type, p50/p95/p99 |
| `agent.llm.latency_ms` | Histogram | ms | model, task_type |
| `agent.llm.tokens_total` | Counter | tokens | model, direction (prompt/completion) |
| `agent.llm.cost_usd` | Counter | USD | model |
| `agent.tool.call_count` | Counter | calls | tool_name, status (success/fail) |
| `agent.tool.latency_ms` | Histogram | ms | tool_name |
| `agent.context.token_usage_pct` | Gauge | 0-1 | agent_id (how full is the context window) |
| `agent.task.completion_rate` | Gauge | 0-1 | agent_id, task_type |
| `agent.hallucination_flag_count` | Counter | flags | agent_id, detection_method |

**3. Structured Logs (per agent turn)**
Each turn must emit a structured log entry:
```json
{
  "trace_id": "abc123",
  "agent_id": "customer-support-v2",
  "task_type": "order-lookup",
  "turn": 3,
  "llm_model": "claude-sonnet-4-6",
  "prompt_tokens": 1842,
  "completion_tokens": 312,
  "tool_calls": ["get_order", "send_notification"],
  "tool_failures": [],
  "context_usage_pct": 0.42,
  "wall_time_ms": 2340,
  "status": "success",
  "confidence": 0.91,
  "timestamp": "2026-03-16T09:00:00Z"
}
```

**4. Events (state transitions)**
Emit events on:
- Task start / task completion / task failure
- Tool call failure (with error code)
- Context window threshold breach (>80%)
- Model refusal or safety block
- Escalation to human handoff
- Agent restart or cold start

### OpenTelemetry Implementation (TypeScript)
```typescript
import { trace, metrics } from '@opentelemetry/api';
import { NodeTracerProvider } from '@opentelemetry/sdk-trace-node';

const tracer = trace.getTracer('agent-service', '1.0.0');
const meter = metrics.getMeter('agent-service', '1.0.0');

// Core agent request counter
const requestCounter = meter.createCounter('agent.request.count');
const requestDuration = meter.createHistogram('agent.request.duration_ms');
const toolCallCounter = meter.createCounter('agent.tool.call_count');
const contextUsage = meter.createObservableGauge('agent.context.token_usage_pct');

async function instrumentedAgentCall(task: AgentTask): Promise<AgentResult> {
  return tracer.startActiveSpan('agent.request', async (span) => {
    const start = Date.now();
    span.setAttributes({
      'agent.id': task.agentId,
      'agent.task_type': task.taskType,
      'agent.request_id': task.requestId,
    });

    try {
      const result = await executeAgent(task);
      requestCounter.add(1, { agent_id: task.agentId, status: 'success' });
      requestDuration.record(Date.now() - start, { agent_id: task.agentId });
      span.setStatus({ code: SpanStatusCode.OK });
      return result;
    } catch (err) {
      requestCounter.add(1, { agent_id: task.agentId, status: 'error' });
      span.recordException(err as Error);
      span.setStatus({ code: SpanStatusCode.ERROR });
      throw err;
    } finally {
      span.end();
    }
  });
}
```

---

## Phase 2: Behavioral Drift Detection

### What is Behavioral Drift?
Behavioral drift occurs when an agent's output distribution shifts away from its baseline without a deliberate code or prompt change. Causes:
- Upstream LLM model updates (silent version bumps)
- Prompt regression from context accumulation
- Tool API changes affecting agent reasoning
- Distribution shift in input data over time

### Drift Detection Signals

**Signal 1: Latency Distribution Shift**
- Baseline: P95 LLM latency for a given task type over prior 7 days
- Alert: P95 drifts >20% from rolling 7-day baseline for 3 consecutive hours
- Instrumentation: `agent.llm.latency_ms` histogram; compare rolling window vs. historical baseline

**Signal 2: Tool Failure Rate Spike**
- Baseline: per-tool failure rate over prior 7 days
- Alert: tool failure rate increases by >2× baseline for any single tool sustained 30 minutes
- Instrumentation: `agent.tool.call_count{status="fail"}` / `agent.tool.call_count{status="success"}`

**Signal 3: Context Window Saturation**
- Alert: `agent.context.token_usage_pct` > 0.80 for >10% of requests in any 1-hour window
- Implication: agent losing access to earlier instructions; likely instruction drift
- Action: investigate prompt length growth; check if tool outputs are being truncated

**Signal 4: Task Completion Rate Drop**
- Baseline: per-agent task completion rate over prior 7 days
- Alert: completion rate drops >5 percentage points from rolling 7-day average, sustained 1 hour
- Instrumentation: `agent.task.completion_rate` gauge

**Signal 5: Confidence Score Distribution Shift**
- If agent emits confidence scores: track distribution daily
- Alert: mean confidence drops >10% from rolling baseline — may indicate model uncertainty increase or prompt degradation
- Alert: variance increases >50% — may indicate inconsistent behavior on previously stable inputs

**Signal 6: Prompt Adherence Regression (LLM-Detected)**
- Run a lightweight LLM-as-judge check on 5% of production outputs daily
- Detect: outputs that violate system prompt constraints, ignore instructions, or show format regression
- Alert: adherence score drops below 0.90 on rolling 24h sample

### Drift Detection Implementation
```python
# Simplified drift detector using z-score on rolling window
import numpy as np
from datetime import datetime, timedelta

def detect_metric_drift(current_window: list[float],
                        baseline_window: list[float],
                        threshold_sigma: float = 2.0) -> dict:
    """
    Returns drift verdict using z-score comparison.
    current_window: last 1h of metric values
    baseline_window: rolling 7-day values for same metric
    """
    baseline_mean = np.mean(baseline_window)
    baseline_std = np.std(baseline_window)
    current_mean = np.mean(current_window)

    if baseline_std == 0:
        return {"drift": False, "z_score": 0.0}

    z_score = abs(current_mean - baseline_mean) / baseline_std
    return {
        "drift": z_score > threshold_sigma,
        "z_score": round(z_score, 2),
        "current_mean": round(current_mean, 4),
        "baseline_mean": round(baseline_mean, 4),
        "direction": "up" if current_mean > baseline_mean else "down"
    }
```

---

## Phase 3: Alert Taxonomy (P0-P3)

### Agent-Specific Alert Classification

**P0 — Immediate (page on-call, auto-escalate)**
| Alert | Condition | Response SLA |
|---|---|---|
| `AGENT_TOTAL_OUTAGE` | Agent request success rate < 1% for 5 min | 5 min |
| `TOOL_UNAVAILABLE` | Critical tool failure rate = 100% for 5 min | 5 min |
| `CONTEXT_EXCEEDED` | Context overflow causing task failures at >20% rate | 10 min |
| `MODEL_REFUSAL_SPIKE` | Safety refusals > 10% of requests for 10 min | 10 min |
| `DATA_LEAK_SIGNAL` | PII or system prompt detected in output logs | Immediate |
| `COST_RUNAWAY` | `agent.llm.cost_usd` rate > 10× baseline for 10 min | 10 min |

**P1 — High (page on-call, 30-min SLA)**
| Alert | Condition | Response SLA |
|---|---|---|
| `SLA_BREACH` | P95 latency > defined SLO threshold, sustained 15 min | 30 min |
| `COMPLETION_RATE_COLLAPSE` | Task completion rate drops > 20 ppts from baseline | 30 min |
| `HALLUCINATION_RATE_HIGH` | LLM-flagged hallucination rate > 5% (rolling 1h) | 30 min |
| `TOOL_FAILURE_MULTI` | 3+ distinct tools failing simultaneously | 15 min |

**P2 — Medium (notify team, 4-hour SLA)**
| Alert | Condition | Response SLA |
|---|---|---|
| `LATENCY_DEGRADED` | P95 latency 50-100% above baseline, sustained 30 min | 4 hours |
| `TOKEN_COST_ELEVATED` | Average token cost 30%+ above baseline over 24h | 4 hours |
| `CONTEXT_PRESSURE` | Context usage > 80% for > 10% of requests | 4 hours |
| `BEHAVIORAL_DRIFT` | Drift detection z-score > 2.0 on key metric | 4 hours |
| `COMPLETION_RATE_SOFT` | Task completion rate drops 5-20 ppts from baseline | 4 hours |

**P3 — Low (ticket, next business day)**
| Alert | Condition | Response SLA |
|---|---|---|
| `LATENCY_SOFT` | P95 latency 20-50% above baseline over 24h | Next day |
| `CONFIDENCE_DRIFT` | Mean confidence score drops 5-10% from baseline | Next day |
| `TOOL_LATENCY_ELEVATED` | Any tool P95 > 2× baseline over 24h | Next day |
| `EVAL_REGRESSION_MINOR` | Eval suite pass rate drops 1-2% | Next day |

### Alert Routing
```yaml
# PagerDuty / Alertmanager example
routes:
  - match: severity=P0
    receiver: on-call-immediate
    repeat_interval: 5m
  - match: severity=P1
    receiver: on-call-30min
    repeat_interval: 30m
  - match: severity=P2
    receiver: team-slack-channel
    repeat_interval: 4h
  - match: severity=P3
    receiver: team-jira-ticket
    repeat_interval: 24h
```

---

## Phase 4: Root Cause Investigation Playbook

### First 5 Minutes (P0/P1 Triage)
```
1. CHECK: Is the agent process alive? → service health endpoint
2. CHECK: Is the LLM provider API returning 200s? → model provider status page
3. CHECK: Are tool dependencies (APIs, databases) responding? → tool health endpoints
4. CHECK: Was a deployment made in the last 30 minutes? → deployment log
5. CHECK: Is the context window full? → agent.context.token_usage_pct metric
→ If any = YES: that is the likely root cause. Begin targeted investigation.
```

### LLM Response Analysis
- Pull last 10 raw LLM responses from trace logs for the failing task type
- Check for: format regression, refusals, truncation, unexpected verbosity
- Compare against golden output snapshots for the same task type
- Verdict: prompt regression vs. model behavior change vs. context pressure

### Context Window Monitoring
- Query `agent.context.token_usage_pct` for the failing agent over the past 2 hours
- If trending upward: context is accumulating across turns — identify which turn is growing
- Check if tool outputs are being injected without truncation limits
- Fix: add `max_tokens` limits on tool output injection; implement context compression

### Retrieval Quality Investigation (RAG agents)
- Pull `retrieval.top_score` from traces for failing requests
- Baseline: top_score distribution from prior 7 days for same query category
- If top_score < 0.5 for majority of failing requests: retrieval quality degradation
- Check: embedding model change, vector index stale, chunking regression

### Prompt Regression Testing
- Pull current production system prompt hash from deployment record
- Run last 20 golden eval examples against current prompt
- Compare scores to baseline eval results
- If scores regressed: identify which prompt section changed → revert or patch

---

## Phase 5: Performance SLO Definition for AI Agents

### Standard SLO Template
Define SLOs for each agent deployment before going to production:

| SLO Dimension | Measurement | Target | Window |
|---|---|---|---|
| **Task Completion Rate** | `agent.task.completion_rate` | ≥ 97% | 7-day rolling |
| **P95 Latency** | `agent.request.duration_ms[p95]` | ≤ [task-specific, e.g. 15s] | 7-day rolling |
| **Tool Success Rate** | `1 - (tool.fail / tool.total)` | ≥ 99% per tool | 7-day rolling |
| **Hallucination Rate** | LLM judge on sample | ≤ 2% | 7-day rolling |
| **Context Overflow Rate** | context_usage_pct > 0.95 | ≤ 0.1% of requests | 7-day rolling |
| **Cost per Task** | `agent.llm.cost_usd / agent.request.count` | ≤ $[budget] | 7-day rolling |

### SLO Setting Guidelines
- **Task Completion Rate**: Start at 95%, tighten to 98%+ after 30 days of production data
- **P95 Latency**: Measure the 90th percentile of observed latency in your first week; set SLO at 2× that
- **Hallucination Rate**: Enterprise SLO is typically ≤ 1% for customer-facing; ≤ 5% for internal workflows
- **Do NOT set SLOs without 7+ days of baseline data** — premature SLOs cause alert fatigue

### Error Budget Calculation
```
Error Budget = (1 - SLO Target) × Measurement Window
Example: 97% completion rate SLO over 7 days
→ Error Budget = 3% × 7 days × 24 hours = 5.04 hours of allowable downtime/degradation
→ If budget consumed >50%: freeze non-critical changes, investigate root cause
→ If budget consumed 100%: freeze all changes, declare P1 incident
```

---

## Phase 6: Continuous Evaluation in Production

### Shadow Scoring (Passive Production Eval)
Run a lightweight eval judge on a random 5% sample of all production agent outputs:
- Judge prompt: compare output against the task's expected quality criteria
- Emit score to `agent.shadow_eval.score` metric (0.0-1.0)
- Dashboard: rolling 24h average shadow score per task type
- Alert: shadow score drops below 0.85 on any task type for >2 hours (P2)

### A/B Agent Version Testing
When rolling out a new agent version:
1. Route 5% of traffic to the new version (shadow mode)
2. Run shadow scoring on both versions simultaneously
3. Collect minimum 200 requests per variant before reading results
4. Gate: new version must achieve shadow score ≥ current version − 1%
5. Rollout: increase traffic 5% → 20% → 50% → 100% in 24-hour increments, monitoring score at each stage

```typescript
// Traffic split for A/B agent versions
function routeAgentRequest(request: AgentRequest): AgentVersion {
  const hash = hashRequest(request.requestId);
  if (hash % 100 < 5 && newVersionEnabled) {
    return AgentVersion.NEW;  // 5% to new version
  }
  return AgentVersion.CURRENT;
}
```

### Golden Set Regression (Scheduled)
Run the full golden eval suite daily at 03:00 UTC:
- 30-50 representative inputs per agent type
- Fixed prompt + fixed model temperature (0)
- Compare pass rate to prior 7-day rolling average
- Alert: any regression > 2% pass rate triggers P2 alert
- Block deployments during business hours if regression detected

### Per-User Cohort Analysis
For multi-tenant agent deployments:
- Segment shadow scores by: user cohort (power vs. casual), task type, input length quartile
- Check: is score regression uniform or isolated to a specific cohort/task?
- Uniform regression → LLM or prompt issue
- Cohort-specific regression → context pattern issue or edge case in that user segment

### Observability Dashboard Layout
Recommended panels for any agent observability dashboard:
```
Row 1 — Health Overview
  [Task Completion Rate — 24h] [P95 Latency — 24h] [Error Rate — 24h]

Row 2 — LLM Signals
  [LLM Latency Heatmap] [Token Usage (prompt vs completion)] [Model Cost/hour]

Row 3 — Tool Health
  [Tool Success Rate by Tool] [Tool Latency by Tool] [Tool Call Volume]

Row 4 — Agent Quality
  [Shadow Eval Score — 7d] [Context Usage Distribution] [Hallucination Flag Rate]

Row 5 — Drift Signals
  [Completion Rate vs Baseline] [Latency Drift Z-Score] [Confidence Score Trend]
```

## Phase 3: Resources
- OpenTelemetry Agent Instrumentation: opentelemetry.io/docs
- Honeycomb for LLM Observability: honeycomb.io/blog/llm-observability
- Helicone — LLM observability platform (proxy-based, minimal instrumentation)
- Langfuse — open-source LLM observability and eval platform
- Arize AI — ML/LLM observability with drift detection
- DORA metrics adapted for AI agents: measure deployment frequency, change failure rate, MTTR

## Related Skills
- Agent Testing & Evaluation Protocol: https://clawmerchants.com/v1/data/agent-testing-eval-skill ($0.03)
- Agent Governance & SLA Compliance Protocol: https://clawmerchants.com/v1/data/agent-governance-sla-skill ($0.05)
- Multi-Agent Coordination & Task Routing: https://clawmerchants.com/v1/data/multi-agent-coordination-skill ($0.03)
