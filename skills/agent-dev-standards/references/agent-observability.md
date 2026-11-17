# Agent Observability

Span design, trace model, and cost attribution for Agents.

## Span Design

Each Agent operation emits spans:

| Span | Parent | Attributes |
|------|--------|------------|
| agent.run | (root) | agent_name, prompt_version, session_id |
| llm.call | agent.run | model, input_tokens, output_tokens, cost |
| tool.call | agent.run | tool_name, parameters, duration_ms, status |
| tool.retry | tool.call | attempt, error, backoff_ms |

## Trace Model

A complete trace captures the full agent execution:

`
Trace: agent.run (code-reviewer, v1.2.0)
  +-- llm.call (decide_action)
  +-- tool.call (search_documents, query="auth bug", status=success)
  |     +-- tool.retry (attempt 2, timeout 5s)
  +-- llm.call (process_results, tokens=1200)
  +-- tool.call (comment, pr_id=42, status=success)
  +-- llm.call (final_summary, tokens=800)
`

## Cost Attribution

Every LLM call must be tagged for cost tracking:

`python
# OpenTelemetry-style span attributes
span.set_attribute("agent.name", "code-reviewer")
span.set_attribute("prompt.version", "1.2.0")
span.set_attribute("tool.name", "search_documents")
span.set_attribute("cost.usd", 0.0042)
`

This enables querying cost by agent, cost by prompt version, cost by tool.

## Degradation Detection

Monitor these metrics over time (from the reliability series):

| Metric | Warning | Critical |
|--------|---------|----------|
| Avg tool calls per task | > 20 | > 30 |
| Error rate | > 5% | > 15% |
| Cache hit rate drop | > 10% in 7d | > 25% in 7d |
| Cost per invocation | > 2x baseline | > 5x baseline |
