# Phase 4 — Technical Risk Assessment

## Goal
Surface the hardest technical problems before committing to a stack.
Recommend the one spike that de-risks the most.

The user is a developer (JS/TS/Node/React/Python). Speak at that level.

---

## 4.1 Risk Identification Framework

For each idea, assess risks across these categories:

### Data Risks
- Where does core data come from? (scraping, APIs, user-generated, proprietary)
- Is that source stable? (ToS compliance, rate limits, cost at scale)
- What happens if the data source changes or disappears?

### AI/ML Risks
- Is the quality of AI output central to the product's value?
- What's the failure mode when the model is wrong?
- Latency requirements — can the user wait 5–30 seconds, or must it be <1s?
- Context window / cost at scale — what's the $/query at 10k MAU?

### Integration Risks
- Third-party APIs that are flaky, expensive, or poorly documented
- Auth complexity (OAuth flows, enterprise SSO)
- Webhook reliability requirements

### Scale Risks
- What's the bottleneck at 10k users? (DB, LLM calls, scraping infra, storage)
- What changes architecturally at 100k users?
- Any state management that gets painful at scale? (sessions, queues, rate limiting)

### Compliance/Legal Risks
- Does the idea involve scraping sites that prohibit it?
- User data that triggers GDPR / CCPA?
- AI-generated content in regulated domains (finance, health, legal)?

---

## 4.2 Risk Matrix

Format as a table:

| Risk | Category | Severity (H/M/L) | Likelihood (H/M/L) | Mitigation |
|------|----------|-------------------|---------------------|------------|
| [Risk description] | Data | H | M | [one-line mitigation] |

Severity × Likelihood → priority order.

---

## 4.3 Spike Recommendation

Pick **one** thing to build first that:
1. Is the highest-risk technical assumption
2. Can be validated in 1–3 days
3. If it fails, kills the idea without wasted infrastructure

Format:
```
Spike Target: [what to build]
Why This One: [why this is the hardest/riskiest thing]
Time Estimate: ~X days
Success Criteria: [what "it works" means technically]
Failure Signal: [what outcome means rethink the approach]
```

---

## 4.4 Stack Recommendation (brief)

Given the idea and the builder's stack (JS/TS/Node/React/Python), recommend:
- **Backend**: [e.g., Node/Fastify, Python/FastAPI — and why]
- **AI Layer**: [e.g., Anthropic API with Claude Sonnet, or LangChain if orchestration is complex]
- **Data**: [e.g., Postgres + pgvector for embeddings, Redis for job queue]
- **Scraping** (if relevant): [e.g., Playwright + BrightData, or Firecrawl]
- **Hosting**: [e.g., Railway/Fly.io for MVP, then migrate]

Keep this to one bullet per category. No over-engineering.

---

## 4.5 Agentic System Assessment (if applicable)

If the idea involves multiple agents, orchestration, or async pipelines:
- How many distinct agent roles are needed at MVP?
- What's the failure/retry strategy when an agent step fails?
- Is a full agent framework needed (LangGraph, CrewAI) or is direct API orchestration sufficient?
- What's the observability plan? (logging, tracing LLM calls)

Flag: "Do you need an agentic system now, or can you fake it with sequential API calls first?"
Sequential is almost always faster to validate.
