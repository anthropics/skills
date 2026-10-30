---
name: software-architecture-review
description: >
  Performs structured software architecture reviews covering design patterns, quality attributes,
  ADR (Architecture Decision Record) generation, anti-pattern detection, and scoring. Use this skill
  whenever the user mentions architecture review, system design evaluation, tech stack assessment,
  ADR creation, reviewing microservices/event-driven/layered/hexagonal designs, Gen AI or RAG
  architecture review, or asks for architectural fitness scoring — even if they don't say
  "architecture review" explicitly. Also trigger for questions like "is my design good?",
  "what's wrong with my system design?", or "how should I structure my AI pipeline?"
---

# Software Architecture Review

A skill for performing structured, expert-level software architecture reviews. Covers
traditional enterprise systems, cloud-native architectures, and modern Gen AI / RAG-based systems.

---

## When to Use This Skill

Trigger for any of these intents:
- "Review my architecture / system design"
- "What are the trade-offs of this design?"
- "Generate an ADR for this decision"
- "Is my RAG pipeline well-architected?"
- "What anti-patterns exist in my design?"
- "Score my architecture against quality attributes"
- Diagrams, C4 models, or architecture descriptions shared for feedback

---

## Review Process

Follow this four-phase process:

### Phase 1 — Understand Context

Gather or infer:
1. **System type** — Web app, microservices, event-driven, monolith, Gen AI pipeline, RAG system, etc.
2. **Quality priorities** — Ask the user to rank: Scalability, Security, Maintainability, Observability, Performance, Cost
3. **Constraints** — Cloud provider, team size, compliance requirements (HIPAA, SOC2, etc.)
4. **Maturity stage** — POC / MVP / Production / Legacy migration

If the user has shared a diagram or description, extract answers directly from it before asking questions.

---

### Phase 2 — Structural Analysis

Evaluate the architecture against these lenses:

#### Design Patterns
Check which architectural style is in use and whether it is applied correctly:

| Style | Key Concerns to Evaluate |
|---|---|
| Microservices | Service boundaries, data ownership, inter-service contracts |
| Event-Driven | Topic naming, consumer groups, event schema versioning |
| Layered (N-Tier) | Layer isolation, cross-layer dependency leaks |
| Hexagonal (Ports & Adapters) | Port definitions, adapter swap-ability |
| RAG / Gen AI Pipeline | Chunking strategy, embedding model choice, retrieval accuracy, LLM prompt isolation |
| CQRS / Event Sourcing | Read/write model separation, event store durability |

#### Quality Attributes Assessment

Score each attribute 1–5 (1 = critical gap, 5 = excellent):

- **Scalability** — Can the system handle 10x load? Where is the bottleneck?
- **Security** — Auth/AuthZ, secrets management, data-in-transit/at-rest encryption
- **Observability** — Logging, tracing, metrics — is the system debuggable in prod?
- **Maintainability** — Modularity, separation of concerns, test coverage design
- **Resilience** — Circuit breakers, retries, graceful degradation
- **Cost Efficiency** — Over-provisioned components, expensive API calls without caching

---

### Phase 3 — Anti-Pattern Detection

Check for and flag the following:

**Structural Anti-Patterns**
- ❌ **Distributed Monolith** — Microservices that share a database or deploy together
- ❌ **God Service / God Object** — One service/class doing everything
- ❌ **Chatty Microservices** — Excessive synchronous inter-service calls
- ❌ **Tight Coupling** — Components that cannot change independently
- ❌ **Anemic Domain Model** — Domain objects with no behavior, all logic in services
- ❌ **Spaghetti Integration** — Point-to-point integrations without an abstraction layer

**Gen AI / RAG Specific Anti-Patterns**
- ❌ **Naive Chunking** — Fixed-size chunking ignoring semantic boundaries
- ❌ **Missing Retrieval Evaluation** — No feedback loop measuring retrieval relevance
- ❌ **Prompt Injection Risk** — User input directly concatenated into system prompts
- ❌ **LLM as Orchestrator Without Guardrails** — Agentic loops without human-in-the-loop or fallback
- ❌ **Embedding Model Mismatch** — Query embedding model differs from document embedding model
- ❌ **No Hallucination Mitigation** — No grounding check, citation tracking, or confidence thresholds
- ❌ **Missing Responsible AI Layer** — No content filtering, bias checks, or audit logging

---

### Phase 4 — Output Generation

Always produce the following output sections:

#### Architecture Scorecard

```
## Architecture Scorecard: [System Name]

| Quality Attribute | Score (1–5) | Key Finding |
|---|---|---|
| Scalability       | X/5         | ... |
| Security          | X/5         | ... |
| Observability     | X/5         | ... |
| Maintainability   | X/5         | ... |
| Resilience        | X/5         | ... |
| Cost Efficiency   | X/5         | ... |
| **Overall**       | **X/5**     | ... |
```

#### Findings Summary

List findings as:
- 🔴 **Critical** — Must fix before production
- 🟡 **Warning** — Should fix in next sprint
- 🟢 **Positive** — Well-designed aspect worth preserving

#### Recommendations

For each critical/warning finding, provide:
1. **What** the issue is
2. **Why** it matters (impact on quality attribute)
3. **How** to fix it (concrete, actionable — not just "add caching")

#### ADR Generation (if requested or if a major decision is identified)

```markdown
# ADR-[NUMBER]: [Title]

**Status:** Proposed | Accepted | Deprecated | Superseded

**Context:**
[What is the problem or situation that prompted this decision?]

**Decision:**
[What was decided and why?]

**Consequences:**
- ✅ Positive: ...
- ❌ Trade-off: ...
- ⚠️ Risks: ...

**Alternatives Considered:**
| Option | Pros | Cons |
|---|---|---|
| Option A | ... | ... |
| Option B | ... | ... |
```

---

## Gen AI / RAG Architecture Review Module

For RAG and Gen AI systems, additionally evaluate:

### RAG Pipeline Checklist

| Component | What to Check |
|---|---|
| **Data Ingestion** | Source diversity, update frequency, metadata preservation |
| **Chunking Strategy** | Semantic vs. fixed-size, overlap, chunk size vs. context window |
| **Embedding** | Model alignment (query vs. doc), dimensionality, update strategy |
| **Vector Store** | Index type (HNSW, IVF), distance metric, filtering capability |
| **Retrieval** | Top-K tuning, hybrid search (dense + sparse), re-ranking |
| **Prompt Design** | System prompt isolation, context injection, few-shot examples |
| **LLM Response** | Citation grounding, hallucination mitigation, temperature settings |
| **Evaluation** | RAGAS or equivalent metrics (faithfulness, relevancy, context recall) |
| **Responsible AI** | Content filters, audit logging, human-in-the-loop for high-stakes outputs |

### Agentic / Multi-Agent Review (LangGraph, AutoGen, CrewAI)

- Are agent roles and boundaries clearly defined?
- Is there a supervisor or orchestration pattern?
- Are there defined exit conditions to prevent infinite loops?
- Is state management deterministic and recoverable?
- Are tool calls sandboxed and permission-scoped?

---

## Examples

**Example 1:**
Input: "Here's my system — React frontend, Node.js BFF, three Python microservices sharing a PostgreSQL database, deployed on Kubernetes."
Output: Scorecard highlighting Distributed Monolith anti-pattern (shared DB), recommendation to introduce service-specific schemas or migrate to event-driven data ownership, ADR for database-per-service.

**Example 2:**
Input: "Review my RAG pipeline: I chunk PDFs by 512 tokens, embed with OpenAI text-embedding-3-small, store in Pinecone, retrieve top-5, send to GPT-4o."
Output: RAG checklist evaluation, flag missing hybrid search and re-ranking, flag no hallucination mitigation layer, score retrieval design, recommend adding RAGAS evaluation.

**Example 3:**
Input: "Generate an ADR for choosing Kafka over RabbitMQ for our event bus."
Output: Full ADR document with context, decision rationale, trade-offs, and alternatives comparison table.

---

## Guidelines

- Always explain **why** a finding matters, not just what is wrong — help the user build architectural intuition, not just fix a checklist.
- Tailor the depth to the system's maturity — a POC needs different advice than a production system handling millions of requests.
- When reviewing Gen AI systems, always check for Responsible AI coverage — this is a critical quality attribute often overlooked.
- If the user shares a diagram (C4, sequence, ER), reference it directly in your findings.
- If no architecture is shared yet, prompt with: "Could you share your architecture diagram, a description of the components, or a C4 model? Even a rough sketch helps."
- Avoid generic advice like "add caching" — always specify *where*, *what type*, and *why*.
