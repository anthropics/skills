# Engineering Reasoning Approaches

Four specialized reasoning methodologies for software engineering tasks. Each includes the complete XML specification for use in Claude prompts, usage guidance, and calibration notes.

## Table of Contents

- [Code and Design Review](#code-and-design-review)
- [API Design](#api-design)
- [Performance and Scalability Analysis](#performance-and-scalability-analysis)
- [Threat Modeling](#threat-modeling)

---

## Code and Design Review

**Use when:** The task requires evaluating code, a pull request, a design document, or a technical proposal for quality, correctness, and maintainability. This evaluates something that already exists or has been proposed — the core analytical work is assessment and feedback, not creation.

```xml
<reasoning>
Approach this review as follows:
1. Understand the intent before evaluating the implementation. What problem is this code or design solving? What are the requirements and constraints? Misunderstanding the goal leads to irrelevant feedback.
2. Check correctness first. Does the implementation actually do what it claims to do? Look for logic errors, unhandled edge cases, race conditions, incorrect assumptions about input data, and failure modes that are silently swallowed rather than surfaced.
3. Evaluate the failure paths. What happens when inputs are invalid, dependencies are unavailable, or operations fail partway through? Is error handling consistent, or are some paths robust while others will crash or corrupt state?
4. Assess maintainability and clarity. Could another engineer understand this code six months from now without the original author explaining it? Are abstractions earning their complexity, or is there unnecessary indirection? Is naming precise enough that the code communicates its intent?
5. Identify any security or data integrity concerns. Is user input validated and sanitized? Are authorization checks in the right place? Could this change introduce a data inconsistency, a leak of sensitive information, or a privilege escalation?
6. Prioritize your findings. Separate critical issues (must fix before merge) from important improvements (should fix soon) from suggestions (could improve but acceptable as-is). Lead with the highest-priority items.
</reasoning>
```

**Calibration notes:**

Claude may produce feedback that is too uniformly weighted — listing fifteen items without clear priority signals. The methodology's step 6 addresses this, but if the output still lacks clear triage, add: "Limit critical findings to no more than five. If you identify more than five critical issues, the code needs a broader redesign rather than point fixes — say so."

Watch for Claude generating feedback on code style and formatting when the review should focus on substance. If style feedback is cluttering the output, add: "Do not comment on formatting, naming conventions, or code style unless they create genuine ambiguity or risk. Assume linting and formatting are handled by tooling."

---

## API Design

**Use when:** The task involves designing a new API (REST, GraphQL, gRPC, internal library interface) or evaluating an existing one. Focus is on the contract between components — the interface itself, its consistency, its evolution strategy, and the developer experience of using it.

```xml
<reasoning>
Approach this API design as follows:
1. Define who consumes this API and how. Is this a public API with external developers, an internal API consumed by other teams, or a library interface consumed within a single codebase? The consumer profile determines the tolerance for breaking changes, the need for documentation, and the appropriate level of abstraction.
2. Design the resource model or interface boundaries. What are the core entities? How do they relate? The model should reflect the domain concepts that consumers think in, not the internal data structures. If the API leaks implementation details, it is coupled to the implementation and will break when the implementation changes.
3. Evaluate consistency. Are naming conventions, error formats, pagination patterns, and authentication mechanisms uniform across all endpoints? Inconsistency is the most common source of developer frustration and integration bugs.
4. Plan for evolution. How will this API change over time without breaking existing consumers? Define the versioning strategy, the deprecation process, and what constitutes a breaking vs. non-breaking change. If backwards compatibility is critical, design the initial version with extension points that allow adding capabilities without modifying existing contracts.
5. Design the error contract. Errors are part of the API — not an afterthought. Define a consistent error format that gives consumers enough information to diagnose and handle failures programmatically, not just human-readable messages.
6. Assess operational concerns. How is this API rate-limited, monitored, and debugged? Can you trace a request through the system? Are there endpoints that could be abused for denial-of-service or data scraping? What SLA does this API commit to, and is that SLA achievable?
</reasoning>
```

**Calibration notes:**

Claude may produce API designs that are technically elegant but impractical — over-normalized resource models that require five requests for a common operation, or HATEOAS-compliant designs when the consumers just need a simple JSON API. If the output optimizes for theoretical purity over developer experience, add: "Optimize for the most common use cases. The API should make the easy things easy. If following a design principle makes the most common operations harder, the principle is not serving this API."

Watch for Claude defaulting to REST conventions regardless of the use case. REST is not always the right choice — for high-throughput internal services, gRPC may be better; for flexible queries, GraphQL may fit. Add context about performance requirements and consumer types to prevent default-mode thinking.

---

## Performance and Scalability Analysis

**Use when:** The task involves identifying performance bottlenecks, evaluating optimization tradeoffs, capacity planning, or analyzing how a system behaves under load. Use when the question is "why is this slow?" or "will this scale?" rather than "how should we build this?"

```xml
<reasoning>
Approach this performance analysis as follows:
1. Define the performance requirements concretely. What are the target latencies (p50, p95, p99)? What throughput must the system sustain? What is the expected load profile — steady, bursty, growing? Without concrete targets, "fast enough" is unmeasurable and the analysis has no anchor.
2. Identify the bottleneck before optimizing anything. Profile the system or reason about the architecture to find where time is actually spent. The bottleneck is almost always in one of: I/O (database queries, network calls, disk), computation (CPU-bound processing), contention (locks, connection pools, shared resources), or data volume (scanning too much data). Optimizing a non-bottleneck component produces no measurable improvement.
3. For each bottleneck, analyze the cause and the tradeoff space. Can the bottleneck be eliminated (e.g., removing an unnecessary query), reduced (e.g., adding an index, caching), or distributed (e.g., sharding, parallelization)? Every optimization has a cost — increased complexity, memory usage, eventual consistency, or development time. State the tradeoff explicitly.
4. Evaluate how the system scales. Where does it hit limits as load grows? Is scaling linear, sublinear, or superlinear in cost? Identify the first resource that saturates — that is the scaling ceiling. Distinguish between vertical scaling limits (bigger machines) and horizontal scaling limits (more machines, which introduces coordination overhead).
5. Consider second-order effects. Caching reduces latency but introduces cache invalidation complexity. Async processing improves throughput but complicates error handling and ordering. Read replicas increase read capacity but introduce replication lag. Every performance optimization shifts the problem — identify where it shifts to.
6. Recommend changes ordered by impact-to-effort ratio. The first optimization should be the one that delivers the most improvement for the least complexity. Avoid recommending a complete architectural overhaul when an index or a cache would solve the immediate problem.
</reasoning>
```

**Calibration notes:**

Claude may produce performance analysis that is theoretical rather than grounded in actual measurements. If no profiling data or metrics are available, Claude may invent plausible-sounding bottlenecks. When the analysis lacks real data, add: "Distinguish clearly between confirmed bottlenecks (based on provided metrics or profiling data) and hypothesized bottlenecks (based on architectural reasoning). For hypothesized bottlenecks, specify what measurement would confirm or eliminate the hypothesis."

Watch for Claude defaulting to "add caching" as the first recommendation regardless of the actual bottleneck — caching is a powerful tool but introduces invalidation complexity. For tasks where simplicity is critical, reinforce: "Prefer solutions that reduce complexity over solutions that add a new layer."

---

## Threat Modeling

**Use when:** The task involves analyzing a system's security posture, identifying attack vectors, evaluating trust boundaries, or designing security controls. This is a structured reasoning methodology for adversarial analysis — use when the question is "where are the vulnerabilities?" or "how could this be attacked?"

```xml
<reasoning>
Approach this threat model as follows:
1. Define the system boundary and the assets worth protecting. What data, capabilities, or access does this system hold that an attacker would value? Not everything needs the same level of protection — identify the crown jewels and the pathways that lead to them.
2. Map the trust boundaries. Where does the system transition between trust levels? Every trust boundary — between user input and server logic, between services, between internal network and external, between privileged and unprivileged operations — is a potential attack surface. Enumerate the boundaries and what crosses them.
3. Identify the threat actors and their capabilities. A script kiddie running automated scanners, a motivated attacker with specific interest in your data, a malicious insider with legitimate credentials, and a nation-state adversary require different defensive postures. Define which actors are in scope for this system based on its exposure and the value of its assets.
4. For each trust boundary, enumerate the attack vectors relevant to the in-scope threat actors. How could each boundary be crossed? What controls currently exist, and what are their failure modes? Focus on the vectors where the attacker's required capability is lowest relative to the asset value — these are the highest-priority risks.
5. Evaluate the existing controls. Are they defense-in-depth (multiple independent layers) or single-point-of-failure? What happens when a control fails — does the system fail open (allowing access) or fail closed (denying access)? Are there detection mechanisms that alert on control failure or bypass?
6. Prioritize findings by risk — the combination of likelihood (given the threat actor profile) and impact (given the asset value). Recommend mitigations for the highest-risk findings, with explicit assessment of residual risk after the mitigation is applied.
</reasoning>
```

**Calibration notes:**

Claude may produce threat models that are exhaustive but undifferentiated — listing every conceivable attack vector without calibrating to the actual threat profile. If the output reads like an OWASP checklist rather than a targeted analysis, add: "Focus on the five highest-risk attack vectors for this specific system and its threat profile. A focused threat model that drives action is more valuable than an exhaustive one that overwhelms the team."

Watch for Claude treating all trust boundaries as equally important. In most systems, the boundary between user input and server-side processing is far more critical than internal service-to-service boundaries on a private network. Add architectural context to help Claude calibrate.
