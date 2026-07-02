# Review Phase Protocols

Reference file for deep-brainstorming skill. Load when running the three-phase review.

## Key Principle

Each review phase must be a **separate agent** with **no context from prior phases**. The agent receives only the spec document and its review instructions. This prevents confirmation bias from earlier approvals.

## Phase R1: Verify-Fix

Standard review for consistency, completeness, and correctness.

### R1 Prompt

```
Review this architecture specification for:

1. **Internal consistency** — Do sections contradict each other?
2. **Completeness** — Are there requirements from the vision that aren't addressed?
3. **Factual accuracy** — Are version numbers, API references, and benchmarks current?
4. **Clarity** — Would a developer understand exactly what to build?
5. **Claim verification** — Are provenance records present for cited numbers?
   Flag any claim marked UNVERIFIED or VENDOR-ONLY.

For each issue found:
- Cite the exact section and line
- Explain what's wrong
- Suggest a specific fix

Categorize issues as: CRITICAL (blocks implementation), HIGH (causes problems), LOW (style/clarity).
```

### R1 Process

1. Agent reviews spec → produces findings
2. Fix all CRITICAL and HIGH issues
3. Re-run R1 agent on the fixed spec
4. Continue until R1 returns clean (no CRITICAL or HIGH)

## Phase R2: Adversarial (MANDATORY for Standard+)

Challenges every architectural decision. Specifically looks for what standard review misses.

**This phase is NOT optional for Standard intensity.** Evidence: adversarial review has caught 7+ YAGNI violations and multiple critical issues invisible to standard review and to deepening agents. "The plan already went through N agents" is the EXACT rationalization this phase counters.

### R2 Prompt

```
You are reviewing a specification that has already passed standard review.
Your job is to find what the standard reviewers missed.

DO NOT trust the previous approval. Assume the spec has unfound problems.

Focus on:
1. **Architectural contradictions** — Does the system design actually work end-to-end?
   Trace a request from user input to database and back. Where does it break?
2. **Phantom requirements** — Are there requirements that the client never asked for?
   Compare every spec requirement against the vision document. Flag additions.
3. **Tool selection justification** — For each chosen tool, can you find a stronger alternative?
   The burden of proof is on the chosen tool, not the alternatives.
4. **Assumption audit** — What assumptions does the spec make about:
   - Scale (concurrent users, data volume)
   - Integration (APIs, services that "support X")
   - Performance (latency, throughput)
   Are these assumptions verified or hoped?
5. **Missing failure modes** — What happens when:
   - The primary database is unreachable
   - An external API changes its contract
   - Traffic exceeds the stated capacity by 10x
   - A dependency is deprecated

For each finding, assign a confidence level:
- CERTAIN: Demonstrably wrong (cite evidence)
- LIKELY: Strong reason to believe it's wrong
- WORTH INVESTIGATING: Suspicious but not confirmed

Only CERTAIN and LIKELY findings need fixing before proceeding.
```

### R2 Process

1. Agent reviews spec with adversarial lens → produces findings
2. For CERTAIN findings: fix immediately
3. For LIKELY findings: verify independently, then fix or dismiss with evidence
4. Re-run R2 agent on the fixed spec
5. R2 is clean when no CERTAIN or LIKELY findings remain

## Phase R3: Security/Operations

Production readiness review. Ignores formatting and style entirely.

### R3 Prompt

```
Review this architecture specification for production readiness.
Ignore formatting, style, and documentation quality — focus only on:

1. **Security vulnerabilities**
   - Authentication/authorization gaps
   - Data exposure risks (PII, credentials, tokens)
   - Input validation gaps (injection, XSS, SSRF)
   - Secret management approach
   - Encryption at rest and in transit

2. **Scalability bottlenecks**
   - Single points of failure
   - Connection pool limits
   - Database query patterns under load
   - Caching strategy gaps
   - Background job queue saturation

3. **Error handling gaps**
   - What happens when external services fail?
   - Retry and circuit breaker strategies
   - Data consistency during partial failures
   - User-facing error messages (information leakage?)

4. **Deployment complexity**
   - How many moving parts to deploy?
   - Rollback procedure
   - Database migration safety
   - Zero-downtime deployment feasibility

5. **Testing gaps**
   - What's untestable in the current design?
   - Integration test complexity
   - Mock/stub requirements for CI

6. **Operational burden**
   - Monitoring and alerting coverage
   - Log aggregation approach
   - On-call complexity (how many systems to understand?)
   - Cost estimation accuracy

For each finding:
- Severity: CRITICAL (must fix before implementation) / HIGH (fix during implementation) / MEDIUM (track as TODO)
- Specific recommendation
```

### R3 Process

1. Agent reviews spec for ops/security → produces findings
2. CRITICAL findings: fix before proceeding to planning
3. HIGH findings: add to implementation plan as requirements
4. MEDIUM findings: track in TODO for later phases
5. Re-run R3 until no CRITICAL findings remain

## "Objectively Best?" Final Gate

After all required review phases for your selected intensity pass, apply this final quality gate.

### Protocol

This is NOT a review phase — it's a re-read of the entire spec with fresh eyes.

1. **Re-read the spec from the beginning** — not from memory of writing it
2. For each major technology choice, ask:
   - "Is this the objectively best option, or the most familiar one?"
   - "What evidence supports this over the alternatives?"
   - "If we removed the tool name and described only the requirements, would research agents converge on this same choice?"
3. For each cited number or benchmark:
   - "Is this verified from an independent source?"
   - "Is the provenance record complete?"
4. For each section:
   - "Would a developer new to this project understand exactly what to build?"
   - "Is anything here because an agent suggested it rather than because the requirements demand it?"

### Quality Gate Pass Criteria

The spec passes the quality gate when:
- [ ] Every technology choice is backed by verified evidence (not popularity)
- [ ] Every cited number has a complete provenance record
- [ ] No phantom requirements remain (everything traces to the client brief)
- [ ] A fresh reader could implement from this spec without ambiguity
- [ ] The user has reviewed and approved the final spec

If any of these fail, fix the issue and re-run the relevant review phase.
