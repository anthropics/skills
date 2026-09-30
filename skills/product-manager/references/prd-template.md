# Strategic PRD Template

A comprehensive Product Requirements Document template for Product Managers. Includes strategic context alongside tactical requirements.

---

## [Initiative Name]

**Author:** [Name]
**Date:** [Date]
**Status:** Draft | In Review | Approved
**Reviewers:** [Engineering Lead, Design Lead, key stakeholders]

---

### 1. Executive Summary

[2-3 sentences: What are we building, why, and what's the expected impact?]

---

### 2. Problem Statement

**Customer problem:**
[Describe the pain point from the customer's perspective]

**Evidence:**
- [User research finding with quote]
- [Support data: X tickets/month about this issue]
- [Churn analysis: Y% of churned users cited this]
- [Competitive gap: Competitors A and B solve this]

**Who is affected:**
[Primary segment, secondary segments, estimated reach]

---

### 3. Strategic Context

**How this aligns with company/product strategy:**
[Connect to company OKRs or strategic pillars]

**Strategic bet:**
We believe [doing X] will result in [outcome] for [segment].
We will know this is true when [measurable signal].

---

### 4. Goals and Success Metrics

**Primary metric:** [The one number that defines success]
**Supporting metrics:**

| Metric | Baseline | Target | Timeline |
|---|---|---|---|
| [Primary metric] | [Current] | [Target] | [When] |
| [Supporting metric 1] | [Current] | [Target] | [When] |
| [Supporting metric 2] | [Current] | [Target] | [When] |

**Guardrail metrics** (must not degrade):
- [Metric that should stay stable, e.g., page load time, existing feature engagement]

---

### 5. User Stories and Requirements

#### Epic: [Epic Name]

**Story 1:** As a [user], I want [action] so that [value].

Acceptance Criteria:
- Given [context], When [action], Then [result]
- [Additional criteria]

Priority: Must Have | Should Have | Could Have

**Story 2:** [...]

#### Non-functional Requirements
- Performance: [Latency, throughput targets]
- Scalability: [Expected load]
- Security: [Authentication, authorization, data handling]
- Accessibility: [WCAG level]

---

### 6. Scope

**In scope (MVP):**
- [Must Have features]

**In scope (fast follow):**
- [Should Have features for next iteration]

**Out of scope:**
- [Explicitly excluded with rationale]

---

### 7. Design

[Link to Figma/design tool]

**Key UX decisions:**
- [Decision and rationale]

**Open design questions:**
- [Unresolved UX question]

---

### 8. Technical Approach

[Link to technical design doc if separate]

**Architecture impact:**
- [New services, API changes, database changes]

**Dependencies:**
- [Team/service dependencies with owners]

**Technical risks:**
| Risk | Likelihood | Impact | Mitigation |
|---|---|---|---|
| [Risk] | [H/M/L] | [H/M/L] | [Plan] |

---

### 9. Go-to-Market

**Target launch:** [Date or sprint]

**Rollout plan:**
1. Internal dogfood → [Date]
2. Beta with [N] customers → [Date]
3. General availability → [Date]

**Marketing/Sales needs:**
- [ ] Landing page update
- [ ] Sales enablement materials
- [ ] Customer communication
- [ ] Help documentation

---

### 10. Alternatives Considered

| Option | Pros | Cons | Why not chosen |
|---|---|---|---|
| [Option A] | [Pros] | [Cons] | [Reason] |
| [Option B] | [Pros] | [Cons] | [Reason] |

---

### 11. Open Questions

| # | Question | Owner | Deadline | Status |
|---|---|---|---|---|
| 1 | [Question] | [Name] | [Date] | Open |

---

### 12. Appendix

[Supporting data, research transcripts, competitive analysis, technical diagrams]
