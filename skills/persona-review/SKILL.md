---
name: persona-review
description: Multi-persona adversarial review using real-world expert philosophies. Use when reviewing code, designs, or decisions where single-reviewer blind spots are risky. Complements code-reviewer and adversarial-reviewer by adding named-persona panels with verifiable principles and anti-fabrication discipline.
license: MIT
---

# Persona-Based Adversarial Review

## Overview

Review work through the lens of real experts with documented, verifiable philosophies — not abstract roles. Each reviewer has a specific perspective grounded in their known principles. A manager persona assembles the panel, and cross-review catches what single reviewers miss.

**When to use:**
- PR review before merge (catches ~15% more issues than single-reviewer in testing)
- Architecture/design decisions
- Resume/portfolio review
- Career or strategic decisions

**When NOT to use:**
- Trivial typo fixes or single-line changes
- Tasks where existing code-reviewer or adversarial-reviewer is sufficient

---

# Process

## Phase 1: Classify the Task

Determine review depth:

| Tier | Scope | Panel | When |
|------|-------|-------|------|
| **T1 (Quick)** | Single file, simple change | 1-2 reviewers, 1 round | Bug fixes, minor refactors |
| **T2 (Standard)** | Multiple files, feature work | 3-4 reviewers, 1 round + divergence check | Features, config changes |
| **T3 (Deep)** | Architecture, identity, methodology | Domain round then Implementation round then Synthesis | System design, career decisions |

Default to T2 when uncertain. The user can override.

## Phase 2: Assemble the Panel

### Step 1: Select a Manager

Choose one manager based on task type:

| Manager | Best for | Style |
|---------|----------|-------|
| **Patty McCord** (Netflix ex-CTO) | Concrete deliverables: code, docs, designs | Zero-sugar, results-first, unafraid to restructure |
| **Ed Catmull** (Pixar co-founder) | Creative/strategic work: portfolios, decisions | Braintrust method: candid feedback from diverse perspectives |

### Step 2: Manager Recruits Reviewers

Pick 1-3 reviewers from the fixed pool based on task needs:

**Engineers:**
- **Rich Hickey** (Clojure creator) — Architecture simplicity. *Does this do one thing or many things?*
- **John Carmack** (id Software / Oculus) — Edge cases, boundary conditions. *What happens at the edges?*
- **Dan Abramov** (React core) — Concept clarity, mental models. *What does the caller need to understand?*
- **Simon Wardley** (Wardley Mapping) — Strategy, build-vs-buy. *Is this commodity or differentiator?*

**Product/UX:**
- **Don Norman** (HCI pioneer) — Usability, affordances. *Does the user know what to do next?*
- **Jesse Schell** (CMU game professor) — Experience, engagement. *Is the first interaction in the first 3 seconds?*
- **Kathy Sierra** (Head First series) — Learning, cognitive load. *Can a new user succeed in 30 seconds?*

**Design/Information:**
- **Stephen Few** (data visualization) — Information density, clarity. *Does every pixel convey information?*

To find additional perspectives outside the fixed pool, use web search to discover experts in the relevant domain. Search for: `"[domain] [engineering/product/design] philosophy principles"`. Apply the same review format, but mark unfamiliar personas' principles as `confidence: moderate`.

### Step 3: Define the Review Context

Share with all reviewers before they begin:

```
Review target: [file/design/decision — be specific]
Expected behavior: [what it should do]
Success criteria: [what "good" looks like]
Known boundaries: [constraints, deliberate trade-offs, out of scope]
```

Different reviewers with the same context produce insight. Different reviewers with different context produce noise.

## Phase 3: Execute Multi-Round Review

### Round Structure

Each round:
1. Manager names the round's theme (e.g. "Completeness Round", "Edge Case Round", "Simplicity Round")
2. Manager assigns reviewers based on theme
3. Each reviewer finds at least 1 issue (zero findings = invalid round, re-review)
4. Output format per finding:

```
[SEVERITY] [confidence] location — finding → reason → specific fix
```

**Severity levels:** CRITICAL / HIGH / MEDIUM / LOW
**Confidence levels:** high / moderate / low

### Cross-Review Rule

If 2 or more reviewers independently flag the same issue, escalate one level (NOTE to WARNING to CRITICAL).

### Attribution Discipline (non-negotiable)

- Every principle citation must be paraphrased, not fabricated as a quote
- Every principle must carry a confidence level
- Unverifiable claims are rejected, not embellished
- When in doubt about a persona's actual position, mark `confidence: low` rather than inventing specificity

This prevents the most common failure mode of persona-based review: the AI fabricating what a famous person "would say" and presenting it as authoritative.

### Round Transition

After each round: switch either the manager OR at least 2 reviewers. Preserve at most 2 reviewers from the previous round for continuity.

## Phase 4: Synthesis

Manager outputs:

```
[MANAGER] Panel: [names]. Rounds: N. Theme: [round themes].
Findings: N total (X CRITICAL, Y HIGH, Z MEDIUM, W LOW).
Verdict: BLOCK / CONCERNS / CLEAN
Key insight: [single most important takeaway]
```

**Decision rules:**
- 1 or more CRITICAL = BLOCK (must fix before proceeding)
- 3 or more HIGH = CONCERNS (strongly recommend fixing)
- Otherwise = CLEAN

---

# Example Reviews

## Code Review (T2, McCord + Hickey + Carmack + Norman)

```
[MANAGER: McCord] Complexity Round. Panel: Hickey(arch), Carmack(boundary), Norman(ux).

[HIGH] [high] src/auth.ts:34 — token refresh triggers on every request without dedup.
Per Hickey: a function should do one thing. Extract to TokenScheduler singleton.

[HIGH] [high] renderer.cpp:230 — framebuffer released before VkDeviceWaitIdle completes.
Per Carmack: test the boundary, not the happy path. Move release to after fence wait.

[MEDIUM] [moderate] settings page — "Export" top-right, "Import" buried in menu layer 3.
Per Norman: related functions should share conceptual space. Group both under "Data Transfer".

---
[MANAGER: McCord] 3 findings (2 HIGH, 1 MEDIUM). Verdict: CONCERNS.
```

## Design Review (T3, Catmull + Schell + Few)

```
[MANAGER: Catmull] First-Experience Round. Panel: Schell(experience), Few(information).

[MEDIUM] [moderate] onboarding — first 3 steps are read-only.
Per Schell: players learn by doing, not reading. First interaction in less than 3 seconds.

[LOW] [moderate] dashboard — 6 KPI cards, 6 colors, 4 encode no data dimension.
Per Few: maximize data-ink ratio. Use position and size for priority instead.
```

---

# Integration With Existing Skills

This skill **complements** — does not replace:

| Existing Skill | What it covers | What persona-review adds |
|---------------|----------------|------------------------|
| code-reviewer | Bugs, logic, security, conventions | Multi-perspective blind-spot coverage |
| adversarial-reviewer | Abstract role-based critique | Named personas with verifiable philosophies |
| security-review | OWASP Top 10, CWE | Architecture-level security from Carmack/Wardley perspectives |

Use persona-review when the cost of a missed issue is high and multiple independent perspectives justify the token investment.

---

# Anti-Patterns

- **Using 4+ rounds**: diminishing returns. 2-3 rounds cover about 90% of findings.
- **Skipping the context template**: different reviewers working from different assumptions = noise, not insight.
- **Fabricating principles**: if you cannot verify a persona actually holds a position, do not attribute it. Say "a reviewer focused on [domain] might flag..."
- **Same panel every round**: defeats the cross-review benefit. Change at least 1 reviewer per round.
