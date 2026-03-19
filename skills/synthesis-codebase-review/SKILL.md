---
name: synthesis-codebase-review
description: "Enterprise-scale codebase audit methodology with tiered review system (Essential through Mission-Critical). Use when asked to: codebase review, code audit, code review, review codebase, architecture review, security audit, full code review, enterprise review, codebase health check."
license: "CC0-1.0"
metadata:
  author: "Rajiv Pant"
  version: "1.0.0"
---

# Enterprise-Grade Codebase Review

## Purpose

A comprehensive, practical codebase audit methodology for projects of any size. Not every project needs every check — the tiered system ensures you apply the right level of rigor.

For the full detailed checklist, see `references/detailed-checklist.md` in this skill directory.

---

## How to Use This Skill

### Step 1: Assess Project Tier

Complete the Project Complexity Assessment to determine which tier applies.

### Step 2: Review Applicable Sections

Each section and many individual items are marked with tier indicators:
- **Essential** (Tier 1) — Apply to ALL projects, even weekend hacks
- **Standard** (Tier 2) — Apply to team projects and production apps
- **Enterprise** (Tier 3) — Apply to large-scale, multi-team, or regulated systems
- **Mission-Critical** (Tier 4) — Apply to financial, healthcare, infrastructure, or high-stakes systems

### Step 3: Skip What Doesn't Apply

- Tier 1: focus only on Essential items (~50 checks)
- Tier 2: include Essential and Standard items (~150 checks)
- Tier 3: include Essential, Standard, and Enterprise items (~400 checks)
- Tier 4: include everything (~900+ checks)

---

## Pre-Flight Checklist

Complete these checks before starting any review. Skipping pre-flight has caused real wasted effort on real engagements.

### Branch Selection

- Confirm which branch represents the current working state — do NOT assume `main` is current
- Check the most recent commit date on the target branch. If `main` has not been updated in weeks and there is an active branch with many commits ahead, you are likely reviewing a stale snapshot
- Ask whether the team uses git-flow, trunk-based, or another model. In git-flow, `develop` is often the correct review target

### Review Scope

- Confirm which directories to exclude (vendor/, node_modules/, generated/, etc.)
- Ask if a previous review has been conducted. If yes, obtain prior findings to enable delta review mode
- Confirm expected output format (markdown, PDF, etc.) and audience (engineering team, leadership, both)

---

## Project Complexity Assessment

Score each characteristic (0 = No, 1 = Yes):

**Scale & Users:** >1 developer, >5 developers, >20 developers, >100 users, >10K users, >1M users

**Business Criticality:** Production system, downtime costs money, downtime costs >$10K/hour, breach would make news, contractual SLAs

**Data Sensitivity:** User accounts, PII, financial data, health data (HIPAA), regulated data (GDPR, SOX)

**Architecture Complexity:** >1 service, >5 services, database exists, multiple data stores, third-party integrations, >5 integrations

**Operational Requirements:** 99% uptime, 99.9% uptime, 99.99% uptime, dedicated ops/SRE team, 24/7 on-call

| Score Range | Tier | Description |
|-------------|------|-------------|
| 0-4 | Tier 1 - Essential | Solo/hobby projects, prototypes, internal tools |
| 5-10 | Tier 2 - Standard | Small team projects, production apps, startups |
| 11-18 | Tier 3 - Enterprise | Large teams, regulated industries, enterprise customers |
| 19+ | Tier 4 - Mission-Critical | Financial systems, healthcare, critical infrastructure |

---

## Minimum Viable Review (15-Minute Quick Check)

Use this for a rapid health assessment. These are the absolute essentials that apply to ANY project.

### Security Essentials (5 minutes)
- No secrets in code: run `git log -p | grep -i "password\|secret\|api_key\|token"` — should return nothing
- Dependencies not ancient: check for critical vulnerabilities (`npm audit`, `pip-audit`, etc.)
- HTTPS only for all external communication
- Input validated before use
- Auth exists if there are users

### Code Health (5 minutes)
- It builds: clean build with no errors
- Tests exist and pass
- No obvious duplication (no copy-pasted files or massive repeated blocks)
- Readable: a new developer could understand the main flow

### Operations Essentials (5 minutes)
- README exists with instructions on how to run it
- Documented or automated deployment process
- Application produces logs
- Errors logged or sent somewhere visible
- Config externalized (no hardcoded environment-specific values)

**Quick Score: ___ / 15.** If you score <12, address the gaps before proceeding.

---

## Review Categories

The full detailed checklist is in `references/detailed-checklist.md`. Here is an overview of all 16 review categories:

### 1. Architecture & System Design
Architectural foundation, API design and contracts, service communication, data architecture. Evaluate whether the chosen patterns are appropriate for scale and team size.

### 2. Secrets, Credentials & Sensitive Data
Active secret scanning, secret type inventory, AI tool configuration files, comment-aware credential scanning, secret management, preventive controls. This section is CRITICAL for all tiers.

### 3. Code Duplication & Reusability
Duplication analysis, shared code and libraries, abstraction quality.

### 4. Code Quality, Efficiency & Optimization
Basic code quality, algorithmic efficiency, database efficiency, memory and resource efficiency, concurrency and thread safety.

### 5. Clean Code & Software Engineering Principles
Naming and readability, function design, SOLID principles, error handling, defensive programming.

### 6. Code Readability & AI/Human Maintainability
Human readability, documentation, AI and automation friendliness.

### 7. Testing
Test existence, coverage, test types (unit, integration, API, E2E, performance, security), test quality (verify tests actually test behavior, not just imports).

### 8. Security
Authentication, authorization, input validation, data protection, dependency security.

### 9. Multi-Tenancy (Tier 3+)
Tenant isolation, configuration, lifecycle.

### 10. Identity & SSO (Tier 3+)
SSO support, session management.

### 11. Scalability & Performance (Tier 2+)
Horizontal scaling, auto-scaling, response times, caching, CDN.

### 12. Reliability (Tier 2+)
Fault tolerance, data durability, backups, disaster recovery.

### 13. Observability (Tier 2+)
Logging, monitoring, alerting, distributed tracing.

### 14. Deployment & Operations
Build and deploy documentation and automation, deployment strategy, configuration management.

### 15. Licensing & Legal
Dependency licenses, intellectual property, attribution.

### 16. Developer Experience
Getting started documentation, development workflow, CI speed.

### Addenda
- **Open Source Software Addendum** — License, community docs, security policy, versioning, distribution, contribution workflow, project health, testing, documentation
- **Proprietary Software Addendum** — Trade secret protection, vendor management, customer data protection
- **Industry-Specific Addenda** — Financial services, healthcare, e-commerce, government/public sector

---

## Output Format

### Key Principle: Strengths Before Findings

All reports lead with strengths before findings. Demonstrating that you understand what the team built well makes critical findings land as constructive guidance rather than an attack.

### Tier 1-2: Simplified Report

```markdown
## Codebase Review Summary

**Project**: [Name]
**Tier**: [1-Essential / 2-Standard]
**Date**: YYYY-MM-DD

### Quick Health Check: Pass / Issues / Fail

### Strengths
1. [What the codebase does well]
2. [Notable good practices]

### Key Findings

| # | Finding | Severity | Location | Fix |
|---|---------|----------|----------|-----|
| 1 | [Description] | Critical/High/Medium/Low | `path:line` | [Action] |

### Recommended Actions
1. [Top priority action]
2. [Second priority]
3. [Third priority]
```

### Tier 3-4: Full Report

Include executive summary with overall score, per-category scores, top strengths, top critical findings, detailed findings with severity/location/evidence/recommendation/effort, and a phased action plan (immediate, short-term, medium-term).

### Delta Review Mode

When a prior review exists, use delta mode. A standalone review says "here are your problems." A delta review says "here is your trajectory." The second is far more useful for engineering leadership.

For each finding from the prior review, classify its current status:

| Status | Meaning |
|--------|---------|
| **Fixed** | Finding fully resolved |
| **Partially Fixed** | Improvement made but not complete |
| **Still Present** | No change — deferred or not yet addressed |
| **Worse** | Finding has regressed or expanded in scope |
| **New** | Finding not present in prior review |

### Deliverable Organization

Date-stamp review deliverables in folders:

```
reviews/
├── 2025-01-15/
│   ├── review-summary.md
│   ├── detailed-findings.md
│   └── executive-report.pdf
├── 2025-04-15/
│   ├── delta-review.md         ← compares against 2025-01-15
│   ├── detailed-findings.md
│   └── executive-report.pdf
```

---

## Key Principles

1. **Tier-appropriate rigor.** Do not apply Tier 4 scrutiny to a weekend project. Do not skip Tier 1 basics for an enterprise system.
2. **Evidence-based findings.** Every finding must cite specific file paths and line numbers with concrete remediation steps.
3. **Practical over theoretical.** Every checklist item should catch real issues found in real codebases.
4. **AI-friendly wording.** Checklist items should be clear enough for AI assistants to evaluate programmatically.
5. **Strengths first.** Understanding what the team did well is as important as finding problems.
