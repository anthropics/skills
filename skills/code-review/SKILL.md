---
name: code-review
description: |
  Deep, structured code review and analysis skill. Use this skill whenever the user wants to review, audit, debug, or analyze code — even if they just say "look at my code", "check this", "find bugs", "security audit", "what's wrong with this", "review my PR", or "help me improve this codebase". Also trigger when the user uploads or shares code files and asks for feedback, optimization, or fixes. This skill covers full-stack analysis: architecture mapping, bug identification, security vulnerabilities, edge cases, performance issues, and maintainability concerns. Always use this skill for any non-trivial code review task.
---

# Code Review Skill

A structured, approval-gated code review workflow covering architecture analysis, issue identification, false-positive verification, and solution proposals — with no changes applied without explicit user sign-off.

---

## Workflow Overview

```
1. Research & Context  →  2. Architecture Map  →  3. Issue Identification
         ↓                                                    ↓
4. Verify & Score      →  5. Prioritized Report →  6. Wait for Approval
                                                             ↓
                                                    7. Implement Approved Fixes
```

---

## Step 1: Research & Context

Before diving into the code:

- **Search for current info** when the tech stack, framework versions, or libraries are unfamiliar or may have changed. Use web search to check latest docs, known CVEs, and breaking changes.
- **Verify compatibility** — confirm framework/library version constraints that might affect proposed solutions.
- **Identify the stack** — note languages, frameworks, databases, and cloud services in use.
- **Read project conventions** — check for `REVIEW.md`, `CLAUDE.md`, `.eslintrc`, `pyproject.toml`, or similar files that encode project-specific review rules. Respect these over generic best practices.

> Only search what's necessary. For well-known, stable APIs (e.g., vanilla JS, Python stdlib), skip search.

---

## Step 2: Architecture Review

Map the full system before identifying individual issues. Cover:

| Layer | What to document |
|---|---|
| Backend | Services, endpoints, business logic, data models |
| Frontend | Components, state management, routing, rendering strategy |
| Database | Schema, query patterns, ORM usage, migrations |
| APIs | Internal and external integrations, auth mechanisms |
| Auth | Authentication flow, authorization rules, token handling |
| Data flow | How user input travels through all layers |
| Tests | Test coverage, testing strategy, gaps in critical paths |

For large codebases, use parallel analysis of subsystems when possible.

---

## Step 3: Issue Identification

Scan across these five categories:

### 🔴 Critical — Security
- SQL injection, XSS, CSRF vulnerabilities
- Exposed secrets, API keys, credentials in code
- Insecure deserialization or file handling
- Missing authentication/authorization checks
- Insecure dependencies (check CVE databases if needed)

### 🟠 High — Bugs
- Logic errors producing incorrect output
- Runtime exceptions or crashes
- Broken core features or data corruption risks

### 🟡 Medium — Edge Cases & Robustness
- Null/undefined handling gaps
- Empty state and boundary condition failures
- Race conditions or async ordering issues
- Unhandled error paths

### 🔵 Medium — Performance
- N+1 query problems
- Memory leaks or unbounded growth
- Inefficient algorithms (O(n²) where O(n log n) is feasible)
- Blocking operations in async contexts

### ⚪ Low — Maintainability
- Code duplication
- Poor naming or missing documentation
- Missing error handling
- Style inconsistencies

---

## Step 4: Verify & Score

Before reporting, verify each finding to reduce false positives:

1. **Trace the code path** — confirm the issue is actually reachable in production. Check if guards, middleware, or upstream validation already prevent it.
2. **Check test coverage** — if a robust test covers the exact scenario, downgrade or note it.
3. **Assess real-world impact** — a theoretical vulnerability behind authentication + rate limiting + input validation is lower risk than one on a public endpoint.

Assign each finding a **confidence level**:

| Confidence | Meaning |
|---|---|
| **HIGH** | Confirmed via code path tracing; reproducible |
| **MEDIUM** | Likely issue but depends on runtime conditions or config |
| **LOW** | Theoretical concern; may be mitigated by factors outside visible code |

Drop findings that are clearly false positives after verification. Don't pad the report.

---

## Step 5: Report Format

For every verified issue, provide:

```
**[PRIORITY] [CONFIDENCE] Issue Title**

📁 File: `path/from/project/root.ext`
📍 Lines: 45–52

**Current code:**
```language
// existing code block
```

**Proposed fix:**
```language
// complete replacement code
```

**Why:** Concise explanation of the problem.
**Impact:** What changes, any side effects or migration notes.
**Test gap:** Whether existing tests cover this scenario (Yes/No/Partial).
```

Group issues by priority level (Critical → High → Medium → Low).

At the end of the report, include a **Summary Table**:

| # | Priority | Confidence | File | Issue | Lines | Test Gap |
|---|---|---|---|---|---|---|
| 1 | 🔴 Critical | HIGH | `auth/login.js` | SQL injection via unsanitized input | 34–38 | Yes |
| 2 | 🟠 High | MEDIUM | `api/orders.js` | Uncaught promise rejection | 91 | No |
| ... | | | | | | |

**Totals:** X critical, Y high, Z medium, W low — across N files.

---

## Step 6: Approval Gate ⛔

**NEVER implement changes before the user explicitly approves.**

After presenting the report:
1. Ask the user which issues to address
2. If they say "fix everything" or "all of them" — confirm the full list before proceeding
3. If they ask for immediate fixes on a specific issue — confirm that specific issue only
4. Proceed to Step 7 only after clear approval

Example prompt after report:
> "I've found X issues across Y files. Which of these would you like me to fix? I can address all of them, just the critical ones, or specific items — just let me know."

---

## Step 7: Implementation

Once approved:

- Make **minimal changes** — only what's necessary to fix the approved issue
- Preserve existing behavior unless the behavior itself is the bug
- Follow the project's existing code style and conventions
- Add inline comments for non-obvious changes explaining the *why*
- Ensure changes don't break existing tests; flag if test updates are needed
- Present complete updated file(s) clearly labeled with the file path
- After implementation, re-verify the fix doesn't introduce new issues

---

## Principles

| Principle | Guideline |
|---|---|
| Minimal changes | Don't refactor beyond what fixes the issue |
| Backward compatibility | Preserve existing interfaces unless they're the problem |
| Standards compliance | Match the project's language/framework conventions |
| Testability | Solutions should be verifiable; flag untestable changes |
| Documentation | Complex changes get inline comments explaining the "why" |
| No false padding | Drop unverifiable or clearly-mitigated findings |
| Project rules first | Respect REVIEW.md / CLAUDE.md / linter configs over generic advice |

---

## Priority Reference

| Level | Label | Examples |
|---|---|---|
| P0 | 🔴 Critical | Security vulns, data loss, crashes |
| P1 | 🟠 High | Core feature bugs, major perf issues |
| P2 | 🟡 Medium | Edge cases, minor bugs, robustness |
| P3 | ⚪ Low | Style, minor opts, nice-to-haves |

## Confidence Reference

| Level | When to assign |
|---|---|
| HIGH | Code path confirmed, issue is reproducible |
| MEDIUM | Likely but depends on runtime/config/environment |
| LOW | Theoretical; may be mitigated elsewhere |
