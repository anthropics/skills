---
name: synthesis-pr-review
description: "Delta review methodology for pull requests in synthesis-coded projects, covering regression risk assessment, root cause analysis, and integration with the adopt-and-adapt workflow. Use when asked to: PR review, pull request, code review, review PR, delta review, review pull request, check PR, evaluate PR."
license: "CC0-1.0"
metadata:
  author: "Rajiv Pant"
  version: "1.0.0"
---

# Synthesis PR Review

A pull request in a synthesis-coded project is not just "does the code work?" It is "does this change make the system better without making it worse?" This skill defines how to evaluate that.

---

## Where This Fits

Three related skills cover different scopes:

| Skill | Scope | When to use |
|-------|-------|-------------|
| **codebase-review** | Full codebase audit (16 categories, tiered) | New engagement, periodic health check, or major milestone |
| **synthesis-code-integration** | Integration workflow (adopt-and-adapt pattern, quality gates) | When merging contributor work into main |
| **pr-review** (this one) | Delta review of a single change | Every PR, before peer approval or lead integration |

PR review is the **most frequent** of the three. It happens on every change. The quality gates from the synthesis-code-integration skill apply here, but this skill operationalizes them as specific review steps.

---

## The Delta Review Mindset

A PR review is a delta review — you are evaluating a change against the current state of the codebase, not evaluating the codebase itself.

**Key questions:**

1. **Does this change do what it claims?** — Read the PR description. Read the code. Do they match?
2. **Does it introduce regressions?** — What worked before that might break now?
3. **Is it the right fix?** — Does it address root cause, or a symptom?
4. **Is it complete?** — Or does it need companion changes to actually solve the problem?
5. **Is it consistent?** — Does it follow existing patterns, or does it diverge without justification?

---

## Review Checklist

### 1. Scope and Separation of Concerns

- [ ] PR does one thing (not multiple unrelated fixes bundled together)
- [ ] PR description accurately describes the change and its motivation
- [ ] If the PR bundles fixes, each fix is clearly identified and could stand alone

**Red flag:** A PR titled "fix X" that also quietly changes Y.

### 2. Root Cause Analysis

- [ ] The fix addresses the actual root cause, not a downstream symptom
- [ ] If the root cause is complex, the PR explains why this specific approach was chosen
- [ ] The PR does not mask a deeper architectural issue

**How to evaluate:** Ask — if the underlying condition that caused the bug occurs again in a slightly different way, does this fix still work? If not, it is a symptom fix.

### 3. Regression Risk

- [ ] No existing behavior is broken by the change
- [ ] Error handling paths are preserved (not accidentally removed)
- [ ] Edge cases still work (empty states, error states, concurrent access)
- [ ] If the PR modifies shared code, all callers are accounted for

**Technique:** Read the diff backward — look at what was REMOVED or CHANGED, not just what was added. Removed lines are where regressions hide.

### 4. Architectural Consistency

- [ ] The pattern used matches how similar things are done elsewhere in the codebase
- [ ] If the pattern diverges from existing code, the divergence is justified
- [ ] No architectural debt is introduced without acknowledgment

**Technique:** Find the closest analog in the codebase. If component A handles retries one way and this PR makes component B handle retries a different way, ask why.

### 5. Completeness

- [ ] The fix is sufficient to actually solve the stated problem
- [ ] If companion changes are needed (backend + frontend, migration + code), they are either included or explicitly tracked
- [ ] Tests cover the new behavior (or a clear reason why they do not)

**Red flag:** A frontend fix for a problem whose root cause is in the backend.

### 6. Security

- [ ] No credentials or secrets in the diff
- [ ] Input validation at system boundaries
- [ ] Auth checks preserved for protected endpoints
- [ ] No new SQL injection, XSS, or command injection vectors
- [ ] Grep the diff for `secret`, `token`, `password`, `key` in any `logger.*`, `print()`, or `console.log()` statement
- [ ] Check JWT/auth code never logs credentials
- [ ] Verify dev conveniences are removed (hardcoded emails, auto-login, skip-auth flags)
- [ ] For large PRs (>1000 lines), question whether it should be split
- [ ] Require PR description — PRs without descriptions are harder to review and more likely to hide issues

**AI code assistant warning:** AI coding tools commonly introduce debug logging that includes sensitive data. Add a pre-commit check that flags patterns like `log.*secret`, `print.*token`, `console.log.*password` in staged files. Prevention is more reliable than review-time detection.

### 7. Data Integrity

- [ ] Database schema changes are idempotent (safe to run multiple times)
- [ ] New fields have sensible defaults or are nullable
- [ ] No data loss scenarios (e.g., overwriting fields without preserving previous values)
- [ ] API contracts are backward-compatible (or breaking changes are intentional and documented)

---

## Verifying AI-Generated Analysis

When someone presents a root cause analysis — whether from an AI tool, a contributor, or a team member — verify the conclusion against actual code, not just intermediate findings.

**Why this matters:** AI analysis can be 5-of-6 correct but critically wrong on the conclusion. The intermediate findings (file X calls function Y, which queries table Z) may all be accurate, but the final conclusion ("therefore the bug is in the query") may miss an alternative code path that actually handles the case differently.

**Verification process:**

1. **Read the cited code yourself.** Do not rely on someone else's summary of what the code does.
2. **Look for alternative code paths.** The analysis may describe one path accurately while missing another that handles the same input differently (error handlers, fallback logic, middleware, decorators).
3. **Be skeptical of sweeping conclusions.** Phrases like "zero effect," "completely broken," or "never works" are almost always wrong. Reality is usually more nuanced.
4. **Check the system-level view.** A function-level analysis may be correct in isolation but miss interactions with caching, middleware, event handlers, or background jobs that change the behavior.
5. **Test the conclusion, not just the intermediate steps.** If the analysis says "changing X will fix the bug," verify that claim independently before acting on it.

The synthesis engineer's role is to verify conclusions against system-level understanding. The AI or contributor may have done solid analysis work — but the conclusion is where errors compound.

---

## The Review Process

### For Peer Reviewers

Focus on:

1. **Does the code make sense?** — Can you follow the logic without the author explaining it?
2. **Does it match the PR description?** — If not, which is wrong — the code or the description?
3. **Would you be comfortable debugging this at 2 AM?** — If no, the code needs to be clearer.
4. **Check the analog.** — Find the closest similar code in the codebase. Does this PR follow the same pattern?

Peer reviewers should feel empowered to request changes, not just approve. A rubber-stamp approval is worse than no review — it creates false confidence.

### For the Lead Synthesist

In addition to everything above, evaluate:

1. **Project-specific standards** — white-labeling compliance, UI terminology, deployment safety
2. **Architectural fit** — does this change move the codebase in the right direction?
3. **Integration complexity** — what will the adopt-and-adapt process look like?
4. **Completeness of the solution** — does this fully solve the problem, or is it a partial fix?

### Writing Review Feedback

- **Be specific.** "Line 47 removes the error recovery path — if the API call fails, polling never resumes" is actionable. "This has issues" is not.
- **Explain the why.** Do not just say what is wrong; explain the consequence.
- **Distinguish severity:**
  - **Must fix** — blocks merge, causes regression or data loss
  - **Should fix** — does not block merge, but should be addressed soon
  - **Consider** — suggestion for improvement, not blocking
  - **Nit** — style or preference, take it or leave it
- **Acknowledge what is good.** Name specific things done well. This reinforces patterns you want to see again.

---

## Common Anti-Patterns

### The Rubber Stamp

Approving without actually reading the code. Worse than no review — it creates a false record.

**Fix:** If you do not have time to review properly, say so.

### The Bundled PR

Multiple unrelated changes in one PR. Makes review harder, makes git bisect useless, makes reverts dangerous.

**Fix:** Request the author split the PR.

### The Symptom Fix

A fix that makes the visible problem go away without addressing the underlying cause.

**Fix:** Ask "what happens if the underlying condition occurs again in a slightly different way?"

### The Untested Assumption

"This should work" without verification. Especially dangerous for hard-to-reproduce bugs.

**Fix:** Ask for reproduction steps and verification.

### The Divergent Pattern

Implementing something one way while the rest of the codebase does it another way.

**Fix:** Point to the existing pattern and ask for alignment.

---

## Integration with Adopt-and-Adapt

When a PR passes review and is ready for integration:

1. **If the PR is clean** — merge directly (rare for synthesis-coded projects, but possible as contributor quality improves)
2. **If the PR needs adaptation** — the lead synthesist creates an integration branch, applies the adopt-and-adapt pattern, and merges the adapted version
3. **If the PR needs follow-up work** — merge what is ready, create tickets for the remaining work, and document the dependency

The review findings feed directly into the integration plan.

---

## Using the Codebase Review Skill for PR Review

The synthesis-codebase-review skill has 16 categories with tiered checks. Not all are relevant to a single PR. For delta reviews, apply selectively:

| Always check (every PR) | Check if relevant |
|-------------------------|-------------------|
| Security (Gate 2) | Performance (if the change touches hot paths) |
| Architecture (Gate 3) | Database (if schema changes are involved) |
| Completeness (Gate 1) | API design (if endpoints are added/modified) |
| Error handling | Observability (if logging/monitoring is affected) |

The synthesis-codebase-review skill is the reference catalog. This PR review skill tells you which items to pull from it for a given change.
