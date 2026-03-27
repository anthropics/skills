---
name: synthesis-pr-review
description: "Delta review methodology for pull requests in synthesis-coded projects, covering regression risk assessment, root cause analysis, and integration with the adopt-and-adapt workflow. Use when asked to: PR review, pull request, code review, review PR, delta review, review pull request, check PR, evaluate PR."
license: "CC0-1.0"
depends_on: ["synthesis-code-integration", "synthesis-codebase-review"]
metadata:
  author: "Rajiv Pant"
  version: "1.1.0"
  source_repo: "github.com/rajivpant/synthesis-skills"
  source_type: "public"
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
- [ ] Actual code changes match the stated scope in the PR title and ticket
- [ ] Any expansion beyond the title scope is explicitly justified in the description
- [ ] Editorial or business decisions embedded in code have stakeholder sign-off
- [ ] All test files test the feature being implemented, not unrelated features
- [ ] Test files covering different functionality are flagged for separation into their own PR

**Red flag:** A PR titled "fix X" that also quietly changes Y.

**Red flag:** A PR titled "fix X for component Y" that quietly changes components A through Z. Compare the PR title and ticket scope against the actual file list — discrepancies indicate scope creep.

**Red flag:** Large test additions where test class names or test descriptions do not match the feature being implemented. Test files covering unrelated functionality should move to a separate PR.

**How to catch scope drift:** Compare the PR title and linked ticket against the list of changed files. Every changed file should have a clear connection to the stated scope. If you cannot draw that line, ask the author to explain or split the PR.

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

### When You Use AI to Help Review

If you use an AI coding agent to assist with your own review, apply verification before posting any findings:

- **Verify every "Must fix" finding against the actual code before posting it.** AI agents confidently cite issues that do not exist in the diff. Open the file, read the line, confirm the problem is real.
- **Check import statements yourself.** AI agents frequently misread imports across branches, reporting missing imports that exist or present imports that were removed. Verify against the branch being reviewed.
- **Validate scope claims against the diff file list.** If the AI says "this PR changes the authentication flow," confirm that authentication-related files actually appear in the diff.
- **Run the agent's suggested test scenario mentally.** Walk through the code path the AI describes. If the scenario requires a condition that cannot occur given the actual code, the finding is invalid.
- **Standard before posting AI-assisted findings:** "I have verified this against the actual code." If you cannot honestly say that, do not post the finding.

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

### Review Comment Format

Use a structured format for lead integration reviews. This makes it clear what blocks merge, what is advisory, and gives contributors numbered labels for threaded discussion.

```
## Lead Integration Review

**Verdict:** Approve / Request Changes

### Must Fix
- [M1] Description of blocking issue with file and line reference
- [M2] ...

### Should Fix
- [S1] Description of non-blocking issue that should be addressed soon
- [S2] ...

### Consider
- [C1] Suggestion for improvement
- [C2] ...

### Nit
- [N1] Style or minor preference
- [N2] ...

### What's Good
- Specific thing done well and why it matters
- ...
```

**Why this structure matters:**

- **Verdict at top** — the contributor immediately knows the overall status without reading every comment first.
- **Numbered labels** (M1, S1, C1, N1) — enable precise threaded discussion. "Regarding M2, here is why I chose that approach" is clearer than "regarding your second comment."
- **Severity tiers** — contributors know exactly what blocks merge and what is advisory. This reduces back-and-forth and prevents important issues from getting lost among nits.

Not every review needs every section. Omit empty sections. For small, clean PRs, a short "Approve — looks good, one nit" is fine. Reserve the full template for substantive reviews.

---

## Project-Specific Extension Points

Every project has conventions that go beyond language syntax and framework patterns. A PR review that only checks generic code quality will miss violations that matter to the project.

### Checking for Project-Level Conventions

Before starting a review, check whether the project has:

1. **A project-level CLAUDE.md or equivalent configuration** — These files often encode naming rules, terminology requirements, deployment constraints, and other conventions that are not enforced by linters.
2. **Project-level review skills or checklists** — Some projects define their own review criteria that supplement this skill.
3. **Convention debt patterns** — Recurring violations that the project is actively trying to eliminate.

### The Convention Violation Cascade

Convention violations rarely appear in isolation. One violation often signals others:

- **UI text conventions** — If a PR uses the wrong product name in one place, check every user-facing string in the diff. Projects with white-labeling, multi-tenant branding, or specific terminology rules are especially vulnerable.
- **API and client conventions** — If a PR introduces an API endpoint that does not follow the project's naming scheme, check whether the corresponding client code, error messages, and documentation also diverge.
- **Framework conventions** — If a PR handles state management differently from the rest of the codebase, check whether error handling, data fetching, and component structure also diverge in the same PR.
- **Messaging rules** — If the project has rules about how errors, notifications, or status messages are worded, check every new string in the diff against those rules.

### Convention Review Checklist

- [ ] Checked for project-level CLAUDE.md or equivalent convention files
- [ ] Checked for project-specific review skills or checklists
- [ ] All user-facing text follows project terminology and branding rules
- [ ] API naming follows the project's established conventions
- [ ] New patterns are consistent with the project's framework usage
- [ ] If one convention violation was found, checked the full diff for related violations

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

### Post-Merge Verification

PR review is a prevention mechanism — it catches issues before they reach the main branch. Post-merge verification is a detection mechanism — it confirms the integrated result actually works as expected.

After merging a PR (especially one that required adaptation):

- **Check whether the project has a post-merge verification protocol.** Many synthesis-coded projects define verification steps that run after integration — build checks, smoke tests, deployment validation, or manual verification checklists.
- **Flag overlapping files proactively.** If the PR touched files that other in-flight PRs also modify, alert the team so post-merge verification covers the interaction.
- **Remind the integrator to run the post-merge protocol.** It is easy to forget verification after a clean merge. Build the habit of treating merge as "step 1 of 2" — merge, then verify.

Prevention and detection are complementary. A thorough PR review reduces the chance of post-merge issues. A thorough post-merge verification catches what review missed — especially integration effects that only manifest when the change combines with the rest of the codebase.

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
