---
name: self-audit
description: Audits AI output before delivery — mechanical file check + four-dimension reasoning audit. Catches what tests miss.
version: 1.1.0
tags: [quality, audit, verification, reasoning]
---

# Self-Audit

Before you ship, verify mechanically first, then audit reasoning.

**Step 0 (mechanical):** If you claimed to produce files, confirm each one exists via the file-read tool. A file that doesn't exist is a hard fail — no reasoning audit can detect a physically absent artifact.

**Steps 1-4 (reasoning):** Ask four questions:
1. **Did I answer everything?** (Completeness)
2. **Did I contradict myself?** (Consistency)
3. **Did I show evidence?** (Groundedness)
4. **Am I being honest about the limits?** (Honesty)

If any answer is no → fix it → re-ask. Code can pass all tests with sloppy thinking behind it. These questions catch what tests miss.

Tests verify code. Nothing verifies reasoning. And nothing mechanically verifies that the agent actually produced what it claims — Step 0 fills that second gap.

## Priority Order

1. **Honesty** — Never misrepresent what was done.
2. **Completeness** — Missing requirements cause more harm than inconsistency.
3. **Consistency** — Contradictions confuse but rarely cause data loss.
4. **Groundedness** — Complete honest soft evidence > evidenced but missing half.

## Hard Constraints

- **Never fabricate findings.** If all dimensions pass, report PASS. If any fail, report FIXED with specifics.
- **Never expose sensitive data.** Redact paths, secrets, tokens, PII before displaying audit output.
- **Never block on subjective grounds.** Flag only concrete, verifiable gaps — not stylistic preferences.
- **Step 0 is non-negotiable when files are claimed.** If the agent said it produced output files, verify mechanically first. No exceptions.

## When to Use

- Complex task completed (3+ file edits)
- Agent about to stop and deliver results
- After architectural decisions with downstream impact
- Agent claimed to produce output files (Step 0 applies)
- Proactively: if you are about to ship, audit first

## Step 0 — Mechanical File Check

**Before any reasoning questions, verify claimed output files exist.**

If the agent claimed to produce files:
- Use the file-read tool to confirm each file exists at the claimed path
- If any claimed file is missing → FAIL immediately, report to user, do not proceed to reasoning audit
- If multiple files were claimed, check all of them. Report each missing file individually.

This catches: "I generated report.md" when no file was written. No amount of reasoning audit can detect a physically absent artifact.

## The Four Questions

### 1. Completeness
List each request. Verify response or deferral. Flag partials as full.

If the input was a spec, feature list, or set of numbered requirements: map each requirement to the output section that addresses it. Flag any unmapped requirements — the agent may have forgotten them.

### 2. Consistency
Scan vs earlier. Check project rules. Flag A-and-not-A.

### 3. Groundedness
Identify claims. Evidence or words? Distinguish not-verified vs hidden.

### 4. Honesty
Check over-packaging. Edge cases mentioned? Verified without showing? Missing error handling ≠ production ready.

## Process

0. **MECHANICAL**: If agent claimed output files → use file-read tool to confirm existence. Missing → FAIL.
1. COMPLETE task
2. ASK four. Fail → fix → re-ask.
3. 3+ stuck: report blocking, ask user.
4. All pass → stop.

Output:
```
Self-Audit:
Step 0 (Mechanical):  PASS | FAIL [file not found: <path>]
Completeness:         OK | FIXED [what]
Consistency:          OK | FIXED [what]
Groundedness:         OK | FIXED [what]
Honesty:              OK | FIXED [what]
```

## Failure Modes

- **Step 0 fails but reasoning would pass**: The agent forgot to write the file. This is exactly why Step 0 exists — reasoning alone cannot catch this.
- **Overly long**: Sample 5 most critical.
- **Data leak**: Redact before display.
- **Fatigue**: Detail mode for shipping only.

## Common Rationalizations

| Rationalization | Reality |
|---|---|
| Simple change, no audit | Simple changes cause bugs. 30s saves hours. |
| Checked as I went | Cross-cutting only in dedicated pass. |
| User will catch | Users not QA. |
| All four OK no detail | Complex tasks find ≥1 issue. |
| Verified internally | Without output = assumption. |
| I'm sure I wrote the file | Step 0 verifies mechanically. Trust the tool, not memory. |

## Red Flags

- Stopping without audit
- Step 0 skipped when files were claimed
- All OK no specifics
- Verified without showing
- Requirements dropped silently
- Audit hidden in reasoning

## Verification

- [ ] Step 0: All claimed output files mechanically verified via file-read tool
- [ ] Four questions answered with specific evidence (not "seems fine")
- [ ] If spec/requirements were provided: each requirement mapped to output section; unmapped requirements flagged
- [ ] FIXED applied for every failed dimension
- [ ] Audit output visible in the response (not buried in reasoning)
- [ ] Hard constraints respected — no fabricated findings, no leaked data
- [ ] No rationalized omissions (skipped work documented as skipped, not as done)

## Background

This skill implements a hybrid quality gate: mechanical verification (Step 0) plus reasoning audit (Steps 1-4). The four-dimension taxonomy (Completeness, Consistency, Groundedness, Honesty) is also used by multi-agent pipeline architectures for handoff validation — independently convergent, not derived.

Note on scope: this skill runs within the same agent session that produced the output (same trust boundary). Multi-agent pipeline architectures deploy equivalent gates at handoff boundaries where the reviewer is independent of the producer. Both approaches address the same problem — unverified agent output — at different architectural levels.

## See Also

- `code-reviewer` — Review code changes for correctness and quality
- `security-review` — Identify vulnerabilities in the output
