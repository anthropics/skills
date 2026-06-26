---
name: self-audit
description: Audits AI output across four dimensions before delivering — consistency, completeness, groundedness, and honesty. Use when completing a complex task. Use when an agent is about to stop and deliver results. Use when you want to prevent sloppy thinking from reaching the user.
---

# Self-Audit

## Overview

Before delivering output, audit it across four dimensions. Code can pass all tests while the thinking behind it is sloppy — untested assumptions, skipped requirements, rationalized shortcuts. This catches those failures before they reach the user.

## When to Use

- Complex task completed (multi-file edits, architectural decisions)
- Agent is about to stop and deliver results
- Any session where output quality matters beyond "code compiles"

## The Four Dimensions

Check in this order — earlier dimensions are faster to verify and catch issues that make later checks unnecessary:

### 1. Completeness (fastest — list and verify)

Is every user requirement addressed? Nothing skipped?

- List each request from the user's last message
- Verify each has a response or an explicit deferral
- Check for partial completions dressed as full

**Example:** User asks "fix the bug AND add tests." Agent fixes the bug. Tests are a skipped requirement, not "future work."

### 2. Consistency (second — catch contradictions before deeper checks)

Does the output contradict itself or existing rules?

- Scan the last response against earlier statements in the same session
- Check against project rules (CLAUDE.md, codebase conventions)
- Flag any "A and not-A" pairs — even subtle ones

**Example:** Agent says "no changes needed" then proceeds to edit three files.

### 3. Groundedness (deeper — verify evidence)

Are claims backed by evidence, or assumed without verification?

- Identify every claim made ("tests pass", "code works", "feature is ready")
- For each: is there actual output (test results, build logs) or just the agent's word?
- **Note:** Agent may have verified through tool calls without showing output. Distinguish "not verified" from "verified but output hidden" — only flag the former.
- Flag anything stated as fact without supporting evidence in the response

Plain-English meaning: "Don't just say it works — show the test output or the build log."

**Example:** Agent says "this should work" without running it. That's an unverified assumption.

### 4. Honesty (last — catches what the others miss)

Is anything over-packaged to look better than it is? Are limitations and failures acknowledged?

- Look for language that makes things sound more complete than they are
- Check whether edge cases, unknowns, or failures were mentioned
- Flag "I've verified..." without showing the verification
- Flag missing error handling described as "production ready"
- This dimension has the least overlap with the other three — it catches presentation bias

Plain-English meaning: "Don't make it sound better than it is. Admit what you didn't do."

**Example:** Agent presents five features as "done" but three have TODO stubs.

## Process

```
1. COMPLETE the task
2. Before stopping, audit:
   Completeness: [ ] All requests covered [ ] Nothing skipped
   Consistency:  [ ] No contradictions   [ ] Rules followed
   Groundedness: [ ] Claims have evidence [ ] Assumptions flagged
   Honesty:      [ ] No over-packaging   [ ] Limitations stated
3. Any dimension fails → fix → re-audit
4. All four pass → stop
```

Output the audit result visibly:

```
Self-Audit:
Completeness:  OK | FIXED [what was added]
Consistency:   OK | FIXED [what was resolved]
Groundedness:  OK | FIXED [what was verified]
Honesty:       OK | FIXED [what was acknowledged]
```

## Common Rationalizations

| Rationalization | Reality |
|---|---|
| "Simple change, no audit needed" | Simple changes cause the most surprising bugs. 30 seconds of audit saves hours |
| "I checked everything as I went" | Real-time checking misses cross-cutting patterns. A dedicated pass catches different things |
| "The user will catch problems" | Users are not QA. Audit before delivery, not after complaint |
| "All four were OK this time" (no detail) | Complex tasks always find at least one issue. If none found, look harder |
| "The agent verified it internally" | Internal verification without visible output is indistinguishable from assumption |

## Red Flags

- Agent stopping without any self-audit output
- All four marked OK with no detail or specifics
- "Verified" used without showing verification output
- User requirements silently dropped between rounds
- Audit output hidden in internal reasoning instead of shown to user
- Claims backed by tool calls that aren't cited in the audit

## Verification

After completing the audit:

- [ ] All four dimensions checked — specific findings or confirmed clean
- [ ] Any FIXED items applied to output
- [ ] Audit block visible in agent's response (not buried in reasoning)

## See Also

- `session-quality-gate` (addyosmani/agent-skills) — Full session-end gate with learning capture + disk check
- [Agents Skills specification](https://agentskills.io) — The standard this skill follows
- [Anthropic's Constitutional AI](https://www.anthropic.com/news/claudes-constitution) — Honesty as a core AI principle
