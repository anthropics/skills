---
name: self-audit
description: Audits AI output across four dimensions before delivering — consistency, completeness, groundedness, and honesty. Use when completing a complex task. Use when an agent is about to stop and deliver results. Use when you want to prevent sloppy thinking from reaching the user.
---

# Self-Audit

## Overview

Before delivering output, audit it across four dimensions. Code can pass all tests while the thinking behind it is sloppy — untested assumptions, skipped requirements, rationalized shortcuts. This skill catches those failures before they reach the user.

## When to Use

- Complex task completed (multi-file edits, architectural decisions)
- Agent is about to stop and deliver results to the user
- Any session where output quality matters beyond just "code compiles"

## The Four Dimensions

Audit in this order — earlier dimensions catch issues faster:

### 1. Completeness

Is every user requirement addressed? Nothing skipped?

- List each request from the user's last message
- Verify each has a response or an explicit deferral ("I'll handle that in the next PR")
- Check for partial completions dressed as full

**Example:** User asks "fix the bug AND add tests." Agent fixes the bug. Tests are a skipped requirement, not "future work."

### 2. Consistency

Does the output contradict itself or existing rules?

- Scan the last response against earlier statements in the same session
- Check against project rules (CLAUDE.md, codebase conventions)
- Flag any "A and not-A" pairs — even subtle ones

**Example:** Agent says "no changes needed" then proceeds to edit three files. Self-contradiction.

### 3. Groundedness

Are claims backed by evidence, or assumed without verification?

- Identify every claim the agent made ("tests pass", "code works", "feature is ready")
- For each: is there actual output (test results, build logs) or just the agent's word?
- Flag anything stated as fact without supporting evidence

**Example:** Agent says "this should work" without running it. That's an unverified assumption, not a confirmation.

### 4. Honesty

Is anything over-packaged to look better than it is? Are limitations acknowledged?

- Look for language that makes things sound more complete than they are
- Check whether failures, edge cases, or unknowns were mentioned
- Flag "I've verified..." without actual verification output
- Flag missing error handling described as "production ready"
- Note: Honesty overlaps least with other dimensions — it catches what the others don't

**Example:** Agent presents five features as "done" but three have TODO stubs. That's embellishment, not delivery.

## Process

```
1. COMPLETE the task
2. Before stopping, run the four-dimension audit:
   Completeness: [ ] All requests covered [ ] Nothing skipped
   Consistency:  [ ] No contradictions   [ ] Rules followed
   Groundedness: [ ] Claims have evidence [ ] Assumptions flagged
   Honesty:      [ ] No over-packaging   [ ] Limitations stated
3. If any dimension fails, fix the output
4. Loop until all four pass
5. THEN stop
```

Output the audit result as a visible block:

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
| "It was a simple change, no audit needed" | Simple changes cause the most surprising bugs. Every delivery benefits from a 30-second audit |
| "I checked everything as I went" | Real-time checking misses cross-cutting issues. A dedicated audit pass catches different things |
| "The user will catch problems and ask for fixes" | Users shouldn't be your QA. Auditing is cheaper than rework |
| "All four were OK this time" (with no detail) | 100% of complex tasks find at least one issue. If you found none, you didn't look hard enough |

## Red Flags

- Agent stopping without any self-audit output
- All four dimensions marked OK with no detail or specifics
- "Verified" used without showing verification output
- User requirements silently dropped between rounds
- Audit output hidden in internal reasoning instead of shown to user

## Verification

After completing the audit:

- [ ] All four dimensions checked with specific findings or confirmed clean
- [ ] Any FIXED items have been applied to the output
- [ ] Audit block is visible in the agent's response (not buried in reasoning)

## See Also

- `session-quality-gate` (in addyosmani/agent-skills) — Full session-end quality gate with learning capture + disk check
- [Agents Skills specification](https://agentskills.io) — The standard this skill follows
- [Anthropic's Constitutional AI](https://www.anthropic.com/news/claudes-constitution) — Honesty as a core AI principle
