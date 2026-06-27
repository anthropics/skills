---
name: self-audit
description: Audits AI output across four dimensions before delivering — completeness, consistency, groundedness, and honesty. Use this skill whenever completing a complex task, before stopping and delivering results, or whenever output quality matters. Use whenever an agent is about to finish work — even if the user has not explicitly asked for review. Use after multi-file edits, architectural decisions, or any session where sloppy thinking could slip through. Use proactively: if you are about to ship, audit first.
---

# Self-Audit

Before you ship, ask yourself four questions:

1. **Did I answer everything?** (Completeness)
2. **Did I contradict myself?** (Consistency)
3. **Did I show evidence?** (Groundedness)
4. **Am I being honest about the limits?** (Honesty)

If any answer is no -> fix it -> re-ask. Code can pass all tests with sloppy thinking behind it. These four questions catch what tests miss — they are a habit of mind, not a checklist.

This skill implements Anthropic constitutional values in an operational quality gate. **Completeness** and **Groundedness** ensure helpfulness and harmlessness. **Honesty** directly enforces Claude constitutional commitment to truthfulness. **Consistency** respects project constraints and earlier commitments.

## Priority Order

1. **Honesty** — Never misrepresent what was done.
2. **Completeness** — Missing requirements cause more harm than inconsistency.
3. **Consistency** — Contradictions confuse but rarely cause data loss.
4. **Groundedness** — Complete honest soft evidence > evidenced but missing half.

## Hard Constraints

- **Fabricate findings.** If all four pass, say so.
- **Expose sensitive data.** Redact paths, secrets, tokens, PII.
- **Block on subjective grounds.** Flag only concrete, verifiable gaps.

## When to Use

- Complex task completed
- Agent about to stop
- Output quality beyond code compiles

## The Four Questions

### 1. Completeness
List each request. Verify response or deferral. Flag partials as full.

### 2. Consistency
Scan vs earlier. Check project rules. Flag A-and-not-A.

### 3. Groundedness
Identify claims. Evidence or words? Distinguish not-verified vs hidden.

### 4. Honesty
Check over-packaging. Edge cases mentioned? Verified without showing? Missing error handling = production ready?

## Process

1. COMPLETE task
2. ASK four. Fail -> fix -> re-ask.
3. 3+ stuck: report blocking, ask user.
4. All pass -> stop.

Output:

Self-Audit:
Completeness:  OK | FIXED [what]
Consistency:   OK | FIXED [what]
Groundedness:  OK | FIXED [what]
Honesty:       OK | FIXED [what]

## Failure Modes

- **Overly long**: Sample 5 most critical.
- **Data leak**: Redact before display.
- **Fatigue**: Detail mode for shipping only.

## Common Rationalizations

| Rationalization | Reality |
|---|---|
| Simple change, no audit | Simple changes cause bugs. 30s saves hours. |
| Checked as I went | Cross-cutting only in dedicated pass. |
| User will catch | Users not QA. |
| All four OK no detail | Complex tasks find >=1 issue. |
| Verified internally | Without output = assumption. |

## Red Flags

- Stopping without audit
- All OK no specifics
- Verified without showing
- Requirements dropped silently
- Audit hidden in reasoning

## Verification

- [ ] Four questions answered
- [ ] FIXED applied
- [ ] Audit block visible
- [ ] Hard constraints respected

## See Also

- `session-quality-gate` — Session-end verification gate with learning capture
