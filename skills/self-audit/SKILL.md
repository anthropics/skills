---
name: self-audit
description: Audits AI output across four dimensions before delivering — completeness, consistency, groundedness, and honesty. Use when completing a complex task. Use when an agent is about to stop and deliver results. Use when you want to prevent sloppy thinking from reaching the user.
---

# Self-Audit

Before you ship, ask yourself four questions:

1. **Did I answer everything?** (Completeness)
2. **Did I contradict myself?** (Consistency)
3. **Did I show evidence?** (Groundedness)
4. **Am I being honest about the limits?** (Honesty)

Code can pass all tests with sloppy thinking behind it. These four questions catch what tests miss.

## When to Use

- Complex task completed (multi-file edits, architectural decisions)
- Agent about to stop and deliver results
- Any session where output quality matters beyond "code compiles"

## The Four Questions

Check in this order — earlier questions are faster and catch issues that make later ones unnecessary:

### 1. Did I answer everything? (Completeness)

- List each request from the user's last message
- Verify each has a response or an explicit deferral
- Flag partial completions presented as full

**Example:** "Fix the bug AND add tests." Bug fixed. Tests missing. That's incomplete, not "future work."

### 2. Did I contradict myself? (Consistency)

- Scan last response against earlier statements in the session
- Check against project rules (CLAUDE.md, codebase conventions)
- Flag any "A and not-A" — even subtle ones

**Example:** "No changes needed" then editing three files. Self-contradiction.

### 3. Did I show evidence? (Groundedness)

- Identify every claim: "tests pass", "code works", "feature is ready"
- For each: is there actual output (test results, build logs)? Or just words?
- Distinguish: "not verified" vs "verified but output hidden" — only flag the former

**Example:** "This should work" without running it. Unverified assumption.

### 4. Am I being honest about the limits? (Honesty)

- Look for language that makes things sound more complete than they are
- Check: were edge cases, failures, unknowns mentioned?
- Flag "I've verified..." without showing verification
- Flag missing error handling called "production ready"

**Example:** Five features "done" but three have TODO stubs. Embellishment.

## Process

```
1. COMPLETE the task
2. ASK four questions. Any fail → fix → re-ask.
3. If 3+ iterations without clearing, report what's blocking and ask the user.
4. All four pass → stop.
```

Output visibly:

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
| "Simple change, no audit needed" | Simple changes cause surprising bugs. 30 seconds saves hours |
| "I checked as I went" | Cross-cutting patterns only visible in dedicated pass |
| "User will catch problems" | Users are not QA. Audit before delivery |
| "All four OK" with no detail | Complex tasks always find ≥1 issue. Look harder |
| "Agent verified internally" | Internal verification without output = indistinguishable from assumption |

## Red Flags

- Agent stopping without audit output
- All four OK with no specifics
- "Verified" without showing verification
- User requirements dropped silently between rounds
- Audit hidden in reasoning instead of shown to user
- Tool-call evidence not cited in audit

## Verification

- [ ] Four questions answered with findings or confirmed clean
- [ ] FIXED items applied to output
- [ ] Audit block visible in response

## See Also

- `session-quality-gate` (addyosmani/agent-skills) — Full session-end gate with learning capture + disk check
- [Agents Skills specification](https://agentskills.io)
- [Anthropic's Constitutional AI](https://www.anthropic.com/news/claudes-constitution) — Honesty as a core AI principle
