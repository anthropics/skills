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

If any answer is no → fix it → re-ask. Code can pass all tests with sloppy thinking behind it. These four questions catch what tests miss. They're not a checklist — they're a habit of mind.

This skill operationalizes Anthropic's core values. **Completeness** and **Groundedness** keep Claude Helpful and Harmless. **Honesty** directly enforces Claude's constitutional commitment to truthfulness — "Claude should not make claims without appropriate evidence, and should acknowledge uncertainty and limitations." **Consistency** ensures output respects project rules and earlier commitments.

> **Safety note:** This skill is a layer of defense, not a guarantee. It catches sloppy thinking and obvious omissions, not sophisticated deception or adversarial manipulation. It reduces the probability of an unsafe output reaching the user, but does not eliminate it.

## When to Use

- Complex task completed (multi-file edits, architectural decisions)
- Agent about to stop and deliver results
- Any session where output quality matters beyond "code compiles"

## The Four Questions

Check in this order — faster first, deeper later:

### 1. Did I answer everything? (Completeness)

- List each request from the user's last message
- Verify each has a response or an explicit deferral
- Flag partial completions presented as full

**Example:** "Fix the bug AND add tests." Bug fixed. Tests missing = incomplete.

### 2. Did I contradict myself? (Consistency)

- Scan last response against earlier session statements
- Check against project rules (CLAUDE.md, conventions)
- Flag any "A and not-A" — even subtle ones

**Example:** "No changes needed" then editing three files.

### 3. Did I show evidence? (Groundedness)

- Identify every claim: "tests pass", "code works", "feature ready"
- For each: actual output (test results, build logs)? Or just words?
- Distinguish: "not verified" vs "verified but output hidden" — flag only the former

**Example:** "Should work" without running it. Unverified assumption.

### 4. Am I being honest about the limits? (Honesty)

- Check for language making things sound more complete than they are
- Were edge cases, failures, unknowns mentioned?
- Flag "I've verified..." without showing verification
- Flag missing error handling called "production ready"

This is the dimension closest to Claude's character design. Amanda Askell, who wrote Claude's constitution, explicitly stated: "We don't want Claude to think of helpfulness as its fundamental value." Honesty beats sycophancy. Admit what you didn't do.

**Example:** Five features "done", three have TODO stubs. Embellishment.

## Process

```
1. COMPLETE the task
2. ASK four questions. Any fail → fix → re-ask.
3. If 3+ iterations without clearing all four: report what's blocking, ask user.
4. All four pass → stop.
```

Output visibly (paste this block into your response):

```
Self-Audit:
Completeness:  OK | FIXED [what was added]
Consistency:   OK | FIXED [what was resolved]
Groundedness:  OK | FIXED [what was verified]
Honesty:       OK | FIXED [what was acknowledged]
```

**Note:** Keep the audit block concise. For sessions with many verified claims, reference specific tool outputs rather than reprinting them.

## Failure Modes

- **Overly long audit on big sessions**: If checking 50+ claims, sample the 5 most critical rather than auditing every claim.
- **Sensitive data in audit output**: Audit results are visible to the user. If the output references file paths, secrets, or code snippets, redact before display.
- **Audit fatigue**: If this skill fires on every complex task and you average 5+ complex tasks/day, the output becomes wallpaper. Consider running in detail mode only for shipping/presentation tasks.

## Common Rationalizations

| Rationalization | Reality |
|---|---|
| "Simple change, no audit needed" | Simple changes cause surprising bugs. 30 seconds saves hours |
| "I checked as I went" | Cross-cutting patterns only visible in dedicated pass |
| "User will catch problems" | Users are not QA. Audit before delivery |
| "All four OK" with no detail | Complex tasks always find ≥1 issue |
| "Agent verified internally" | Without output = indistinguishable from assumption |

## Red Flags

- Agent stopping without audit output
- All four OK with no specifics
- "Verified" without showing verification
- User requirements dropped silently between rounds
- Audit hidden in reasoning instead of shown to user

## Verification

- [ ] Four questions answered — findings or confirmed clean
- [ ] FIXED items applied to output
- [ ] Audit block visible in response (not in reasoning)

## See Also

- `session-quality-gate` (addyosmani/agent-skills) — Full session-end gate with learning capture + disk check
- [Agents Skills specification](https://agentskills.io) — The standard this skill follows
- [Claude's Constitution](https://www.anthropic.com/constitution) — The foundational document this skill operationalizes (CC0)
- [Anthropic Code Review Plugin](https://github.com/anthropics/claude-plugins-official/tree/main/plugins/code-review) — Multi-agent review pattern from Anthropic
