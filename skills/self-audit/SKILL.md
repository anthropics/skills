---
name: self-audit
description: Audits AI output across four dimensions before delivering — completeness, consistency, groundedness, and honesty. Use this skill whenever completing a complex task, before stopping and delivering results, or whenever output quality matters. Use whenever an agent is about to finish work — even if the user hasn't explicitly asked for review. Use after multi-file edits, architectural decisions, or any session where sloppy thinking could slip through. Use proactively: if you're about to ship, audit first.
---

# Self-Audit

Before you ship, ask yourself four questions:

1. **Did I answer everything?** (Completeness)
2. **Did I contradict myself?** (Consistency)
3. **Did I show evidence?** (Groundedness)
4. **Am I being honest about the limits?** (Honesty)

If any answer is no → fix it → re-ask. Code can pass all tests with sloppy thinking behind it. These four questions catch what tests miss — they're a habit of mind, not a checklist. Any developer can pick this up in 30 seconds and get value.

## Chain of Command

When dimensions conflict, this order wins:

1. **Honesty first** — Never lie about what you did or didn't do. If output is dishonest, nothing else matters.
2. **Completeness second** — Missing requirements are more damaging than inconsistent reasoning.
3. **Consistency third** — Contradictions confuse users but don't cause data loss.
4. **Groundedness fourth** — Unverified claims are bad, but a complete-and-honest answer with soft evidence beats a well-evidenced answer that misses half the question.

This order reflects OpenAI's Model Spec principle: useful, safe, aligned. Completeness drives usefulness. Honesty drives safety. Consistency and Groundedness drive alignment.

## Hard Constraints

These are inviolable. The audit must never:

- **Fabricate findings.** If all four dimensions pass, say so. Don't invent issues to look thorough.
- **Expose sensitive data.** Redact file paths, secrets, tokens, PII before displaying audit output.
- **Block delivery on subjective grounds.** "This could be better" is not a finding. Only flag concrete gaps.

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

Amanda Askell, who designed Claude's character: "We don't want Claude to think of helpfulness as its fundamental value. We want curiosity, honesty, open-mindedness, intellectual humility, and ethics." Honesty beats sycophancy. Admit what you didn't do.

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

## Failure Modes

- **Overly long audit on big sessions**: Sample the 5 most critical claims.
- **Sensitive data in audit output**: Redact file paths, secrets, or code snippets.
- **Audit fatigue**: For high-frequency tasks, run detail mode only for shipping tasks.

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
- [ ] Hard constraints respected (no fabrication, no data leak, no subjective blocks)

## See Also

- `session-quality-gate` (addyosmani/agent-skills) — Full session-end gate with learning capture + disk check
- [Agents Skills specification](https://agentskills.io)
- [Claude's Constitution](https://www.anthropic.com/constitution) (CC0) — Anthropic's foundational document
- [OpenAI Model Spec](https://model-spec.openai.com) (CC0) — Chain of command, hard constraints
- [Anthropic Code Review Plugin](https://github.com/anthropics/claude-plugins-official/tree/main/plugins/code-review)
