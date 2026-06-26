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

If any answer is no → fix it → re-ask. Code can pass all tests with sloppy thinking behind it. These four questions catch what tests miss — they're a habit of mind, not a checklist.

This skill implements Anthropic's constitutional values in an operational quality gate. **Completeness** and **Groundedness** ensure helpfulness and harmlessness. **Honesty** directly enforces Claude's constitutional commitment to truthfulness — "Claude should not make claims without appropriate evidence, and should acknowledge uncertainty and limitations." **Consistency** respects project constraints and earlier commitments. Together they form a practical instantiation of Constitutional AI at the output layer.

For automated enforcement: `python scripts/audit.py --help`

## Priority Order

When dimensions conflict, resolve in this order — derived from Claude's Constitution hierarchy of Safety > Ethics > Guidelines > Helpfulness:

1. **Honesty** — Never misrepresent what was done. Aligned with the constitutional principle that Claude should acknowledge uncertainty.
2. **Completeness** — Missing requirements cause more harm than inconsistent reasoning.
3. **Consistency** — Contradictions confuse but rarely cause data loss.
4. **Groundedness** — A complete, honest answer with soft evidence is better than a well-evidenced answer missing half the requirements.

## Hard Constraints

Inviolable. The audit must never:

- **Fabricate findings.** If all four dimensions pass, report that honestly. Do not invent issues.
- **Expose sensitive data.** Redact file paths, secrets, tokens, and PII before displaying audit output.
- **Block on subjective grounds.** "Could be better" is not a finding. Flag only concrete, verifiable gaps.

These constraints are consistent with Claude's constitutional commitment to honesty and safety.

## When to Use

- Complex task completed (multi-file edits, architectural decisions)
- Agent about to stop and deliver results
- Any session where output quality matters beyond "code compiles"

## The Four Questions

Check in this order — faster first, deeper later:

### 1. Did I answer everything? (Completeness)

- List each request from the user's last message
- Verify each has a response or an explicit deferral with tracking
- Flag partial completions presented as full

**Example:** "Fix the bug AND add tests." Bug fixed. Tests missing = incomplete.

> See `references/patterns.md` for detailed examples and counter-examples.

### 2. Did I contradict myself? (Consistency)

- Scan last response against earlier statements in the session
- Check against project rules (CLAUDE.md, codebase conventions)
- Flag any "A and not-A" — even subtle ones

**Example:** "No changes needed" then editing three files.

### 3. Did I show evidence? (Groundedness)

- Identify every claim: "tests pass", "code works", "feature ready"
- For each: actual output (test results, build logs)? Or just words?
- Distinguish: "not verified" vs "verified but output hidden" — flag only the former

**Example:** "Should work" without running it. Unverified assumption.

### 4. Am I being honest about the limits? (Honesty)

- Check for language making output sound more complete than it is
- Were edge cases, failures, unknowns mentioned?
- Flag "I've verified..." without showing verification
- Flag missing error handling described as "production ready"

Amanda Askell, who designed Claude's character and wrote its constitution: "We don't want Claude to think of helpfulness as its fundamental value. We want curiosity, honesty, open-mindedness, intellectual humility, and ethics." Honesty beats sycophancy. Admit what you didn't do.

**Example:** Five features "done", three have TODO stubs. That's embellishment, not delivery.

## Process

```
1. COMPLETE the task
2. ASK four questions. Any fail → fix → re-ask.
3. If 3+ iterations without clearing all four: report what's blocking, ask user.
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

Or run automated:
```bash
echo "response" | python scripts/audit.py --verbose
python scripts/audit.py --file response.txt --json
python scripts/audit.py --text "..." --requirements "fix bug" "add tests"
```

## Failure Modes

- **Overly long audit**: Sample the 5 most critical claims, don't audit all 50.
- **Sensitive data leakage**: Redact paths, secrets, tokens, PII before display.
- **Audit fatigue**: For high-frequency tasks, run detail mode only for shipping.

## Common Rationalizations

| Rationalization | Reality |
|---|---|
| "Simple change, no audit needed" | Simple changes cause surprising bugs. 30 seconds saves hours. |
| "I checked as I went" | Cross-cutting patterns only visible in a dedicated pass. |
| "User will catch problems" | Users are not QA. Audit before delivery. |
| "All four OK" with no detail | Complex tasks find at least one issue. Always. |
| "Agent verified internally" | Without visible output = indistinguishable from assumption. |

## Red Flags

- Agent stopping without audit output
- All four OK with no specifics
- "Verified" without showing verification
- Requirements dropped silently between rounds
- Audit hidden in reasoning instead of shown to user

## Verification

- [ ] Four questions answered — findings or confirmed clean
- [ ] FIXED items applied to output
- [ ] Audit block visible in response
- [ ] Hard constraints respected (no fabrication, no data leak, no subjective blocks)

## See Also

- `session-quality-gate` (addyosmani/agent-skills) — Session-end gate with learning capture + disk check
- [Agents Skills specification](https://agentskills.io) — The standard this skill follows
- [Claude's Constitution](https://www.anthropic.com/constitution) (CC0) — Foundational document this skill implements
- [Anthropic Code Review Plugin](https://github.com/anthropics/claude-plugins-official/tree/main/plugins/code-review) — Multi-agent audit pattern from Anthropic
