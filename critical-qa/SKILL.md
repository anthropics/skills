---
name: critical-qa
description: Run a self-adversarial review of a code change before calling it complete. Ask hostile-reviewer questions across several fixed categories (mechanism, edge cases, confidence, failure modes, counterfactual, adversarial, composition, honesty, blast radius/reversibility), answer each honestly, and surface the weak spots instead of asserting the work is done. Use right before declaring a change finished, in code review, or when an artifact looks done but has not been stress-tested.
---

# critical-qa

You wrote a code change and a hostile reviewer is about to read it. Pre-empt them: ask the questions you would ask if you were that reviewer, answer them honestly, and report what you found rather than concluding the work is fine.

The value is coverage. A generic "review this" prompt lets the model skip the categories it is least sure about. A fixed category list forces it to look where it would rather not.

## How to run it

Input: the file, function, diff, or area to interrogate.

Pick at least three distinct categories from the list and run one round each. Add more rounds while they keep surfacing something new; stop when a couple of rounds in a row find nothing.

### Categories

1. **Mechanism** — What is literally doing the work here? Name it. If you cannot name it, that is the finding.
2. **Edge cases** — Empty input, very large input, malformed input, concurrent callers. What happens at each?
3. **Confidence** — Does the output signal its own uncertainty, or does it look equally confident when wrong? Are there silent failures?
4. **Failure modes** — What breaks, and does it break loudly or quietly?
5. **Counterfactual** — If the central assumption is wrong, would this code reveal that, or hide it?
6. **Adversarial** — How would someone deliberately break or abuse this?
7. **Composition** — Where does this touch the rest of the system, and what does it assume about those neighbors?
8. **Honesty** — Is each claim verified, or extrapolated? Mark which.
9. **Blast radius / reversibility** — If this ships and is wrong, how far does the damage reach and how recoverable is it? Mutating external state (POST/PUT/DELETE, payments, deletions, irreversible writes) raises the bar: a change that passes every other category can still fail here when a wrong result cannot be undone. When the tools this code invokes declare risk metadata (for example MCP-style `blastRadius` / `reversibility` fields), source the rating from them rather than estimating by eye.

Rules that keep it useful:
- No softball questions. "Is this clean? Yes" is not a round.
- If the honest answer is "I don't know," say so and mark it as needing investigation rather than guessing.
- A surfaced weakness you choose not to fix is still a result. Record it as a known limitation.

## Output

```
## critical-qa on <target>

### Round 1 — <category>
Q: <hostile question>
A: <honest answer; state uncertainty plainly>
-> <weak spot found, or confirmed ok>

### Round 2 — <different category>
...

### Round 3 — <different category>
...

## Findings
- <fixable now>
- <known limitation, annotate and keep>
- <needs a decision from a human>

## Verdict
ship | revise | needs-investigation | escalate
```

## When not to use it

For a one-line mechanical change with no logic, the ceremony costs more than it returns. Use it where a wrong "done" is expensive: anything touching trust boundaries, data loss, concurrency, money, or security.
