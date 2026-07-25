---
name: "freeze"
description: "/cs:freeze <decision> <days> — Lock a strategic decision for a cooldown period to prevent impulse reversal. Mirrors gstack's safety primitives for the business layer. Use when an irreversible decision was made under pressure — e.g. a layoff plan or multi-year contract — and deserves a cooling-off lock before execution."
---

# /cs:freeze — Cooldown Lock on a Decision

**Command:** `/cs:freeze <decision-path> <days>`

Locks a decision for a defined cooldown period. During the freeze, the chief-of-staff router refuses to re-litigate the decision unless a kill criterion explicitly triggers.

Inspired by gstack's `/freeze` and `/guard` safety primitives — adapted from code-scoping to strategic-scoping.

## When to Use

Founders are pattern-matchers; pattern-matching after a tough decision often produces a reversal that's actually just decision fatigue. The freeze enforces a discipline:

- After any **irreversible** or **high-cost-to-reverse** decision (fundraise, layoff, market entry)
- After a **split-vote boardroom** (preserve the call against second-guessing)
- After a **founder gut-feel** override of unanimous advisor consensus (let it run)
- During a **personnel transition** (lock the strategy so the new exec can execute, not redebate)

## Default Freeze Periods

| Decision type | Default freeze |
|---|---|
| Fundraise round size / lead choice | 30 days |
| Pricing change | 60 days |
| Market entry / exit | 90 days |
| Layoff / RIF | 30 days |
| Strategic pivot | 90 days |
| Personnel (exec hire / fire) | 60 days |
| M&A LOI | 30 days |
| Custom | specify in command |

## Workflow

1. Read the decision record
2. Validate it has APPROVED status
3. Apply freeze: write `freeze_until: YYYY-MM-DD` to the decision record
4. Add to active-freezes index at `~/.claude/freezes/active.md`
5. cs-chief-of-staff router now refuses to re-route this topic to the boardroom until:
   - The freeze period expires, OR
   - A kill criterion explicitly triggers

## Output

The decision record is updated in place:

```markdown
# Decision: <title>
...
**Status:** FROZEN
**Frozen until:** YYYY-MM-DD
**Reason for freeze:** <text>
**Override condition:** Kill criterion <name> triggers OR founder issues `/cs:unfreeze` with stated reason
```

The active-freezes index is updated:

```markdown
# Active Freezes
**Updated:** YYYY-MM-DD

| Decision | Frozen until | Override condition |
|---|---|---|
| <decision title> | YYYY-MM-DD | <kill criterion or /cs:unfreeze> |
```

## Override

To unfreeze before the period ends, the founder runs:

```
/cs:unfreeze <decision> <reason>
```

The unfreeze is logged in the decision history (preserved permanently). Forced overrides create a paper trail that surfaces at post-mortem.

## Auto-Override

If a kill criterion in the decision triggers, the freeze auto-releases and the chief-of-staff routes immediately to `/cs:post-mortem`. The freeze does not protect against reality; it protects against impulse.

## Why This Beats "Just Don't Re-Decide"

Founders have authority. Without an explicit lock + log, every wobble produces a "let's discuss this again" — which is exhausting for advisors and erodes the value of the boardroom. The freeze is **a process**, not a rule; it logs every override so the post-mortem can audit founder discipline.

## Routing

- `/cs:unfreeze` — explicit early release
- `/cs:post-mortem` — auto-triggered if kill criterion fires
- `/cs:boardroom` — blocked until unfreeze or expiry

## Related

- Skill: [`decision-logger`](../../../skills/decision-logger/SKILL.md)
- Agent: [`cs-chief-of-staff`](../../agents/cs-chief-of-staff.md) — enforces freezes in routing

---

**Version:** 1.0.0
