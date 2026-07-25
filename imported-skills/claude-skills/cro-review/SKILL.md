---
name: "cro-review"
description: "/cs:cro-review <plan> — Pipeline-paranoid interrogation of revenue, win rate, NRR, and ramp time. Use when the forecast misses pipeline coverage, win rates drop, or before scaling the sales team."
---

# /cs:cro-review — CRO Forcing Questions

**Command:** `/cs:cro-review <plan>`

The pipeline-paranoid operator pressure-tests revenue assumptions. Six questions that surface next-quarter pain this quarter.

## When to Run

- Before committing to a quarterly revenue target
- Before changing sales motion (PLG ↔ sales-led, mid-market ↔ enterprise)
- Before hiring a batch of reps
- When pipeline coverage drops below 3x
- When NRR is trending down

## The Six CRO Questions

### 1. Pipeline Coverage
**What is pipeline coverage for the current quarter, by stage?**
- Inbound-heavy: 3x. Outbound-heavy: 4x. Below either threshold = act now.
- Stage-weighted, not just total.

### 2. Win Rate Trajectory
**What's win rate this quarter vs the last 4 — and what's the leak point?**
- Stage-by-stage conversion.
- If a single stage softens, identify why before forecasting.

### 3. NRR Decomposition
**What's gross retention, contraction, and expansion separately?**
- NRR alone hides churn.
- A 110% NRR with 95% gross retention is different from 110% with 80%.

### 4. Ramp Time
**For the last 4 hires, how many days to first deal and to quota?**
- If ramp > 90 days at growth stage, hiring profile or enablement is broken.
- Forecasted hires must build in ramp.

### 5. Discount Discipline
**What's the median discount this quarter vs last 4? Where is it creeping?**
- Discount creep is the leading indicator of pricing or positioning weakness.
- Cap discounts by approver tier.

### 6. Pipeline Source Mix
**What % of pipeline is marketing-sourced, sales-sourced, partner-sourced?**
- If one source dominates > 80%, you have concentration risk.
- Cross-check with cs-cmo-advisor.

## Workflow

```bash
python ../../../skills/cro-advisor/scripts/revenue_forecast_model.py
python ../../../skills/cro-advisor/scripts/churn_analyzer.py
```

## Output Format

```markdown
# CRO Review: <plan>
**Date:** YYYY-MM-DD

## Pipeline
- Coverage: X.Xx (target 3x+)
- Win rate: X% (4Q trend: ↑ / → / ↓)
- Top leaking stage: <name>

## Retention
- Gross retention: X%
- NRR: X%
- Expansion: X%
- Contraction: X%

## Ramp
- New hires last quarter: N
- Median days to first deal: X
- Median days to quota: X

## Discount
- Median discount this quarter: X%
- Trend vs 4Q ago: <delta>

## Source Mix
- Marketing: X% | Sales: X% | Partner: X%

## Verdict
🟢 ON PLAN | 🟡 GAP | 🔴 PIPELINE CRISIS

## Next Steps
[3 concrete actions]
```

## Routing

- `/cs:cfo-review` — does this hit the cash plan?
- `/cs:cmo-review` — is pipeline source-mix healthy?
- `/cs:execute` — quarterly plan if GREEN
- `/cs:boardroom` — if RED

## Related

- Agent: [`cs-cro-advisor`](../../agents/cs-cro-advisor.md)
- Skill: [`cro-advisor`](../../../skills/cro-advisor/SKILL.md)
- Execution: `../../../../business-growth/`

---

**Version:** 1.0.0
