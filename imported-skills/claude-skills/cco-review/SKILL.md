---
name: "cco-review"
description: "/cs:cco-review <plan> — Retention-obsessed Chief Customer Officer interrogation of any plan that touches customer retention, segmentation, CS team sizing, or CS team hiring. Use when gross retention is slipping, before approving CSM headcount, or when deciding which customer segments to keep or fire."
---

# /cs:cco-review — CCO Forcing Questions

**Command:** `/cs:cco-review <plan>`

The retention-obsessed CCO pressure-tests any plan that touches customer experience. Six questions before any retention claim, segmentation change, CS team expansion, or major CS hire.

## When to Run

- Before any board narrative that includes a retention number
- Before approving a CS team headcount expansion
- Before re-segmenting the customer base or changing tier definitions
- Before launching a customer marketing or advocacy program
- Before a major CS hire (CSM, AM, Implementation, Customer Marketing)
- When NRR is "great" but churn complaints from CSMs are increasing
- Before deciding whether to add an AM role separate from CSM

## The Six CCO Questions

### 1. What's the GROSS retention rate?
**Not NRR. Gross.** NRR can hide a leaky bucket behind expansion.
- GRR healthy ≥ 90% at growth stage, ≥ 95% at scale
- If GRR < 85% but NRR > 100%, the product is failing for 15%+ of customers; expansion is masking the failure
- Run `retention_decomposition_analyzer.py`

### 2. What's the #1 reason customers leave?
**If you can't name it, you don't understand churn.**
- 7-category taxonomy: product_fit / competitor_loss / no_value_realized / pricing / champion_left / company_event / tactical_failure
- Preventable churn = product_fit + no_value_realized + tactical_failure
- If preventable > 50%, CS has clear leverage; if < 30%, churn is structural (ICP, market, competition)

### 3. What's the median time-to-value (TTV) by segment?
**Long TTV signals different problems by segment.**
- Long TTV in low tier = ICP misfit; downgrade or kill
- Long TTV in high tier = onboarding broken; fix the Implementation Manager handoff
- TTV is a leading indicator of GRR

### 4. Which customer would you fire today?
**If "none" — your segmentation is broken.**
- Some accounts cost more than they earn (support cost > 50% of ARR + low ICP fit)
- Run `customer_segmentation_designer.py` to surface kill list
- The 3 paths for kill candidates: non-renewal / downgrade-to-tech-touch / raise-price-to-cost-recover

### 5. What's the ARR-per-CSM ratio, and is the model pooled or named?
**Wrong model wastes capacity.**
- Strategic: named + exec sponsor, $300K-$1M ARR/CSM
- Enterprise: named, $500K-$2M
- Mid-market: pooled, $2M-$5M
- SMB: tech-touch, $5M+
- Run `cs_coverage_calculator.py` to size the team

### 6. Is CS in your comp plan, and how is it different from Sales comp?
**Misalignment is the leading indicator of CS failure.**
- CS comp: 70/30 base/variable typical
- Variable: 50% gross retention + 30% net retention + 20% activity
- Anti-pattern: comp CSMs on NPS — they game it
- Anti-pattern: comp CSMs same as Sales — they sell instead of serve

## Workflow

```bash
# 1. Retention decomposition (always start here)
python ../../../skills/chief-customer-officer-advisor/scripts/retention_decomposition_analyzer.py cohorts.json

# 2. Segmentation audit
python ../../../skills/chief-customer-officer-advisor/scripts/customer_segmentation_designer.py customers.json

# 3. Coverage sizing (if making CS team changes)
python ../../../skills/chief-customer-officer-advisor/scripts/cs_coverage_calculator.py book.json
```

## Output Format

```markdown
# CCO Review: <plan>
**Date:** YYYY-MM-DD

## The Decision Being Made
[one sentence — retention | segmentation | coverage | next hire]

## Retention (if applicable)
- GRR: X% (vs vanity NRR of Y%)
- Top churn driver: <category> at X% of churn
- Preventable churn: X% (CS-controllable)
- Leaky-bucket pattern? yes/no

## Segmentation (if applicable)
- Tier distribution: Strategic X / Enterprise X / Mid-market X / SMB X
- Kill list size: N customers (X% of customers, Y% of ARR)
- Upgrade candidates: N

## Coverage (if applicable)
- Current CSMs: N | Required now: M | Required 12mo: P
- Annual cost (12mo): $X
- Manager trigger fired: yes/no

## Org (if applicable)
- Next hire: <CSM | Support | AM | IM | CS Ops | Customer Marketing>
- Why this, not the alternative: <one line>
- Customer outcome unblocked: <specific>

## Verdict
🟢 SHIP | 🟡 SHARPEN | 🔴 BLOCK

## Next Steps
[3 concrete actions]
```

## Routing

- `/cs:cpo-review` — if churn root cause is product_fit or no_value_realized
- `/cs:cro-review` — if expansion math or comp alignment is in question
- `/cs:cfo-review` — for CS cost commitments and retention-impact-on-revenue
- `cs-chro-advisor` agent — for CS hires, comp, ladder
- `/cs:decide` — log the verdict
- `/cs:freeze 30` — on multi-year CS comp plan changes

## Related

- Agent: [`cs-cco-advisor`](../../agents/cs-cco-advisor.md)
- Skill: [`chief-customer-officer-advisor`](../../../skills/chief-customer-officer-advisor/SKILL.md)
- Adjacent: `../../../../business-growth/` (tactical CS execution)

---

**Version:** 1.0.0
