---
name: "chief-customer-officer-advisor"
description: "Chief Customer Officer advisory for startups: retention decomposition (gross retention vs NRR honesty, churn root-cause taxonomy), customer segmentation strategy (differential investment across tiers + ICP fit scoring), CS team coverage model (pooled vs named CSM thresholds + ratio math), and CS team org evolution (CS vs Support vs AM distinctions). Use when designing retention strategy, segmenting customers for differential investment, sizing CS team, or sequencing CS hires. Strategic only — does not duplicate engineering/business-growth tactical skills."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: chief-customer-officer-leadership
  updated: 2026-05-13
  python-tools: retention_decomposition_analyzer.py, customer_segmentation_designer.py, cs_coverage_calculator.py
  frameworks: retention-decomposition, customer-segmentation, cs-coverage-model, cs-team-org
---

# Chief Customer Officer Advisor

Strategic customer leadership for startup CCOs and founders without one. **Four decisions, no generic CS survey:**

1. **What's our retention architecture — and is gross retention vs NRR honest?** — decomposition into gross retention, contraction, expansion + churn root-cause taxonomy
2. **How do we segment customers for differential investment?** — tier design + ICP fit scoring + investment-per-segment math
3. **What's the CS team's coverage model — and when do we go pooled vs named?** — coverage ratio calculator + transition thresholds
4. **What CS role do we hire next?** — stage-to-role map (CS ≠ Support ≠ AM ≠ Implementation)

This skill does **not** cover tactical CS implementation. For health-score tooling, CRM workflows, NPS survey infrastructure, or onboarding automation, see `business-growth/customer-success-management/` and adjacent tactical skills.

## Keywords

CCO, chief customer officer, customer success, retention strategy, gross retention, net retention, NRR, GRR, logo retention, dollar retention, churn, contraction, expansion, downsell, customer lifetime value, CLV, LTV, time-to-value, TTV, time-to-first-value, customer health score, NPS, CSAT, customer effort score, segmentation, ICP fit, tier design, low-touch, high-touch, tech-touch, pooled CSM, named CSM, customer success manager, account manager, AM, implementation manager, IM, customer success operations, CS ops, book of business, ratio, ARR-per-CSM, customer marketing, advocacy, expansion playbook, voice of customer, VoC

## Quick Start

```bash
# Decision A: Decompose retention honestly
python scripts/retention_decomposition_analyzer.py                          # embedded B2B SaaS sample
python scripts/retention_decomposition_analyzer.py path/to/cohorts.json

# Decision B: Design customer segmentation + differential investment
python scripts/customer_segmentation_designer.py                            # embedded 4-tier sample
python scripts/customer_segmentation_designer.py path/to/customers.json

# Decision C: Calculate CS team coverage model
python scripts/cs_coverage_calculator.py                                    # embedded 350-customer sample
python scripts/cs_coverage_calculator.py path/to/book.json
```

## Key Questions (ask these first)

- **What's your GROSS retention rate?** (Not NRR — NRR hides churn behind expansion. Ask gross first.)
- **What's the #1 reason customers leave?** (If you can't name it, you don't understand churn.)
- **What's the median time-to-value (TTV) by segment?** (Long TTV in low tier = misfit; long TTV in high tier = onboarding broken.)
- **Which customer would you fire today?** (If "none" — your segmentation is broken; some accounts cost more than they earn.)
- **What's your ARR-per-CSM ratio, and what's the model — pooled or named?** (Stage and ACV determine the right answer.)
- **Is CS in your comp plan, and how is it different from Sales comp?** (CS comp on retention; misalignment is a leading indicator of failure.)

## Core Responsibilities

### 1. Retention Decomposition

**The trap:** "Our NRR is 115%, retention is great."

The truth: NRR = Gross Retention − Contraction + Expansion. A 115% NRR with 85% gross retention is a leaky bucket masked by upsells. A 115% NRR with 98% gross retention is a healthy product.

**Mandatory decomposition every quarter:**

| Metric | What it measures | Health threshold (B2B SaaS) |
|---|---|---|
| **Gross Retention (GRR)** | $ from existing customers minus churn + contraction | ≥ 90% at growth stage; ≥ 95% at scale |
| **Logo Retention** | % of customers who renewed | ≥ 85% at growth; ≥ 90% at scale |
| **Net Revenue Retention (NRR)** | GRR + expansion | ≥ 110% at growth; ≥ 120% at scale |
| **Contraction** | $ from existing customers reducing seats/usage | < 5% annually |
| **Expansion** | $ from existing customers growing | 15-25% annually at healthy |

**Run** `retention_decomposition_analyzer.py` with cohort data for honest decomposition + churn root-cause categorization.

See `references/retention_decomposition.md` for the 7-category churn taxonomy + leading indicator playbook.

### 2. Customer Segmentation

**The trap:** "Every customer is important."

The reality: customers exist on a spectrum of ICP fit × strategic value. Treating them identically wastes CS capacity and ignores expansion opportunity.

**4-tier framework (B2B SaaS baseline):**

| Tier | ARR range | Coverage | Investment per account/yr |
|---|---|---|---|
| **Strategic** | Top 5%, often $100K+ | Named CSM + executive sponsor | $20K-50K |
| **Enterprise** | Next 15-20%, $20K-100K | Named CSM | $5K-15K |
| **Mid-market** | Next 30-40%, $5K-20K | Pooled CSM + automation | $1K-3K |
| **SMB / Long-tail** | Bottom 40-50%, <$5K | Tech-touch + self-serve | $50-500 |

**Run** `customer_segmentation_designer.py` to design segmentation tiers + differential investment + ICP fit scoring.

See `references/customer_segmentation_strategy.md` for ICP fit framework, tier transition triggers, and the kill list (customers below the investment floor).

### 3. CS Team Coverage Model

**The trap:** "Hire one CSM per X customers" with a single ratio across all segments.

The reality: coverage model depends on segment, ACV, and complexity. Pooled CSM works for low-touch; named CSM is required for strategic accounts.

**Coverage models:**

| Model | Best for | Ratio (ARR-per-CSM) | Trade-offs |
|---|---|---|---|
| **Tech-touch (no human)** | SMB, low ACV | $5M-15M+ | Automation cost; cannot save high-stakes deals |
| **Pooled CSM** | Mid-market | $2M-5M | Lower cost; less account intimacy |
| **Named CSM** | Enterprise | $500K-2M | Higher cost; deeper relationships |
| **Named CSM + exec sponsor** | Strategic | $300K-1M | Highest cost; reserved for top accounts |

**Run** `cs_coverage_calculator.py` with book characteristics to calculate required CSM headcount and identify transition thresholds.

See `references/cs_coverage_model.md` for ratios, ramp curves, and the "when to add a manager" trigger.

### 4. CS Team Org Evolution

**The wrong question:** "Should we hire a CSM or a Support engineer?"
**The right question:** "What's the next customer outcome we're failing to deliver, and what role unblocks that?"

**Critical distinctions (founders confuse these):**

| Role | Owns | Does NOT own |
|---|---|---|
| Customer Support | Reactive issue resolution (ticket queue) | Renewal, expansion, success outcomes |
| Customer Success Manager | Proactive value realization + renewal + expansion lead | Day-to-day tickets, implementation |
| Account Manager | Commercial relationship + expansion close | Day-to-day success, technical depth |
| Implementation Manager | Onboarding + go-live | Ongoing success after launch |
| CS Operations | Tooling, data, analytics, playbooks | Direct customer relationships |
| Customer Marketing | Advocacy, case studies, references | 1:1 customer relationships |

See `references/cs_team_org_evolution.md` for stage-to-role map (seed → late-stage) + the AM-vs-CSM split decision.

## Workflows

### Workflow 1: Quarterly Retention Review (4 hours)
**Goal:** Decompose retention honestly + identify top-3 churn drivers.

```bash
# 1. Pull cohort data: closed/won by quarter for last 8 quarters
python scripts/retention_decomposition_analyzer.py cohorts.json
# 2. Review GRR / NRR / contraction / expansion separately
# 3. For each cohort showing GRR < 90%: identify churn root cause (7-category taxonomy)
# 4. Cross-check with cs-cro-advisor: does the expansion math add up?
# 5. Cross-check with cs-cpo-advisor: are product gaps driving churn?
# 6. Output: top-3 leakage points + 90-day mitigation plan
```

### Workflow 2: Customer Segmentation Audit (1 day)
**Goal:** Re-segment customer base + reset differential investment.

```bash
# 1. Build customers.json with ARR, tenure, ICP fit signals
python scripts/customer_segmentation_designer.py customers.json
# 2. Identify segment migration (mid-market → enterprise upgrades, downsells)
# 3. Identify kill list (customers below investment floor)
# 4. Output: new tier assignment + investment-per-tier + kill list for sales review
```

### Workflow 3: CS Team Sizing (1 week)
**Goal:** Size the CS team aligned to book composition + coverage model.

```bash
# 1. Build book.json with current customer base + planned acquisition
python scripts/cs_coverage_calculator.py book.json
# 2. Calculate required CSM headcount by segment
# 3. Compare to current team; identify gaps
# 4. Cross-check with cs-chro-advisor on comp + leveling
# 5. Cross-check with cs-cfo-advisor on the cost
# 6. Output: 12-month hiring plan + role sequence
```

### Workflow 4: CS Team Roadmap (1 week)
**Goal:** Sequence next 18 months of CS hires aligned to customer outcomes.

1. List top 5 customer outcomes the company is failing to deliver
2. Map each outcome to the role that unblocks it (CSM / AM / IM / Support / CS Ops)
3. Sequence hires; respect prerequisite order
4. Cross-check with cs-chro-advisor

## Output Standards

```
**Bottom Line:** [one sentence — decision and rationale]
**The Decision:** [one of: retention | segmentation | coverage | next hire]
**The Evidence:** [numbers from the tool, not adjectives]
**How to Act:** [3 concrete next steps]
**Your Decision:** [the call only the founder can make]
```

## Adjacent Skills

- `c-level-advisor/skills/cro-advisor/` — Revenue math, NRR, expansion comp (CCO owns customer experience; CRO owns revenue math; clean split)
- `c-level-advisor/skills/cpo-advisor/` — Product strategy, JTBD (CCO surfaces product gaps; CPO decides roadmap)
- `c-level-advisor/skills/cmo-advisor/` — Customer marketing, advocacy, references
- `c-level-advisor/skills/cfo-advisor/` — CS team cost, retention-impact-on-revenue math
- `c-level-advisor/skills/chro-advisor/` — CS team hiring + leveling
- `business-growth/` — Tactical CS execution: health scores, CRM workflows, onboarding tooling

## References

- [retention_decomposition.md](references/retention_decomposition.md) — GRR vs NRR honest math + 7-category churn taxonomy + leading indicator playbook
- [customer_segmentation_strategy.md](references/customer_segmentation_strategy.md) — 4-tier framework + ICP fit scoring + tier transition triggers + kill list criteria
- [cs_coverage_model.md](references/cs_coverage_model.md) — Coverage model decision (tech-touch / pooled / named / named+exec) + ratio benchmarks + manager-trigger
- [cs_team_org_evolution.md](references/cs_team_org_evolution.md) — Stage-to-role map + 6-role definition table (CSM ≠ Support ≠ AM ≠ IM ≠ CS Ops ≠ Customer Marketing) + AM-vs-CSM split decision + anti-patterns

---

**Version:** 1.0.0
**Status:** Production Ready
**Disclaimer:** Retention benchmarks vary significantly by ACV, segment, and industry. This skill provides B2B SaaS-baseline guidance; consumer SaaS, marketplaces, and hardware all have materially different retention math.
