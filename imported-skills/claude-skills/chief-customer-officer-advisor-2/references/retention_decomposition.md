# Retention Decomposition — The Decision: "Is our retention number honest?"

This reference answers exactly one decision: **what does our retention number actually mean, and where is the leakage?**

Pair with `scripts/retention_decomposition_analyzer.py` for automation.

## The Vanity Trap

> "Our NRR is 115%, retention is great."

Wrong question. NRR can hide a leaky bucket: 85% gross retention + 30% expansion from existing customers = 115% NRR. The product is failing for 15% of paying customers; expansion from the survivors is masking the failure.

**Always decompose:**

```
NRR = Gross Retention (GRR) − Contraction + Expansion
```

If GRR < 85% but NRR > 100%, you have a **leaky bucket**. Acquisition spend keeps the metric up; eventually expansion can't outrun churn.

## The Honest Metrics

### Gross Revenue Retention (GRR)
**Definition:** Of the ARR that existed at the start of period N, how much remains at the end of period N+1, NOT counting expansion?

**Formula:** `GRR = (starting_arr - churn_arr - contraction_arr) / starting_arr`

**Thresholds (B2B SaaS baseline):**

| Stage | Healthy | Concerning | Critical |
|---|---|---|---|
| Seed / Series A | ≥ 85% | 75-85% | < 75% |
| Series B / Growth | ≥ 90% | 85-90% | < 85% |
| Late-stage / Scale | ≥ 95% | 90-95% | < 90% |

**This is the truth metric.** Without it, you cannot diagnose product-market fit problems.

### Net Revenue Retention (NRR)
**Definition:** GRR plus expansion from existing customers.

**Formula:** `NRR = GRR + (expansion_arr / starting_arr)`

**Thresholds:**

| Stage | Healthy | Concerning | Critical |
|---|---|---|---|
| Seed / Series A | ≥ 100% | 95-100% | < 95% |
| Series B / Growth | ≥ 110% | 100-110% | < 100% |
| Late-stage / Scale | ≥ 120% | 110-120% | < 110% |

**This is the vanity metric in isolation.** Useful only when reported alongside GRR.

### Logo Retention
**Definition:** % of customers (count, not dollars) who renewed.

**Why it matters separately:** dollar retention can stay healthy if you lose lots of small customers and retain big ones. Logo retention exposes whether you're losing the long tail.

**Thresholds:** typically tracks GRR within 3-5 percentage points.

## The 7-Category Churn Taxonomy

Every churned customer falls into one of these categories. Tracking the distribution tells you what to fix.

| Category | Definition | Preventable? | Fix |
|---|---|---|---|
| **product_fit** | Product didn't solve the customer's actual JTBD | Mostly yes (long term) | Sharpen ICP, fix onboarding mismatch, OR accept and price-segment out |
| **competitor_loss** | Lost to a competitor with better fit / price | Partially | Competitive intelligence, product differentiation, pricing review |
| **no_value_realized** | Customer never reached time-to-value; onboarding gap | Yes | Onboarding redesign, milestone tracking, intervention triggers |
| **pricing** | Price-driven churn (too expensive, or perceived as low value) | Sometimes | Price-value re-audit; segmentation; downsell offers vs churn |
| **champion_left** | Internal champion changed roles or left the customer company | Partially | Multi-threading: avoid single-champion dependency |
| **company_event** | M&A, layoffs, shutdown — not your fault | No | Track frequency; if high, your ICP may be unstable |
| **tactical_failure** | Service / support failure — preventable with better CS execution | Yes (always) | CS playbook gaps, response time, escalation paths |

**Preventable churn = product_fit + no_value_realized + tactical_failure.** If preventable churn > 50% of total, your CS function has clear leverage. Below 30%, churn is mostly structural (ICP, market, competitors).

## Leading Indicators (catch churn before it happens)

By the time a customer cancels, you're 60-90 days late. Leading indicators give 30-90 days warning.

**Product engagement signals:**
- Drop in daily active users (DAU) per account (week-over-week trend)
- Drop in "depth of use" — features touched per session
- Drop in API calls (for technical products)
- No login from any user in account for 14+ days

**Commercial signals:**
- Failed payment / payment delay
- Reduction in seat count (often precedes contraction or full churn)
- Champion stops responding to QBR scheduling
- Account team reassignment on customer's side

**Sentiment signals:**
- NPS / CSAT drop > 2 points
- Support ticket volume spike (paradoxically — high engagement, not low)
- Negative sentiment in support tickets (manual or NLP-tagged)
- Public review or social media complaint

**Action:** Build a health score using 3-5 of these. When score crosses threshold, CSM intervention triggers.

## Cohort Analysis: Mandatory Discipline

Pull retention by **acquisition cohort** (quarter or month), not by reporting period. Reporting-period retention mixes cohorts and hides which acquisition vintage is leaky.

**Pattern to watch:**

- Cohort GRR **improves over time** = product quality improving, onboarding maturing
- Cohort GRR **flat** = stable product, no quality regression but no improvement
- Cohort GRR **degrading** = recent cohorts churning faster than older ones → quality regression, ICP drift, or wrong customer acquisition

The third pattern is a critical signal. Acquire less, fix product, or both.

## NPS / CSAT — Use Carefully

NPS is a directional indicator, not a precise measurement. Useful for:
- Trends quarter-over-quarter
- Comparison across segments (e.g., enterprise NPS vs SMB NPS)
- Specific transactional moments (post-onboarding, post-renewal)

NOT useful for:
- Benchmarking against other companies (calculation methodology varies)
- Predicting individual customer churn (better signals exist)
- Single-shot decisions ("our NPS is 35, so we're good")

## When This Reference Doesn't Help

- **Implementing health scores in your CRM.** Tactical; see business-growth/ skills.
- **Setting up NPS survey infrastructure.** Use Delighted, Wootric, Pendo, etc.
- **CS comp design.** See `c-level-advisor/skills/chro-advisor/`.
- **Pricing strategy.** See `c-level-advisor/skills/cmo-advisor/` and consider Patrick Campbell's "Monetizing Innovation" framework.

This reference is about reading retention data honestly, not about gathering it.

---

**Source authorities (non-exhaustive):**

- Nick Mehta, Dan Steinman, Lincoln Murphy — "Customer Success" (Wiley, 2016) — foundational text for the modern CS discipline
- Lincoln Murphy — "Customer Success: Building a Customer Engagement and Retention Framework" — defines GRR/NRR/CHURN clearly
- David Skok (Matrix Partners) — "SaaS Metrics 2.0" (forEntrepreneurs blog) — financial framework for retention math
- Bessemer Venture Partners — "State of the Cloud" annual report — benchmark retention numbers across SaaS stages
- ChartMogul / ProfitWell SaaS Benchmarks — public industry benchmarks for NRR/GRR by stage and ACV
- Reichheld, Fred — "The Loyalty Effect" (HBS Press, 1996) — origin of NPS framework and retention economics
- Tomasz Tunguz (Redpoint) — extensive writing on NRR vs GRR and the leaky bucket pattern
