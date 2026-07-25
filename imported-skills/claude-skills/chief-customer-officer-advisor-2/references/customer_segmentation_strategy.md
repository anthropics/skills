# Customer Segmentation Strategy — The Decision: "How do we invest differently across customers?"

This reference answers exactly one decision: **which customers get how much investment from CS — and why?**

Pair with `scripts/customer_segmentation_designer.py` for automation.

## The Failure Mode

> "We treat all our customers equally."

This is operationally false (you can't) and strategically wrong (you shouldn't). Equal treatment means:
- Strategic accounts get under-served (executive sponsorship goes to whoever's loudest)
- SMB accounts get over-served (high-touch CS time that destroys unit economics)
- Misfit accounts consume resources that should fund the next strategic acquisition

The discipline is **differential investment**: more CS time and budget per dollar of ARR for high-fit, high-value accounts; less or none for low-fit, low-value accounts.

## The 4-Tier Framework

Standard B2B SaaS framework. ARR ranges are baseline; adjust for your ACV distribution.

### Tier 1: Strategic
- **ARR range:** Top 5% of accounts, typically $100K+
- **% of customers:** ~5%
- **% of ARR:** often 30-50% (Pareto distribution)
- **Coverage model:** Named CSM + executive sponsor + dedicated implementation
- **Investment per account/yr:** $20K-50K (CSM time + exec time + custom work)
- **Examples:** Top 10 logos by ARR, design-partner accounts, public-reference customers

**Hallmarks:**
- Multi-year contracts with QBRs / EBRs
- Custom integrations, API support, prioritized roadmap input
- Executive sponsor on the customer side AND on yours
- Reference + advocacy expected

### Tier 2: Enterprise
- **ARR range:** Next 15-20%, typically $20K-$100K
- **% of customers:** ~15-20%
- **% of ARR:** often 25-35%
- **Coverage model:** Named CSM
- **Investment per account/yr:** $5K-15K
- **Examples:** Mid-sized companies, departmental deployments at large companies

**Hallmarks:**
- Annual contracts, quarterly check-ins
- Standard integrations
- Single primary CSM, no executive sponsor unless escalated

### Tier 3: Mid-Market
- **ARR range:** Next 30-40%, typically $5K-$20K
- **% of customers:** ~30-40%
- **% of ARR:** ~15-25%
- **Coverage model:** Pooled CSM + automation (1:many)
- **Investment per account/yr:** $1K-3K
- **Examples:** Growing SMBs, smaller departmental deployments

**Hallmarks:**
- Pooled CSM model: one CSM owns 50-150 accounts, automation triggers human touch
- Annual contract auto-renew default
- Self-serve onboarding with optional human support
- Standard health scoring + trigger-based intervention

### Tier 4: SMB / Long-Tail
- **ARR range:** Bottom 40-50%, typically <$5K
- **% of customers:** ~40-50%
- **% of ARR:** often <10%
- **Coverage model:** Tech-touch + self-serve
- **Investment per account/yr:** $50-500 (mostly automation cost)
- **Examples:** Solo users, small teams, freemium/PLG converts

**Hallmarks:**
- Fully self-serve onboarding
- Email-based + community-based support
- 1 CSM for the entire tier (escalation handler only)
- Monthly or annual contracts; high price sensitivity

## ICP Fit Scoring (0-10 weighted)

Segmentation by ARR alone is incomplete. A $50K customer with poor ICP fit may cost more than they earn. Layer ICP fit on top.

**Recommended weighting:**

| Signal | Weight | Why |
|---|---|---|
| in_target_industry | 2.0 | Industry fit drives product-market fit |
| in_target_size_range | 1.5 | Wrong size = wrong feature requirements |
| uses_target_workflow | 2.0 | Workflow fit is the strongest retention predictor |
| has_executive_sponsor | 1.5 | Single-threaded accounts churn 3-5x more |
| advocates_publicly | 1.0 | Public advocacy is a strong forward signal |
| expansion_potential_high | 1.0 | Existing customers ARE the next round of revenue |
| competitor_concentration_low | 1.0 | High competitor concentration = price war risk |

**Score interpretation:**

| Score | Meaning |
|---|---|
| 8-10 | Strong ICP fit; invest aggressively, regardless of current ARR |
| 5-7 | Decent fit; standard tier investment |
| 0-4 | Poor fit; consider tech-touch only, or kill list |

## The Kill List (politically difficult, financially obvious)

**Kill candidate criteria** (any one is a yellow flag; two or more is a kill):

- ICP fit score < 5
- Annual support cost > 50% of ARR
- Tenure < 12 months AND multiple escalations
- Customer's company has recently been acquired by a larger conflicting entity
- Customer is in a declining industry / shutting down

**The 3 paths for kill candidates:**

1. **Do not renew.** Send a polite non-renewal communication 60-90 days before contract end.
2. **Downgrade to tech-touch.** Remove CSM coverage; let the customer self-serve. Many will churn naturally; some will stick if the product is actually serving them.
3. **Raise price to cost-recover.** Make the renewal pricing reflect the real cost of serving them. If they accept, great. If they leave, also fine.

**Anti-pattern:** "Strategic accounts" that are actually kill candidates. Founders often protect their first 5-10 customers far past the point of economic sense. Quarterly audits force the conversation.

## Tier Transition Triggers

Customers migrate between tiers. Standard triggers:

- **SMB → Mid-market:** ARR grows above $5K AND tenure > 12 months AND ICP fit ≥ 6
- **Mid-market → Enterprise:** ARR grows above $20K AND has dedicated executive contact
- **Enterprise → Strategic:** ARR above $100K AND multi-year deal AND expansion potential AND named exec sponsor on both sides
- **Down-tier:** ARR drops below tier floor OR ICP fit drops AND quarterly review confirms

**Operational discipline:** quarterly tier review forced for every customer above $5K. Below $5K, automation handles tier assignment.

## Why Segmentation Is Strategic, Not Operational

Segmentation seems like an ops question ("how do we organize the book?"). It's actually a strategic question: **which customers does the company exist to serve?**

A segmentation that has 70% of customers in the "Strategic" tier means the company isn't choosing — and likely is over-investing in the long tail relative to ARR concentration. A segmentation with 70% in "SMB / long-tail" means the company is a PLG/SMB business and should design CS, product, and pricing accordingly.

**Segmentation = strategy in operational form.** Get it wrong, and your CS team, product roadmap, and pricing all misfire.

## When This Reference Doesn't Help

- **Setting up segmentation in your CRM.** Tactical; use Salesforce / HubSpot / etc. native tier fields.
- **ICP refinement when product-market fit is unclear.** See `c-level-advisor/skills/cpo-advisor/` for PMF framework first.
- **Pricing strategy across tiers.** See `c-level-advisor/skills/cmo-advisor/` and consider Patrick Campbell's "Monetizing Innovation".

This reference is about the strategic design of differential investment, not the CRM implementation.

---

**Source authorities (non-exhaustive):**

- Lincoln Murphy — "Customer Success" (Wiley, 2016) + extensive blog on segmentation
- Bain & Co. — "Net Promoter System" research on differential treatment of "promoters"
- Bain — "The Loyalty Effect" (Reichheld) — economics of long-term customer value
- Tomasz Tunguz (Redpoint) — multiple essays on tiered CS coverage
- David Skok — SaaS Metrics 2.0 on the Pareto distribution of revenue and the long-tail problem
- ChartMogul / ProfitWell SaaS benchmarks — distribution of customers by ACV across SaaS companies
- Adamson, Dixon, Toman — "The Challenger Customer" (Portfolio, 2015) — buying-center concentration and CS implication
