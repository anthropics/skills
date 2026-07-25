# CS Coverage Model — The Decision: "How do we cover our customer base — and when do we add CSMs?"

This reference answers exactly one decision: **what coverage model do we use, what's the ratio, and when do we add headcount?**

Pair with `scripts/cs_coverage_calculator.py` for automation.

## The Four Coverage Models

### Tech-Touch (no human CSM)
- **Best for:** SMB / long-tail, ACV < $5K, high-volume PLG products
- **Ratio:** Often $5M-$15M ARR per CSM-equivalent (a single CSM handles escalations only)
- **How it works:** Self-serve onboarding, in-product guidance, lifecycle email automation, community support
- **Tooling stack:** Pendo / Appcues / Userpilot (in-product), Customer.io / HubSpot (email), Discourse / Slack community

**Trade-offs:**
- Lowest cost per customer
- Cannot save high-stakes deals; tech-touch customers churn silently
- Requires investment in product onboarding UX and content
- Escalation path must exist — when a tech-touch account becomes valuable, a human takes over

### Pooled CSM (1:many)
- **Best for:** Mid-market, ACV $5K-$20K
- **Ratio:** $2M-$5M ARR per CSM; 50-150 accounts per CSM
- **How it works:** One CSM owns a pool of accounts; automation triggers proactive outreach; reactive when customers ask
- **Hallmarks:** Quarterly automated check-ins, library of playbooks, on-demand 1:1 when triggered

**Trade-offs:**
- Lower cost than named
- Less account intimacy; CSMs don't know all 100 customers deeply
- Works well only with strong CS Ops + health-score automation
- Burnout risk if pool grows too large

### Named CSM (1:few)
- **Best for:** Enterprise, ACV $20K-$100K
- **Ratio:** $500K-$2M ARR per CSM; 20-30 accounts per CSM
- **How it works:** Each customer has a named CSM who knows their business; weekly to monthly cadence; CSM owns the renewal
- **Hallmarks:** Account plans, QBRs, named relationship with customer contacts

**Trade-offs:**
- Standard for enterprise SaaS
- Higher cost (~$180K fully-loaded per CSM)
- CSM ramp time 3-6 months; turnover is expensive
- Named CSMs become single point of failure if they leave

### Named CSM + Executive Sponsor
- **Best for:** Strategic accounts, ACV $100K+
- **Ratio:** $300K-$1M ARR per CSM; 5-10 accounts per CSM; exec sponsor allocates 4-8 hrs/quarter per account
- **How it works:** Named CSM handles tactical relationship; executive sponsor handles strategic + reputation + escalation
- **Hallmarks:** EBRs with customer C-suite, custom roadmap input, multi-year contracts

**Trade-offs:**
- Highest cost (CSM + 5-10% of an exec's time)
- Reserved for top accounts where loss would be material to the company
- Exec sponsor must actually engage — ceremonial sponsorship destroys trust

## Choosing the Model per Segment

Rule of thumb: model follows segment, segment follows ARR + ICP fit.

| Segment | Default model | Override when |
|---|---|---|
| Strategic (top 5%) | Named + exec sponsor | Always — the cost is justified by retention + reference value |
| Enterprise (15-20%) | Named CSM | Downgrade to pooled if ACV barely qualifies AND tenure stable |
| Mid-market (30-40%) | Pooled CSM | Upgrade to named if customer is on Strategic-upgrade trajectory |
| SMB / Long-tail (40-50%) | Tech-touch | Upgrade to pooled if expansion potential is exceptional |

## The Ratio Math

ARR-per-CSM is the most-cited CS metric. It's a useful starting point but **not a target**.

**What "ARR-per-CSM" actually measures:** the ratio of revenue under a CSM's responsibility. Higher = more leveraged; lower = more intimate.

**Ratios by stage (B2B SaaS baseline):**

| Stage | Strategic | Enterprise | Mid-market | SMB |
|---|---|---|---|---|
| Seed | n/a | $300K-$800K | $1M-$3M | n/a |
| Series A | $500K-$1M | $800K-$1.5M | $2M-$4M | $5M+ |
| Series B / Growth | $700K-$1.5M | $1M-$2M | $3M-$5M | $8M+ |
| Late-stage | $1M-$2M | $1.5M-$3M | $4M-$8M | $15M+ |

**Industry variation:**
- **Lower ratios (more CSM density needed):** complex products, regulated industries, customer success critical to expansion
- **Higher ratios (more leverage possible):** simple products, low-complexity workflows, strong product UX

## When to Add a CSM

Two independent triggers:

1. **By ARR:** total tier ARR exceeds (current_csm_count × target_ratio + 20% buffer)
   - The 20% buffer absorbs ramp time of new hires
   - Don't wait until existing CSMs are at 100% capacity to hire

2. **By account count:** total tier accounts exceeds (current_csm_count × accounts_cap)
   - Named CSM cap is ~25 accounts; beyond that, attention degrades
   - Pooled CSM cap is ~150 accounts; beyond that, automation must increase

**Whichever triggers first.** Run `cs_coverage_calculator.py` quarterly.

## When to Add a Manager

A CS manager is needed when **any of these become true:**

1. **5+ ICs in a single tier:** the original CSM lead can no longer code AND manage
2. **8+ CSMs across the entire CS function:** spans of control exceed comfortable management
3. **CS is escalating to CTO/CEO for non-product issues weekly:** clear leadership gap

**Manager profile:**
- Internal promotion preferred (knows the playbooks)
- Strong on people management + cross-functional skills
- Has run a CS book themselves; not a pure people manager

## Ramp Curve

New CSMs are not productive at hire.

| Tier | Time to 50% productive | Time to fully productive |
|---|---|---|
| Strategic | 3 months | 6-9 months |
| Enterprise | 2 months | 4-6 months |
| Mid-market | 1 month | 2-3 months |
| SMB / Tech-touch | 2 weeks | 1 month |

**Operational implication:** hire 90 days BEFORE you need the capacity, not when you're already underwater.

## CS Comp Design

CS comp aligned to retention + expansion is the standard.

**Common structure (named CSM):**

- 70% base salary + 30% variable
- Variable split:
  - 50% of variable on gross retention (renewals)
  - 30% on net retention (expansion)
  - 20% on activity (QBRs completed, health-score green %, etc.)

**Critical anti-pattern:** comp CSMs on "customer happiness" or NPS only. They game it and don't drive renewals.

**Pooled CSM comp:** more weight on activity + automation health, less on individual account outcomes (which are statistical at this volume).

## When This Reference Doesn't Help

- **CS technology stack selection (Gainsight, ChurnZero, Vitally, etc.).** Tactical; see CS Ops resources.
- **Health-score formula design.** Tactical; depends on product data model.
- **Comp negotiation with individual CSMs.** HR / management territory.

This reference is about the strategic decision of coverage model + ratio + hiring trigger, not the operational implementation.

---

**Source authorities (non-exhaustive):**

- Gainsight — "CS Maturity Model" + state-of-the-industry reports
- TSIA (Technology Services Industry Association) — annual CS benchmarks including ARR-per-CSM by segment
- Nick Mehta, Allison Pickens — "The Customer Success Economy" (Wiley, 2020)
- ChurnZero — "CS Salary Survey" annual report (CSM comp benchmarks)
- David Skok — SaaS Metrics 2.0 (CAC payback economics that fund CS)
- Lincoln Murphy — extensive writing on pooled vs named models
- Pacific Crest / KeyBanc Capital Markets — annual SaaS survey including CS-as-% of revenue benchmarks
