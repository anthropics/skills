---
name: commercial-skills
description: Use when reviewing, approving, or designing commercial motion — pricing models, deal review, discount approval, partnership economics, channel mix, commercial policy, RFP/RFI response, bookings forecast. Triggers on "review this deal", "should we discount", "pricing model", "partner economics", "RFP response", "bookings forecast", "channel mix". Forks context to route to one of seven Commercial sub-skills (pricing-strategist, deal-desk, partnerships-architect, channel-economics, commercial-policy, rfp-responder, commercial-forecaster) and returns a digest. Distinct from business-growth (sales execution) and c-level-advisor/cro-advisor (strategic CRO judgment).
context: fork
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [commercial, pricing, deal-desk, partnerships, channel, rfp, forecast, cro, orchestrator]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Commercial — Domain Orchestrator

The Commercial surface is **per-deal economics and packaging**: how the company prices, packages, approves, and forecasts revenue. This orchestrator forks its context, routes your inquiry to one of seven sub-skills, then returns a digest. Heavy intake (RFP PDFs, pipeline exports, partner agreements) stays in the forked context.

## When to invoke

| Symptom | Sub-skill |
|---|---|
| "We're losing deals on price — should we drop prices or repackage?" | `pricing-strategist` |
| "Can we approve a 40% discount on this Enterprise deal?" | `deal-desk` |
| "Should we sign with this reseller? What's their tier?" | `partnerships-architect` |
| "Is our partner channel actually profitable?" | `channel-economics` |
| "What should our standard discount matrix look like?" | `commercial-policy` |
| "Help me respond to this 60-page RFP" | `rfp-responder` |
| "What's our Q4 bookings forecast at current conversion?" | `commercial-forecaster` |

## Routing logic (deterministic)

Same two-signal threshold pattern as `business-operations-skills`. Single-signal → clarifying question. Mixed signals → highest-confidence first, chain second in follow-up turn.

### Signal table

| Signal class | Keywords | Sub-skill |
|---|---|---|
| **PRICING** | pricing, price, packaging, tier, WTP, willingness to pay, Van Westendorp, value pricing | `pricing-strategist` |
| **DEAL** | deal, discount, approval, margin, T&Cs, redline, exception, MSA | `deal-desk` |
| **PARTNERSHIP** | partner, reseller, OEM, co-sell, joint GTM, revenue share, channel agreement | `partnerships-architect` |
| **CHANNEL_ECON** | channel mix, cost to serve, channel ROI, direct vs partner, channel economics | `channel-economics` |
| **POLICY** | commercial policy, discount matrix, T&C library, exception policy, deal framework | `commercial-policy` |
| **RFP** | RFP, RFI, RFQ, proposal request, vendor questionnaire, security questionnaire | `rfp-responder` |
| **FORECAST** | forecast, bookings, billings, ARR, NRR forecast, pipeline math, funnel projection | `commercial-forecaster` |

## Workflow (Matt Pocock grill discipline)

Derived from Matt Pocock's `grill-with-docs` pattern: **explore-then-ask, one question per turn with a recommended answer, walk the decision tree depth-first, track dependencies, anchor every challenge in the SaaS pricing / deal desk canon** (`references/`).

### Step 1 — Explore before asking

Check the user's working directory first:
- Is there a deal record, pricing comp table, RFP doc, or pipeline export already in the workspace?
- Does the inquiry already disambiguate the lane (e.g., "review this 60-page RFP" — that's `rfp-responder`, no question needed)?
- Is there an artifact filename that resolves the lane (`pipeline-Q4.csv` → forecast; `MSA-redline.docx` → deal)?

If the workspace resolves the lane, **route silently**.

### Step 2 — If still ambiguous, ONE forcing question with a recommended answer

Matt's rule: never bundle. Always recommend.

Pattern:
```
Q1/1: [precise question naming the two candidate lanes]
Recommended: [Lane X, because <signal-table rationale>]

(Confirm, or override?)
```

### Step 3 — Decision-tree walk for multi-lane inquiries

If the inquiry legitimately crosses two lanes (e.g., "this RFP wants a discount we don't normally give" = RFP + DEAL + maybe POLICY), walk depth-first:

1. Highest-confidence lane first → run sub-skill in forked context → digest
2. Ask: "Now run [second lane]? Recommended: yes, because [dependency]."
3. Confirm before chaining.

Never silently chain.

### Step 4 — Invoke sub-skill in forked context

Forward original prompt + structured inputs (pipeline CSV, RFP doc path, pricing comp table, MSA redline).

### Step 5 — Return digest with cited canon challenge

≤ 200 words: analyzed, top 3 findings (anchored to canon citation), top 3 next actions (named approver where applicable), artifact path, and **one grill challenge** for the user. Examples:

- "Your deal scorecard shows 38% margin after discount. Skok's For Entrepreneurs benchmark says SaaS deals < 70% gross margin pre-discount need scrutiny. Did you model fulfillment cost or just COGS?"
- "Your packaging has 14 features in Better and 16 in Best. Madhavan Ramanujam (Monetizing Innovation): tiers with no clear differentiator make 70% of customers pick the cheapest. What's the one feature that forces an upgrade?"

## Forcing-question library (grill-with-docs pattern)

Grill the user on lane-defining decisions before invoking the sub-skill. One per turn, recommended answer, canon citation:

- **PRICING lane**: "Before picking a model: is your customer paying for outcomes, seats, or usage? Recommended: outcomes (value-based) if you can measure them. Anti-pattern (Ramanujam 2016 *Monetizing Innovation*): seat-based pricing on a usage-variable product caps your TAM at 20% of WTP."
- **DEAL lane**: "Before approving: what's the gross margin at full discount, **and** what does next quarter's pipeline look like at the same terms? Recommended: model both. Anti-pattern (Tunguz benchmarks): one 40% precedent reshapes 3 quarters of pipeline."
- **FORECAST lane**: "Before forecasting: are you using stage-conversion rates from the last 4 quarters, or the last 12? Recommended: last 4 weighted heavier. Anti-pattern (Skok, OpenView): equal-weighting 12 months hides the recent slowdown."
- **PARTNERSHIP lane**: "Before signing: does the partner have **independent demand**, or are they reselling our pipeline? Recommended: insist on indep demand evidence. Anti-pattern (Forrester channel research): channel-led deals from your own pipeline cost more than direct."

Never run a sub-skill until the lane-defining decision is locked.

## Assumptions

1. User has commercial authority OR is preparing analysis for someone who does.
2. User wants **deterministic decision support**, not the final answer — the human approves the deal, sets the price, signs the partner.
3. Inputs may be partial — every sub-skill ships templated dummy data so the user can see the shape before filling in their own.

## Non-goals

- Not a CRM, CPQ system, or contract repository.
- Does not auto-approve deals. Every output is **a score + recommendation + human-approver routing**.
- Does not store deal history across sessions.

## Distinct from

- **`business-growth/sales-engineer`** — that's the **technical sale** (demos, POCs). Commercial is **economic shape** of the deal.
- **`business-growth/revenue-operations`** — that's **process** (lead routing, SDR motion). Commercial is **per-deal economics + policy**.
- **`business-growth/contract-and-proposal-writer`** — that's **authoring** prose. Commercial is **decision logic + structured response**.
- **`c-level-advisor/cro-advisor`** — that's strategic CRO judgment ("when do we hire VP Sales?"). Commercial is tactical ("approve this discount").
- **`finance/financial-analysis`** — that's **close + report**. Commercial is **forecast + per-deal economics**.

## Output artifacts

| Sub-skill | Artifact |
|---|---|
| pricing-strategist | `pricing_model.md` + `wtp_analysis.json` |
| deal-desk | `deal_scorecard.md` + `discount_approval_routing.json` |
| partnerships-architect | `partner_tier_assignment.md` + `revshare_model.json` |
| channel-economics | `channel_mix_analysis.md` + `cost_to_serve.json` |
| commercial-policy | `commercial_policy.md` (discount matrix + exception flow) |
| rfp-responder | `rfp_response.md` + `winrate_estimate.json` |
| commercial-forecaster | `forecast.md` + `pipeline_math.json` |

## Anti-patterns (do not)

- ❌ Recommend a specific price — recommend a **range + model**, user picks the number
- ❌ Auto-approve discounts above policy — every >X% discount routes to a named human approver
- ❌ Generate an RFP response without proof points the user can verify
- ❌ Forecast bookings without surfacing the **conversion assumption** explicitly
- ❌ Run all 7 sub-skills "to be thorough" — pick one, digest, chain if needed

## References

- SaaS pricing canon: Tomasz Tunguz, David Skok, Bessemer Venture Partners
- Deal desk: SaaStr playbooks, Winning by Design
- Path-B build pattern: `documentation/implementation/bizops-commercial-expansion-plan.md`
