# Deal Desk Canon

Operating practice for per-deal review and approval routing in B2B SaaS / enterprise software. Compiled from authoritative deal-desk and revenue-operations sources.

## Why a deal desk exists

The deal desk is the **operational gate between sales and finance/legal**. Its job:

1. **Standardize discount approval** so the same discount-percent always routes the same way.
2. **Defend gross margin** by quantifying the actual margin loss from a proposed discount (not just the discount percent).
3. **Triage commercial terms** so legal review hits only the deals that need it.
4. **Speed up the deals that should be fast** by routing simple deals to AE/Manager authority and reserving CFO/CRO attention for the consequential ones.

Without a deal desk, every above-band deal becomes a 1:1 negotiation between an AE and a finance leader, which is slow, inconsistent, and creates pricing-integrity drift over time.

## Operating tenets

These are the non-negotiables — adopted across every reference cited below.

1. **Never auto-approve.** Even green deals get a named approver. The skill outputs *who must sign*, not *the deal is fine*.
2. **Margin, not discount.** A 30% discount on an 80%-gross-margin product destroys *37.5% of the margin dollars* (COGS is fixed, so every discounted dollar comes straight out of margin) — not 30%. See `discount_economics.md` for the math.
3. **The chain stops at the lowest hop that has authority.** Over-routing trains reps to over-discount because they expect VP attention anyway.
4. **Critical signals override composite.** A high-composite deal with uncapped indemnity is still a DECLINE.
5. **Modifiers must be explicit.** Enterprise floor (large ARR forces VP review) and SMB fast-lane (small deals can skip a hop) are surfaced; hidden adjustments destroy audit trails.
6. **The deal desk is a router, not a salesperson.** It does not negotiate; it routes the negotiation to the named human.
7. **One source of truth per deal.** The intake template is the spec. Re-pricings or term changes create a new intake, not an edit-in-place.

## Standard approval bands (industry-customary)

Default policy (override with `policy_thresholds` in input JSON):

| Discount band | Approver | Typical cycle |
|---|---|---|
| 0% - 15% | AE | same-day |
| 15% - 25% | Sales Manager | 1 business day |
| 25% - 35% | Director of Sales | 2 business days |
| 35% - 50% | VP Sales | 3 business days |
| 50%+ | CFO + CRO | 5+ business days |

Enterprise-software profile shifts bands upward (larger ACVs absorb deeper discounts). Services profile shifts downward (margin-thin). Marketplace profile is tightly capped (take-rate is the lever).

## Tier and ARR modifiers

- **Enterprise floor**: Deals at ARR >= profile threshold force VP-level review even on small discounts. Rationale: the customer is consequential regardless of the discount.
- **SMB fast-lane**: Deals at ARR <= profile threshold can drop one hop (only if discount is within the second band). Rationale: cycle time matters more than marginal margin defense on a $12K deal.

## Sources

1. **SaaStr** — Jason Lemkin's deal-desk playbooks emphasize that the deal desk's primary job is *defending gross margin and pricing integrity*, not just routing discounts. https://www.saastr.com/
2. **Winning by Design** — Jacco van der Kooij + Jason Reichl, *Bowtie Funnel* and *Revenue Architecture*. Establishes that the deal desk owns the gate between Acquisition (sales) and Retention (CS) — bad-term deals cost more in churn than they earn in ARR. https://winningbydesign.com/
3. **Forrester Research** — Deal desk maturity model (4 stages: ad-hoc → formal → strategic → predictive). Most companies hit a wall at stage 2 because they lack the data infrastructure to score deals consistently.
4. **RevOps Co-op** — Community playbooks (operating notes from Iceberg RevOps, Sapphire Ventures, others). Emphasizes that the deal desk is a **routing function**, not an approval function. The named approver is always a human.
5. **OpenView Venture Partners** — *State of the SaaS Sales Org* annual benchmarks. Documents discount-band conventions across stage (seed → growth → late-stage) and shows that median discount creeps up year-over-year unless deal-desk discipline is enforced. https://openviewpartners.com/
6. **Bridge Group SaaS AE Compensation Research** — Annual survey of B2B SaaS AE comp + quota. Establishes that AE discount authority above 15-20% destroys quota attainment math (because the AE under-prices to close).
7. **Salesforce Deal Desk Best Practices** — Internal Salesforce documentation (Trailhead + RevOps blog). Codifies the queue model: every above-AE-authority deal enters a queue with SLA. Aging deals escalate automatically.

## Patterns to surface in any deal-desk review packet

- Composite score with per-dimension breakdown.
- Named approver chain with the hop where the discount lands highlighted.
- Estimated cycle days based on hop count.
- Any CRITICAL signals (uncapped indemnity, MFN, perpetual license-back, missing DPA).
- The standard counter-language for any HIGH/CRITICAL redline.
- A **single explicit statement**: "This is a routing recommendation. The named approvers must sign."
