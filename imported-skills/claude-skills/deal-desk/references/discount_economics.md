# Discount Economics

The math of what a discount actually costs. Most sales discounts are described as a list-price reduction; the real impact is on **gross margin** and **LTV**, both of which compound across the customer base over time.

## The fundamental formula

The model is **fixed COGS**: discounting the price does not shrink the cost of delivering the product. At list price P with gross margin G%, COGS = (1 − G/100) × P and stays fixed when the price drops to (1 − D/100) × P. Two numbers follow:

    net_margin_pct = (G - D) / (100 - D) * 100        # post-discount margin %
    margin_dollars_destroyed_pct = D / G * 100        # share of margin $ given up

Every discounted dollar comes straight out of margin dollars — the discount amount IS the margin loss in dollars.

### Worked examples

| List discount | Gross margin | Margin $ destroyed | Net margin % |
|---|---|---|---|
| 10% | 80% | 12.5% | 77.8% |
| 20% | 80% | 25.0% | 75.0% |
| **30%** | **80%** | **37.5%** | **71.4%** |
| 30% | 60% | 50.0% | 42.9% |
| 40% | 80% | 50.0% | 66.7% |
| 50% | 80% | 62.5% | 60.0% |

**A 30% discount on an 80%-gross-margin product destroys 37.5% of the margin dollars** (30/80), even though the margin *percentage* only slips from 80% to 71.4%. The percentage is cosmetic; the dollars fund the P&L.

### Why the conventional shorthand is wrong

People often say "a 30% discount loses 30% of margin." Under fixed COGS that *understates* the damage: the discount cuts revenue by 30% but COGS doesn't move, so the entire discount comes out of margin dollars — 30/80 = **37.5%** of the margin is gone. The lower the starting margin, the worse it gets: the same 30% discount on a 60%-margin business destroys half its margin. This is why the deal scorer's margin dimension penalizes margin-dollar destruction directly, not just the post-discount margin percentage.

## LTV impact

Discount also compounds across multi-year contracts. Because COGS is fixed, every discounted dollar is a lost margin dollar — the gross margin % determines what *fraction* of margin that represents (D/G), not the dollar amount:

    lifetime_margin_loss = (D / 100) * list_arr * (term_months / 12)

For a $200K-list-ARR deal at 30% discount, 24-month term:

    = 0.30 * 200,000 * 2 = $120,000 of gross margin given up
    (= 37.5% of the $320K margin the deal would have carried at 80% GM)

That's $120K of fully-loaded P&L impact for one deal. Across 50 deals/quarter at the same discount and terms, the company signs away $24M/year of contracted gross margin.

## Discount creep

The most-cited dataset (Pacific Crest / KeyBanc SaaS Survey) shows median discount rises ~1.5 pts/year unless the deal desk actively defends pricing. Causes:

1. AE comp on bookings, not margin → AEs discount to close.
2. Multi-year deals trade discount for term length but term length doesn't recover the margin loss if churn risk is non-zero.
3. Competitive deals get matched discounts that then propagate to non-competitive deals via MFN clauses.
4. Renewal discounts (CS giving discount to retain) anchor the next renewal lower.

## When a discount is justified

The deal desk should approve a discount when **at least one** of these is true and quantified:

1. **Strategic logo** — the customer is a reference account that materially shortens future sales cycles. Logo value ≥ discount $.
2. **Expansion lock-in** — the discount is paired with a *multi-year + expansion commitment* that recovers margin over the contract term.
3. **Competitive displacement** — the discount displaces an incumbent and the lifetime ARR > displacement cost.
4. **Cash-acceleration** — payment up-front in exchange for discount, where the cash NPV recovers the margin loss.

The deal scorer's `strategic` dimension flags logo / reference / expansion / renewal explicitly. If none of those are set, a discount above the policy band is presumptively unjustified.

## NRR + discount correlation

OpenView's *State of the SaaS Industry* shows companies with high NRR (≥ 120%) discount less on initial deals than companies with low NRR (≤ 100%). The mechanism: high-NRR companies have a strong expansion motion that they don't need to buy with up-front discount; low-NRR companies discount up-front to compensate for weak expansion.

This is why deal-desk should treat "discount to close" as a leading indicator of NRR weakness, not a one-deal problem.

## Sources

1. **David Skok — For Entrepreneurs** — *SaaS Metrics 2.0* and *The SaaS Business Model*. Canonical treatment of LTV/CAC + the impact of discount on payback period. https://www.forentrepreneurs.com/
2. **Bessemer Venture Partners — State of the Cloud** — Annual report with discount benchmarks by ACV band ($1K, $10K, $100K, $1M+) and stage. https://www.bvp.com/
3. **Tomasz Tunguz — Redpoint** — Multi-year studies on discount-to-close patterns, including the finding that median enterprise SaaS discount sits at 18-22% across the industry. https://tomtunguz.com/
4. **OpenView Venture Partners** — *State of the SaaS Industry* + Expansion Economics research. Documents the NRR-vs-discount correlation. https://openviewpartners.com/
5. **Pacific Crest SaaS Survey** (now KeyBanc Capital Markets) — Annual primary-research survey of B2B SaaS companies. Most-cited dataset for discount benchmarks. https://www.key.com/businesses-institutions/industry-expertise/saas-survey.html
6. **KeyBanc Capital Markets SaaS Survey** — Continuation of Pacific Crest. Annual benchmark for net dollar retention, gross margin, and discount-by-segment.
7. **Insight Partners Revenue Operations Research** — Their PitchBook + portfolio data on discount discipline at growth-stage SaaS. https://www.insightpartners.com/

## Patterns to surface in any margin review

- Pre-discount gross margin and post-discount net margin in **absolute points**, not just percent.
- Lifetime margin given up over the contract term, in dollars.
- Whether the strategic flags justify the discount (logo / reference / expansion / renewal).
- Whether the customer is paying up-front in exchange for the discount (cash NPV).
- Comparison to the company's median deal-discount (drift signal).
