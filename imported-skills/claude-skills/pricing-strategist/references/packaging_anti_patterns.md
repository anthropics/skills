# Packaging Anti-Patterns

Reference for `packaging_designer.py`. The anti-pattern detectors in the tool implement the
flags below. This document is the source-of-truth for *why* each pattern is harmful.

---

## The seven anti-patterns

### 1. Decoy tier that fools no one

A middle tier designed to make the top tier look reasonable — but the price gap is too small,
the feature list is too thin, or the differentiation is purely cosmetic. Customers see through
it, and worse: it trains them to question your pricing integrity.

**Detection:** Best tier > 2x Better price with < 1.5x value.
**Fix:** Either compress Better and Best closer (real differentiation) or widen the value gap.

### 2. Feature dump in the Best tier

Every roadmap feature gets tossed into Best because "Enterprise wants it." Result: Best has
3x the features for 2x the price. Customers buy Better and never upgrade.

**Detection:** Best feature count > 2x Better's with price ratio < 1.5x.
**Fix:** Move 1-3 "upgrade trigger" features down to Better and re-price.

### 3. No clear upgrade trigger

A customer on Good has no specific friction that pushes them to Better. Marketing fixes this
with "more advanced features" copy — but if you can't name the *single event* that triggers
the upgrade ("you hit 10k API calls", "you added a 5th seat", "you needed SSO"), customers
don't upgrade.

**Detection:** Better tier features have lower average importance than Good tier features.
**Fix:** Identify 1-2 "moment of pain" features and move them into the gate.

### 4. Usage-based pricing hidden inside subscription tiers

"Pro tier: includes up to 100k events, then $X per 1k." This is two pricing models pretending
to be one. Customers feel deceived when overage hits. Either commit to subscription (with a
realistic cap) or commit to usage (with a transparent meter).

**Detection:** Pricing-page narrative inspection — not algorithmic. Flag manually.
**Fix:** Pick one model. If you genuinely need both, use a clean Platform + Consumption hybrid,
not a hidden-overage subscription.

### 5. Bronze / Good tier as loss leader

Good is so cheap that cost-to-serve eats most of the revenue. Customers stay on Good forever
because the value-per-dollar is too good. Acquisition costs amortize through Better/Best
upgrades that never happen.

**Detection:** Cost-to-serve aggregate > 80% of Good tier price.
**Fix:** Raise Good's price floor, or strip a feature down to Better.

### 6. Enterprise / Best = "Call us" with no anchor

"Contact sales for pricing" at the top tier with no published anchor price. Prospects with
budget constraints disqualify themselves without ever talking to you. Competitors who publish
ranges win the consideration set.

**Detection:** Best tier has features but no published price.
**Fix:** Publish a "Starting at $X" anchor. The number doesn't have to be precise — it just
has to disqualify the wrong-fit prospects and qualify the right-fit ones.

### 7. Feature appears in all 3 tiers (no differentiation)

If "API access" is in Good, Better, and Best with the same scope, it's not a tier feature —
it's a base feature. Listing it three times wastes pricing-page real estate and dilutes the
upgrade narrative.

**Detection:** Feature appears in all 3 tiers' assigned-feature lists.
**Fix:** Either drop it from the tier comparison or differentiate scope (rate-limited /
metered / unlimited).

---

## Authoritative sources

1. **Patrick Campbell — ProfitWell / Paddle research on packaging**.
   "The State of Subscription Pricing" reports and the ProfitWell podcast.
   Empirical: tier redesigns that fixed clear upgrade triggers grew NRR by 8-15 points on
   average across their cohort. https://www.paddle.com/resources

2. **Madhavan Ramanujam — Monetizing Innovation (Wiley, 2016)**.
   The "9 mistakes" framework: feature shock, minivation, hidden gem, undead. Anti-patterns 2
   (feature dump), 3 (no upgrade trigger), and 7 (no differentiation) map directly to
   Ramanujam's mistake taxonomy.

3. **OpenView — SaaS Benchmarks + Product-Led Growth reports**.
   Annual benchmarks on tier mix, free-to-paid conversion, and the cost of bad packaging.
   https://openviewpartners.com/saas-benchmarks-report/

4. **Bessemer Venture Partners — Vertical SaaS Index + Cloud 100 Memos**.
   Documents the move from 3-tier to 4-tier packaging in vertical SaaS as products mature, and
   the failure modes when the 4th tier is added without removing complexity from existing tiers.
   https://www.bvp.com/atlas

5. **Kyle Poyar — Growth Unhinged**.
   "The Anatomy of a Great Pricing Page" series. Anti-patterns 5 (loss leader) and 6 (no
   anchor) come from Poyar's documented PLG-to-enterprise transition patterns.
   https://www.growthunhinged.com/

6. **SaaS Capital — Spending Benchmarks for Private B2B SaaS Companies (annual)**.
   Cost-to-serve benchmarks by ACV band. Source for the "Bronze tier loss leader" threshold
   (80% cost-to-serve ratio).

7. **Tomasz Tunguz — Theory Ventures**.
   Multi-year posts on tier-mix evolution in Cloud 100 cohort. Documents the death of 5-tier
   pricing pages and the consolidation toward Good/Better/Best + Enterprise.
   https://tomtunguz.com/

8. **Simon-Kucher & Partners — Global Pricing Studies**.
   Cross-industry data on pricing-page complexity vs conversion. Their research underpins the
   "more tiers = more cognitive load" finding behind anti-pattern 4 (hidden usage inside subscription).

## How this skill uses the references

- `packaging_designer.py` runs deterministic detection for 7 anti-patterns (the manual-inspection
  one — hidden usage in subscription — is documented but not auto-detected; the tool relies on
  the human reading the pricing-page narrative).
- Industry profiles encode tier-mix priors (Good 50% / Better 30% / Best 20% for SaaS, etc.)
  derived from OpenView and BVP benchmarks.
- Price-ratio thresholds (2.5x Good → Better, 2.0x Better → Best for SaaS) come from
  ProfitWell + Tunguz cohort averages.
- The "no anchor price" flag implements the Poyar / BVP guidance that Enterprise tiers need
  published starting prices.
