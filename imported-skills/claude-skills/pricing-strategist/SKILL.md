---
name: pricing-strategist
description: "Use when designing or revisiting product pricing — selecting a pricing model (subscription seat-based, usage-based, value-based, freemium, or hybrid), running Van Westendorp Price Sensitivity Meter analysis on WTP survey data, or designing Good/Better/Best packaging tiers. Recommends a model and a price range with trade-offs, never a single number. For Commercial leads, Product Marketing, and CMOs at the pricing-design moment — not deal-by-deal discounting, not brand positioning."
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [commercial, pricing, packaging, wtp, van-westendorp, value-based-pricing, saas-pricing]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# pricing-strategist

## Purpose

Help Commercial, Product Marketing, and CMO functions answer three questions at the pricing-design moment:

1. **Which pricing model fits this product + customer + market?** (subscription seat-based, usage-based, value-based, freemium, hybrid)
2. **What does the customer actually pay before it feels too expensive?** (Van Westendorp PSM on WTP survey responses)
3. **How should we package this into tiers?** (Good / Better / Best — with anti-pattern detection)

The skill recommends **a model and a range**. The human picks the number, owns the trade-offs, and runs the GTM.

## When to use

- Launching a new SaaS / API / AI tool and choosing the first pricing model
- Revisiting pricing after 18+ months of GTM data (model shift, not just price increase)
- Designing or redesigning tier packaging (Good/Better/Best, Bronze/Silver/Gold)
- You have Van Westendorp survey data and want the optimal price range
- A board / exec is asking "what should we charge?" and you need the structured answer
- You suspect your packaging has anti-patterns (decoy tier, feature dump, no upgrade trigger)

**Do not use for:**
- Per-deal discount approval → `deal-desk`
- Strategic CMO positioning, brand, category creation → `c-level-advisor/cmo-advisor`
- Whole-company revenue strategy → `c-level-advisor/cro-advisor`
- Technical-sale enablement → `business-growth/sales-engineer`

## Workflow

### Step 1 — Assess customer context

Fill `assets/pricing_brief_template.md` (≈ 20 min). Capture: industry, deal size avg, customer count, value drivers, adoption curve, consumption pattern (seat / usage / value / hybrid), competitor models.

### Step 2 — Pick the pricing model

Run `scripts/pricing_model_picker.py --input brief.json --profile saas --output markdown`. Output ranks 5 models by fit-score 0-100 with trade-offs. Decision logic is deterministic: low usage variance + high seat-attach → subscription wins; power-law usage + variable customer value → usage-based wins.

### Step 3 — Validate WTP with Van Westendorp PSM

If you have survey data (≥ 4 questions per respondent: too cheap / bargain / getting expensive / too expensive), run `scripts/wtp_analyzer.py --input survey.json --output markdown`. Output: 4 intersection points (OPP, IDP, PMC, PME) and the Range of Acceptable Prices.

PSM gives a **range**, not the price. See `references/van_westendorp_methodology.md` for common misinterpretations.

### Step 4 — Design packaging

Run `scripts/packaging_designer.py --input features.json --profile saas --output markdown`. Output: 3-tier Good/Better/Best assignment with anti-pattern flags (decoy tier, feature dump, no upgrade trigger, Bronze loss leader, Enterprise no-anchor).

### Step 5 — Decide

Take model + range + packaging into the pricing committee. Skill does not commit the number — you do.

## Scripts

- `scripts/pricing_model_picker.py` — 5-model fit scorer (subscription / usage / value / freemium / hybrid)
- `scripts/wtp_analyzer.py` — Van Westendorp PSM implementation
- `scripts/packaging_designer.py` — Good/Better/Best tier designer with anti-pattern detection

All scripts: stdlib only. `--help` and `--sample` work on all three.

## Quick example

```bash
# Emits a scored 5-model pricing-fit recommendation (subscription / usage / value / freemium / hybrid) for the built-in example
cd commercial/skills/pricing-strategist && python3 scripts/pricing_model_picker.py --sample
```

## References

- `references/saas_pricing_canon.md` — Skok, Tunguz, Campbell, Ramanujam, BVP, Shevlin, Stanford GSB
- `references/van_westendorp_methodology.md` — original 1976 paper, NMS refinement, Conjoint.ly, Sawtooth, ESOMAR, Lipovetsky, Decision Analyst
- `references/packaging_anti_patterns.md` — ProfitWell, OpenView, BVP vertical SaaS, Ramanujam, Poyar, SaaS Capital

## Assumptions

- Pricing decisions are joint: Commercial owns the model + tier shape, Product owns the features-per-tier, Finance owns the discount envelope, Legal owns the contract.
- Van Westendorp PSM is a **directional** tool. N ≥ 30 minimum, N ≥ 100 preferred. Below 30, the script emits a sample-size warning.
- "Value-based pricing" requires a measurable customer value driver (revenue lift, cost saved, time recovered). If you can't measure it, don't pick value-based.
- Industry profiles tune defaults — they don't override your data.
- This is a decision-support skill, not a price oracle. Output is a model + range, never the number.

## Anti-patterns

- **Recommending a specific number.** This skill emits a model and a range. Final price is a human commercial decision involving deal-desk policy, competitive intel, and strategic intent that this skill cannot know.
- **Using PSM with N < 30.** Statistical noise dominates. The script warns; respect the warning.
- **Treating PSM as "the price."** PSM gives a Range of Acceptable Prices (RAP) and an Optimal Price Point (OPP). Test the range in market, don't anchor on a single intersection.
- **Picking value-based pricing without a measurable value metric.** Without instrumentation to show customer ROI, value-based collapses into "whatever they'll pay" — which is just bad usage-based pricing.
- **Designing tiers before picking a model.** Tier structure depends on the model. Run pricing_model_picker first.
- **Packaging "feature dumps" into the Best tier.** If Best has 3x the features for 2x the price, customers buy Better and never upgrade. See `packaging_anti_patterns.md`.
- **Hidden usage-based pricing inside subscription tiers.** "Up to 100k API calls/mo, then $X per 1k" disguised as a "Pro tier" is two pricing models in one. Customers notice. Pick one.
- **Confusing this skill with deal-desk.** Pricing strategy = the menu. Deal-desk = approving discounts off the menu. Different decision, different cadence, different owner.

## Distinct from

- **deal-desk** — per-deal discount approval, MEDDIC, deal scoring. Operates daily on existing pricing.
- **c-level-advisor/cmo-advisor** — strategic positioning, brand, category. Pricing strategist consumes positioning as input, doesn't generate it.
- **c-level-advisor/cro-advisor** — full-funnel revenue strategy, comp plans, territory design. Pricing strategist is one input to CRO.
- **business-growth/sales-engineer** — technical sale, POC scoping. Sales engineering operates after pricing is set.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-commercial` or the orchestrator. Recommended answer + canon citation per question. Never bundled.

1. **"Is your customer paying for outcomes, seats, or usage?"**
   Recommended: outcomes (value-based) if you can measure them; usage if marginal cost is variable; seats only if usage is roughly flat per user.
   Canon: Ramanujam 2016 (*Monetizing Innovation*) — Mistake #1 of 9: seat-based pricing on a usage-variable product caps TAM at ~20% of WTP.

2. **"Do you have a measurable value metric, or are you guessing?"**
   Recommended: instrument the value metric BEFORE going to market with value-based pricing.
   Canon: Patrick Campbell / ProfitWell research — value-based without instrumentation collapses into bad usage-based pricing.

3. **"What's the variance in customer usage across your top decile vs. median?"**
   Recommended: variance > 10x → usage-based wins; variance < 3x → subscription wins; in between → hybrid with usage overage.
   Canon: Kyle Poyar (*Growth Unhinged*) — high-variance products lose 60%+ of revenue on flat-rate plans.

4. **"What's your competitor's pricing model, and why are you choosing the same or different?"**
   Recommended: surface the differentiation hypothesis explicitly. Identical pricing = identical value claim.
   Canon: David Skok (*For Entrepreneurs*) — pricing is a positioning signal.

5. **"What sample size do you have for WTP analysis, and is it segmented?"**
   Recommended: N≥30 per segment for PSM, N≥100 for conjoint.
   Canon: van Westendorp 1976 / Sawtooth Software methodology — sub-30 PSM is statistical noise.

6. **"What's the ONE feature that forces a tier upgrade?"**
   Recommended: every Better and Best tier needs a single non-negotiable upgrade trigger.
   Canon: Ramanujam (*Monetizing Innovation*) — Mistake #4: tiers with no clear differentiator make 70% of customers pick the cheapest.

Walk depth-first. Lock 1-3 before opening 4-6. After all 6 are answered, invoke `pricing_model_picker.py` → `wtp_analyzer.py` → `packaging_designer.py` in sequence.
