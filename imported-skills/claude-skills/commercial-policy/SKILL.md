---
name: commercial-policy
description: "Use when designing or revising a company's commercial policy — the rules of engagement governing discounts off list price, approver thresholds, exception flows, and the deal framework that Deal Desk and AEs operate under. Covers discount matrix design (ARR band x term length x payment terms x strategic value), commercial policy design, exception policy, discount governance, approval thresholds, deal framework structure, and policy linting (contradictions, gaps, cliff edges, gaming surfaces). For Head of Commercial, Head of Deal Desk, VP Sales, or RevOps at the policy-design moment — NOT per-deal application (that is deal-desk) and NOT pricing model selection (that is pricing-strategist)."
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [commercial, discount-policy, discount-matrix, exception-flow, governance, deal-framework, commercial-discipline]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# commercial-policy

## Purpose

Design the **rules of engagement** that govern discounting off list price — the artifact that Deal Desk and AEs operate under. Three deterministic tools:

1. `discount_matrix_builder.py` — builds a 4-dimensional matrix (ARR band × term length × payment terms × strategic value tier), each cell carrying an approved discount band backed by current win-rate + NRR data, plus an approver tier (AE / Manager / Director / VP / CFO).
2. `exception_router.py` — when an asks-for-discount lands outside the matrix, routes it through the named approver chain, attaches required compensating commitments (multi-year prepay + named expansion path + reference commitment + MSA tightening), produces machine-readable audit-trail metadata, and flags precedent risk if 3+ similar exceptions have landed in the trailing quarter.
3. `policy_linter.py` — lints the matrix for governance defects: approver inversion, band inversion, margin-floor violation, coverage gaps, cliff edges, undefined strategic tiers, inconsistent margin floors, thin data backing.

The output is the **policy itself** (matrix + exception flow + lint report), not a per-deal application of it.

## When to use

- A new Head of Commercial or Head of Deal Desk is writing the company's first formal commercial policy
- The existing matrix is older than 6 months and discount drift is showing in margin reviews
- Reps are citing "Maria approved 28% on Acme last quarter" as precedent and you need to break the precedent loop
- Q-over-Q exception count is rising and you suspect the matrix bands are mispriced
- CFO has tightened the margin floor and the matrix needs to be rebuilt against the new constraint
- A board / exec is asking "why do we discount this much?" and you need a data-backed defensible policy

**Do NOT use this skill to:**
- Approve a specific deal — that's `commercial/skills/deal-desk`
- Set the pricing model + list price — that's `commercial/skills/pricing-strategist`
- Author a proposal / SOW / MSA prose — that's `business-growth/contract-and-proposal-writer`
- Make the strategic "when do we hire a VP Sales" call — that's `c-level-advisor/cro-advisor`

## Workflow

1. **Audit current discount distribution.** Pull the last 4 quarters of closed-won + closed-lost deals from CRM. Fill `assets/policy_design_template.md` (~20 minutes). Capture: `arr`, `discount_pct`, `term_months`, `payment_terms_days`, `strategic_value`, `win_lost`, `nrr_12mo` per deal.

2. **Design the data-backed matrix.** Run `scripts/discount_matrix_builder.py --input policy_intake.json --profile {saas|enterprise-software|api|marketplace|services}`. Output is a 4-dimensional matrix with approved discount band + approver tier + margin floor + observed win-rate + observed NRR per cell. Cells with `n < 5` observed deals are flagged `THIN`.

3. **Design the exception flow.** Run `scripts/exception_router.py --sample` to see the structure. For each severity band of exception (0-5 pts over, 5-10, 10-20, 20+), the router enforces required compensating commitments. Codify the flow in your policy doc; the router becomes the operational implementation.

4. **Lint the matrix.** Run `scripts/policy_linter.py --input matrix.json`. Get a ranked findings report — BLOCKER / MAJOR / MINOR — across 10 lint rules. Resolve every BLOCKER before publishing the matrix to AEs.

5. **Publish + quarterly review.** Publish the matrix as a versioned artifact. Re-run the builder and the linter every quarter against the new 4-quarter rolling deal corpus. Cells where observed NRR < `target_nrr` are flagged for review.

## Scripts

| Script | Purpose | Industry profiles |
|---|---|---|
| `scripts/discount_matrix_builder.py` | 4-dim data-backed matrix with approver tiers + margin floors | saas, enterprise-software, api, marketplace, services |
| `scripts/exception_router.py` | Routes exception requests with compensating commitments + audit trail | n/a (matrix-driven) |
| `scripts/policy_linter.py` | 10-rule lint pass over the matrix | n/a (deterministic across profiles) |

All three: stdlib-only, `--help`, `--sample`, `--input <json>`, `--output {markdown,json}`.

## References

- `references/discount_governance_canon.md` — Discount governance evidence base: OpenView Partners benchmarks, David Skok (For Entrepreneurs) discount math, Tomasz Tunguz on discount distribution, Bessemer State of the Cloud, KeyBanc Capital Markets SaaS Survey, Bridge Group AE-compensation research, RevOps Co-op playbooks, Forrester deal-desk research. 8 sources.
- `references/policy_design_canon.md` — Policy-as-artifact design: SaaStr (Jason Lemkin), Winning by Design (Jacco van der Kooij) on commercial discipline, Forrester deal-desk maturity research, MIT Sloan on incentive-system gaming, McKinsey on commercial-policy effectiveness, Bain *Pricing Power*, Salesforce CPQ implementation guides. 7 sources.
- `references/policy_anti_patterns.md` — 8 named anti-patterns with sourced studies + countermeasures + lint-rule mapping: precedent-sets-policy, no-data-backing, no-compensating-commitments, approver/margin misalignment, no audit trail, cliff edges, undefined "strategic value", no quarterly review. 8 sources.

## Assumptions

- The skill assumes the **pricing model and list price already exist** (set via `commercial/skills/pricing-strategist`). Commercial-policy governs **discounts off list** — it does not set list.
- The CFO owns the `min_margin_pct` constraint (margin floor). The CRO / Head of Deal Desk owns the `max_discount_pct_without_exception` constraint (band cap). The skill keeps these inputs separate by design (per Bain *Pricing Power* — mixing accountability is the most common cause of policy drift).
- Industry profiles bake in *customary* band widths. Companies with idiosyncratic economics should pass overrides via the input JSON.
- The matrix is data-backed but **not data-driven**: the band is set by the constraints + profile; observed data is annotation that tells you whether the cell is performing. If observed NRR < target, that's a signal to **review the band**, not to keep discounting deeper.
- "Strategic value" tiers (`logo`, `expansion`, `lighthouse`) are useful only if defined with concrete tests. The lint rule L06 enforces this.
- This is a policy-design skill, not a deal-approval skill. It never says "approve" — it produces the matrix + exception flow that **deal-desk** then applies.

## Anti-patterns

- **Setting discount bands without data backing.** "VP Sales argued for it in a Slack thread" is not data backing. If you can't show win-rate and NRR for the band, the band is rhetoric. (Caught by `data_backing` per cell + lint L08.)
- **Letting precedent set policy.** "Maria approved 28% on Acme last quarter" is not a band — it's an exception that didn't break the policy. `exception_router.py` flags 3+ similar exceptions as a signal that **the matrix is wrong**, not the deal. (Anti-pattern AP-1.)
- **Approving exceptions without compensating commitments.** Discount-for-nothing is a leak (Winning by Design). Every exception severity band requires non-negotiable commitments. (`exception_router.COMPENSATING_LIBRARY`.)
- **Cliff edges at round-number ARR thresholds.** A hard $100K threshold produces deal-size gaming within 2 quarters (MIT Sloan agency theory). Smooth the gradient. (Lint L05.)
- **"Strategic value" as an undefined catch-all.** If "strategic" is undefined, within a quarter 60% of deals will be flagged strategic and the matrix is dead. Define with concrete tests. (Lint L06.)
- **No quarterly review.** Markets shift; matrices unchanged for 12 months are mispriced. Re-run the builder and linter every quarter. (Anti-pattern AP-8.)
- **Mixing CFO and CRO accountabilities.** CFO owns the margin floor; CRO owns the band cap. Same accountable owner = predictable drift toward whatever they're compensated on (Bain *Pricing Power*).
- **Skipping the lint pass before publishing.** BLOCKER findings (approver inversion, margin-floor violation, inverted bands) make the policy unsignable. Lint is the gate, not the after-action review.

## Distinct from

| Sibling | Scope | Difference |
|---|---|---|
| `commercial/skills/deal-desk` | **Applies** the policy to one deal at a time | Commercial-policy **designs the policy itself**. Deal-desk consumes the matrix; commercial-policy produces it. |
| `commercial/skills/pricing-strategist` | Sets pricing **model** (per-seat / usage / value / tiered) + **list price** | Commercial-policy governs **discounts off list**. Pricing-strategist sets the menu; commercial-policy governs the menu's discount discipline. |
| `c-level-advisor/cro-advisor` | Strategic CRO judgment ("when do we hire VP Sales?", "is our motion product-led or sales-led?") | Strategic, not operational. Commercial-policy is the artifact CRO commissions; it isn't CRO judgment itself. |
| `c-level-advisor/cfo-advisor` | Margin floor + unit-economics judgment | The CFO supplies `min_margin_pct` to commercial-policy as an input. Commercial-policy **operationalizes** the CFO's constraint as per-cell margin floors. |
| `business-growth/contract-and-proposal-writer` | Authors proposal/SOW/MSA **prose** | Commercial-policy emits structured matrix + audit-trail JSON, not customer-facing prose. |

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-commercial` or the Commercial orchestrator before the skill runs. Recommended answer + canon citation per question. Never bundled.

1. **"What's your observed discount distribution across the last 4 quarters — and is the median inside or outside your current matrix?"**
   Recommended: pull the corpus before designing any band. If the observed median is outside the matrix, the matrix is rhetoric.
   Canon: OpenView SaaS Benchmarks; RevOps Co-op playbooks. Anti-pattern AP-2.

2. **"What's the win-rate AND the 12-month NRR for deals at your current 'max discount' band?"**
   Recommended: both, not one. A band with high win-rate but low NRR is buying logos with leaky-bucket retention. Tunguz benchmarks: top-NRR-quartile companies discount 6 pts less than bottom quartile.
   Canon: Tomasz Tunguz; Bessemer State of the Cloud.

3. **"Who at the company owns the margin floor, AND who owns the discount-band cap — are those the same person?"**
   Recommended: CFO owns floor; CRO/Head of Deal Desk owns cap. Same owner = drift toward what they're compensated on.
   Canon: Bain *Pricing Power* — separation of accountability is the structural fix. Anti-pattern AP-4.

4. **"How is 'strategic value' defined in your current policy — with concrete tests, or with adjectives?"**
   Recommended: concrete tests. "Top-20 named account in 2026 target list" is a test; "important customer" is not.
   Canon: SaaStr (Lemkin); Forrester deal-desk research. Lint rule L06. Anti-pattern AP-7.

5. **"For exceptions above your matrix max, what compensating commitments are required — and are they in writing before the approver signs?"**
   Recommended: minimum multi-year prepay + named expansion path; deeper exceptions require reference commitment + MSA tightening + executive sponsor.
   Canon: Winning by Design (van der Kooij); McKinsey B2B pricing studies. Anti-pattern AP-3.

6. **"Has the same kind of exception been approved 3+ times in the trailing quarter — and if so, is the matrix wrong?"**
   Recommended: 3+ similar exceptions means the band is mispriced. Rebuild the matrix; don't keep approving exceptions.
   Canon: OpenView discount drift studies; `exception_router._precedent_risk`. Anti-pattern AP-1.

7. **"When was the last time you re-ran the matrix against the previous 4 quarters of data?"**
   Recommended: quarterly. Annual review is too slow; the disciplined cohort revises quarterly.
   Canon: OpenView benchmarks; RevOps Co-op. Anti-pattern AP-8.

8. **"For every exception in the last quarter, is there a machine-readable audit-trail record — or is the approval in Slack and email?"**
   Recommended: structured record in CPQ or equivalent. Slack/email approvals don't survive year-2 renewal negotiations.
   Canon: Salesforce CPQ best practices; Forrester deal-desk maturity research. Anti-pattern AP-5.

Walk depth-first. Lock 1-4 before opening 5-8. After all 8 are answered, invoke `discount_matrix_builder.py` → `policy_linter.py` → `exception_router.py --sample` in sequence to produce the policy artifact.

## Quick examples

```bash
# Design the matrix
python3 scripts/discount_matrix_builder.py --sample
python3 scripts/discount_matrix_builder.py --input policy_intake.json --profile saas --output json > matrix.json

# Lint the matrix
python3 scripts/policy_linter.py --sample
python3 scripts/policy_linter.py --input matrix.json

# Walk the exception flow
python3 scripts/exception_router.py --sample
python3 scripts/exception_router.py --input request.json --output json
```

The sample matrix lints to **FAIL** with 4 BLOCKERs + 6 MAJORs + 2 MINORs — by design, to exercise every rule path. A real policy intake should lint to PASS or PASS_WITH_WARNINGS. The sample exception (42% on a $320K logo deal) routes to AE → Sales Manager → Director → VP Sales with 3 required compensating commitments (multi-year 36mo, prepay, named expansion path).
