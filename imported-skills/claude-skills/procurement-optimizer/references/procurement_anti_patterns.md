# Procurement Anti-Patterns

A field guide to the most common procurement mistakes — drawn from A.T. Kearney's maverick-spend research, IACCM/WorldCC contract studies, McKinsey's category strategy commentary, Hackett purchasing-cycle research, BCG's supplier-consolidation post-mortems, Spend Matters' analyses of failed rationalization initiatives, and ISM (Institute for Supply Management) procurement maturity studies.

Use this file before running any tool. Most "spend audits" produce a beautiful slide deck that triggers a consolidation initiative that destroys 30-50% of the theoretical savings. Read these first.

---

## Sources (≥ 7)

1. **A.T. Kearney — Maverick spend research** (AEP studies, multi-year)
2. **IACCM / WorldCC — *State of Contract and Commercial Management***
3. **McKinsey — *The CPO Agenda* and category strategy commentary**
4. **Hackett Group — *Procurement Performance Study*** (annual benchmarks)
5. **BCG — Supplier consolidation case studies and *The CPO Agenda***
6. **Spend Matters — Failed rationalization analyses** (Pierre Mitchell, Jason Busch)
7. **ISM (Institute for Supply Management) — *Manage Indirect Spending* and lessons-learned studies**
8. **Productiv / Zylo / Vendr / Tropic — SaaS-specific anti-patterns** (cross-referenced from `saas_management_canon.md`)

---

## Anti-pattern 1: Consolidate to single-source for a tier-1 critical category

**Pattern.** You have three monitoring tools. You consolidate to one. The new sole vendor has a major outage three months in. You have no break-glass plan because you offboarded the other two tools to capture the savings. Engineering is flying blind for 6 hours.

**Why it happens.** Savings math is easy and visible. Operational risk is intangible and unmeasured. The CFO incentive points one direction.

**Fix.** Before consolidating any tier-1 category, document a 72-hour break-glass plan: which alternative do you switch to, who executes the switch, what's the SLA expectation, where's the contractual fallback. The skill's `supplier_consolidation.py` refuses to recommend tier-1 consolidation without the `break_glass_documented: true` flag in the input.

**Canon.** BCG supplier-consolidation case studies (multi-year retrospectives show 30-50% of theoretical savings disappear due to operational disruption). NotPetya / M.E.Doc and SolarWinds supply-chain attack lessons.

---

## Anti-pattern 2: Categorize by vendor name, not by what's purchased

**Pattern.** You categorize Workday as "HR Software." But you also licensed the financial planning module — that's Finance Software. Your category Pareto now mis-attributes $400k of Finance spend to HR.

**Why it happens.** Vendor name is easy. Line-item description requires reading every entry.

**Fix.** Categorize from the line-item `description` and `category_hint`, not the supplier. The skill's `spend_categorizer.py` ranks `description` and `category_hint` ahead of `supplier` in keyword matching.

**Canon.** Pierre Mitchell / Spend Matters — *Category strategy mechanics*. UNSPSC categorization principle: classify the good/service, not the provider.

---

## Anti-pattern 3: Ignore renewal-date clustering

**Pattern.** Twelve tier-2 SaaS contracts all renew in March. You go into the negotiation cycle simultaneously, with three weeks to renegotiate twelve contracts. You auto-renew nine of them because you ran out of bandwidth.

**Why it happens.** Renewals piled up over years of unmonitored procurement. Nobody saw it because nobody built the calendar.

**Fix.** Build a renewal calendar (the skill outputs this). At each next renewal, negotiate term length deliberately (18-month, 6-month, 12-month rotation) to permanently spread the calendar across the year.

**Canon.** IACCM/WorldCC contract studies — 60-80% of contracts auto-renew without review. Vendr SaaS Buyers Report — quarter-end and year-end discounts are real, but only if you have negotiation bandwidth.

---

## Anti-pattern 4: Approve-by-default for sub-$5k spend (death by a thousand SaaS)

**Pattern.** Approval workflow requires CFO sign-off for $5k+ purchases. Below that, any manager can approve. Result: 80 SaaS subscriptions each costing $2-4k/year, totaling $250k of unmonitored spend that grows 50% YoY.

**Why it happens.** Approval thresholds are usually set once (often at company founding) and never re-tuned.

**Fix.** Tighten the sub-$5k threshold — but only for net-new SaaS, not for renewals of catalog items. Require a single owner for "death-by-a-thousand-SaaS" risk (typically the BizOps lead or a SaaS-management platform). The skill's `spend_categorizer.py` surfaces "small-spend, many-supplier" clusters explicitly.

**Canon.** A.T. Kearney maverick-spend research (10-40% of indirect spend leaks through sub-threshold purchases). BetterCloud State of SaaSOps — sub-$5k is the dominant shadow-IT entry point.

---

## Anti-pattern 5: No quarterly renewal review (annual is too slow)

**Pattern.** You do an "annual SaaS audit" every January. Between January and December, 30 new subscriptions get added, 12 grow >50%, and 8 auto-renew before you re-review them.

**Why it happens.** Annual reviews feel sufficient. They're not for SaaS, which is continuously renewing across the year.

**Fix.** Quarterly category review for tier-1 and tier-2 categories. Annual deep audit for tier-3 (low-spend, non-critical).

**Canon.** Forrester SaaS Portfolio Management — three-tier governance with quarterly cadence for high-tier categories. Hackett — world-class procurement reviews categories on a rolling quarterly basis.

---

## Anti-pattern 6: Rationalize without measuring switching cost

**Pattern.** You identify three monitoring tools costing $315k/year. You decide to consolidate to one tool costing $180k. Theoretical savings: $135k. Actual cost of migration (training, integration rework, alert re-tuning, parallel-run period): $200k. Net Y1 result: lost money.

**Why it happens.** Savings are visible (line-item subtraction). Switching cost is invisible (engineering time, parallel-run period, training).

**Fix.** Estimate switching cost explicitly for every consolidation. Sum across all losers in the cluster. Net Y1 savings = annual savings − migration cost. The skill's `supplier_consolidation.py` does this and flags `LOW_SAVINGS` for clusters where net Y1 < $10k.

**Canon.** BCG supplier-consolidation post-mortems. Tropic analysis of failed SaaS consolidations (60%+ failure rate to capture theoretical savings).

---

## Anti-pattern 7: Consolidate based on price alone, ignoring integration debt

**Pattern.** You consolidate to the cheapest monitoring tool. It doesn't integrate with your data warehouse or your incident management platform. You rebuild the integration plumbing for 6 months. The "cheaper" tool ends up costing more.

**Why it happens.** Price is easy to compare. Integration depth is hard to score.

**Fix.** Score `integration_count_with_other_systems` as a winner-selection input, not just price. The skill's `pick_winner` function uses integration count as the primary tiebreaker for tier-2/3 clusters.

**Canon.** Spend Matters — *Total Cost of Ownership in procurement decisions*. McKinsey — category strategy mistakes (price-only thinking is the most common error).

---

## Anti-pattern 8: Treat shadow IT spend as marketing's (or any other department's) problem

**Pattern.** Marketing has 14 unmonitored SaaS subscriptions. Procurement says "that's marketing's problem." Marketing says "we don't have the procurement bandwidth to manage that." Nobody owns it.

**Why it happens.** Shadow IT lives in expense reports and corporate-card transactions, which procurement doesn't see. Department heads see it but lack procurement skills.

**Fix.** Procurement owns the audit, even of departmental spend. A SaaS-management platform (or expense-platform integration) discovers shadow subscriptions. The Productiv finding (47% of SaaS spend is shadow) is the size of the prize.

**Canon.** Productiv State of SaaS (47% shadow IT). Zylo SaaS Management Index (marketing and engineering are the top two shadow-IT entry points).

---

## Anti-pattern 9: Negotiate without a BATNA (Best Alternative To Negotiated Agreement)

**Pattern.** You go into renewal with your monitoring vendor without having priced any alternative. The vendor knows you have no BATNA. You get 5% off list because you have no leverage.

**Why it happens.** Pricing alternatives takes time and feels confrontational.

**Fix.** Before any renewal worth $50k+, get a competitive quote — even a non-serious one. The existence of an alternative changes the negotiation tone.

**Canon.** Vendr SaaS Buyers Report on negotiation leverage. McKinsey — category strategy requires a credible threat of substitution. Tropic per-category pricing benchmarks provide the BATNA when you can't get a live quote.

---

## Anti-pattern 10: Skip the offboarding checklist when consolidating

**Pattern.** You consolidate three monitoring tools to one. Six months later, you discover the offboarded tools still have your data, still have active API keys, and one of them quietly auto-renewed because the offboarding paperwork was never filed.

**Why it happens.** Consolidation projects celebrate the new tool going live; offboarding the old tools is treated as paperwork.

**Fix.** Offboarding checklist per loser: cancel auto-renew, delete data, revoke API keys, rotate any shared credentials, confirm final invoice. The skill's `supplier_consolidation.py` outputs an explicit "Offboard:" list per cluster.

**Canon.** BetterCloud SaaS Operations on offboarding gaps. SolarWinds + Okta breach lessons on lingering vendor access.

---

## How this skill defends against the anti-patterns

| Anti-pattern | Skill defense |
|---|---|
| Single-source tier-1 | `supplier_consolidation.py` hard refusal without `break_glass_documented: true` |
| Categorize by vendor | `spend_categorizer.py` reads description + category_hint, not just supplier |
| Renewal clustering | `supplier_consolidation.py` flags months with ≥ 3 simultaneous renewals |
| Sub-$5k death | `spend_categorizer.py` surfaces small-spend many-supplier clusters |
| Annual is too slow | Forcing-question library asks about quarterly cadence |
| Ignore switching cost | `supplier_consolidation.py` requires `switching_cost_estimate`; net Y1 = savings − migration |
| Price-only consolidation | `supplier_consolidation.py` weights `integration_count_with_other_systems` in winner selection |
| Shadow IT is "marketing's problem" | Forcing-question library asks who owns sub-$5k SaaS |
| No BATNA | Forcing-question library asks about competitive quotes before renewal |
| Skip offboarding | `supplier_consolidation.py` outputs explicit Offboard list per cluster |
