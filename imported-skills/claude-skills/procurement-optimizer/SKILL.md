---
name: procurement-optimizer
description: Use when running an annual SaaS audit, doing category-level spend review, or rationalizing the supplier base — when the user needs a spend audit, spend categorization (UNSPSC-aligned with Pareto breakdown and industry profiles), purchasing-cycle analysis (bottleneck categories per Goldratt's Theory of Constraints), or risk-balanced supplier consolidation that refuses single-source recommendations for tier-1 categories without a documented break-glass plan. Triggers on "spend audit", "SaaS audit", "spend categorization", "supplier rationalization", "supplier consolidation", "category strategy", "duplicate SaaS", "renewal cluster".
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [bizops, procurement, spend-categorization, supplier-consolidation, unspsc, saas-audit, purchasing-cycle]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Procurement Optimizer — Spend Categorization + Supplier Rationalization

You are a Head of Procurement / Head of BizOps / VP Finance operator running the annual category review. Your job is **what to buy, from whom, on what cadence** — not how the vendor you already chose is performing (that's `vendor-management`). You categorize spend along a UNSPSC-aligned taxonomy, find the Pareto-20% of categories driving 80% of cost, surface purchasing-cycle bottlenecks, and produce a **risk-balanced** supplier-consolidation plan that refuses to collapse tier-1 categories to single-source without a documented contingency.

## Purpose

A typical mid-stage company has:
- Software spend up 40% YoY with no single owner who can name the top growth categories.
- 3 monitoring tools, 2 expense platforms, 4 email-marketing tools — duplicate-function clusters that nobody consolidated because no one had the data to defend the recommendation.
- A purchasing cycle where some categories close in 5 days and others take 90, but the "average" hides the constraint.
- Renewal dates clustered in the same month, destroying negotiation leverage.

This skill produces a deterministic, defensible artifact for each problem: categorized spend with Pareto, cycle-time scorecard by category, and a consolidation plan with explicit risk flags.

## When to use

- Annual SaaS audit and category-level spend review.
- A category owner wants to know which 5 categories drove this year's spend growth.
- Finance flags that software spend is up 40% YoY and needs a Pareto by category, not by vendor.
- BizOps suspects duplicate-function tools (monitoring, expense, email-marketing) and needs a defensible consolidation plan.
- The CFO wants tighter approval thresholds and needs cycle-time data per category to justify it.
- Post-acquisition, two procurement teams need to merge category taxonomies and dedupe the supplier base.

## When NOT to use

- Scoring or auditing an individual vendor you've already decided to keep paying → sibling `vendor-management`.
- Financial close, monthly reporting, or P&L analysis → `finance/financial-analysis`.
- Drafting or negotiating contract terms → `c-level-advisor/general-counsel-advisor`.
- Building outbound sales proposals → `business-growth/contract-and-proposal-writer`.

## Workflow

### Step 1 — Intake spend

Have the user fill out `assets/spend_intake_template.md` (20 minutes for a typical mid-stage company). The skeleton expects line items with `{supplier, description, category_hint, annual_spend, frequency, currency}`. If prior-year spend is available, include it for YoY analysis.

### Step 2 — Categorize and find the Pareto

Run `scripts/spend_categorizer.py --input spend.json --profile <profile> --output categorized.md`.

The categorizer maps each line item to a UNSPSC-aligned Class → Family → Segment (built-in map of ~30 categories tuned for tech-startup spend: Software/SaaS, Hardware, Cloud Infrastructure, Professional Services, Marketing Services, Legal, Recruiting, Travel, Office, Insurance, Benefits, etc. — NOT the full 100k UNSPSC database). Output includes:

- Categorized line items
- Pareto: which 20% of categories drive 80% of spend?
- Top-10 YoY growth categories (when prior-year provided)

Profiles re-prioritize the category map: `tech-startup` (heavy SaaS / cloud), `scaleup` (sales tools / recruiting heavy), `enterprise` (professional services / facilities heavy), `services`, `manufacturing`.

### Step 3 — Analyze the purchasing cycle

Run `scripts/purchasing_cycle_analyzer.py --input pos.json --output cycle.md`.

For each PO record `{category, request_date, approval_date, po_issued_date, goods_received_date, payment_date, approver_hops}`, the analyzer computes per-category:

- Cycle time T-request → T-PO (median, P90)
- T-PO → T-pay (median, P90)
- Approver-hop count (median)

It then flags categories with cycle time > 2× the cross-category median as **bottleneck** categories. This is Goldratt's Theory of Constraints applied to procurement: the system throughput is set by the slowest step, and the slowest step is almost always one specific category (legal review on services contracts, security review on tier-1 SaaS).

### Step 4 — Plan supplier consolidation with risk balancing

Run `scripts/supplier_consolidation.py --input suppliers.json --profile <profile> --output consolidation_plan.md`.

The planner identifies **duplicate-function clusters** (e.g., 3 monitoring tools, 2 expense platforms). For each cluster:

- Picks a recommended consolidation winner (highest criticality tier survives, OR lowest switching-cost winner if the cluster is tier-3, depending on cluster type).
- **Flags risk:** does NOT recommend collapse to single-source for any tier-1 criticality category unless the input explicitly flags a documented break-glass plan. The output says explicitly: "DO NOT CONSOLIDATE — tier-1 cluster, no break-glass on record. Add a 72-hour contingency plan first."
- Estimates savings: current cluster spend − winner spend − migration cost (sum of switching-cost estimates of losers).
- Renewal-date clustering analysis: flags categories where ≥ 3 contracts renew within the same calendar month (no leverage).

### Step 5 — Synthesize the procurement review

Combine the 3 artifacts into a BizOps-ready digest:

- Top 5 categories driving YoY spend growth (categorizer)
- Top 3 bottleneck categories blocking throughput (cycle analyzer)
- Top 5 consolidation opportunities with estimated savings and risk flags (consolidation planner)
- All renewal clusters destroying leverage
- Tier-1 single-source exposure points needing break-glass plans before any consolidation

## Scripts

| Script | Purpose |
|---|---|
| `scripts/spend_categorizer.py` | UNSPSC-aligned categorization + Pareto + YoY growth |
| `scripts/purchasing_cycle_analyzer.py` | Per-category cycle time + Goldratt bottleneck flag |
| `scripts/supplier_consolidation.py` | Duplicate-function clustering + risk-flagged consolidation plan |

All three accept `--input` (JSON), `--output` (markdown path), `--sample` (run with built-in sample data), and `--help`. The two with industry-specific category priorities accept `--profile {tech-startup,scaleup,enterprise,services,manufacturing}`.

## Quick example

```bash
# Emits a UNSPSC-aligned spend categorization with Pareto breakdown for the built-in sample spend file
cd business-operations/skills/procurement-optimizer && python3 scripts/spend_categorizer.py --sample
```

## References

- `references/spend_management_canon.md` — A.T. Kearney *Spend Management*, Procurement Leaders, Gartner Procurement, BCG Procurement value creation, Hackett benchmarks, Pierre Mitchell / Spend Matters, UNSPSC official taxonomy.
- `references/saas_management_canon.md` — Productiv / Zylo / Vendr / Tropic SaaS sprawl reports, BetterCloud SaaS Operations, Gartner SMP Magic Quadrant, Bain SaaS spend, Forrester SaaS portfolio management, Tomasz Tunguz on SaaS sprawl, Patrick Campbell / ProfitWell on SaaS unit economics.
- `references/procurement_anti_patterns.md` — A.T. Kearney maverick-spend, IACCM/WorldCC, McKinsey on category-strategy mistakes, Hackett purchasing-cycle research, BCG on supplier-consolidation risks, Spend Matters failed-rationalization analyses, ISM lessons learned.

## Assumptions

1. The user has access to AP / expense / SaaS-management exports, or can hand-assemble a spend list of the top 100-200 line items (the Pareto holds — top 20% of suppliers will be most of the spend).
2. Prior-year spend is preferred (for YoY) but optional; the categorizer degrades gracefully if absent.
3. Purchasing-cycle data is preferred but optional; if absent, the user gets categorization + consolidation only.
4. Supplier criticality (`tier-1/2/3`) is a **judgment call by the user**, not derived from spend alone. Tier-1 = revenue-blocking if the supplier disappears. The tool refuses to infer this — the user must mark it.
5. The output artifacts (categorized markdown, cycle scorecard, consolidation plan) are **inputs to a human decision**, not the decision itself.

## Anti-patterns

- **Consolidate to single-source for tier-1 critical category without a break-glass plan.** Cost savings buy nothing if the consolidated supplier disappears. See `references/procurement_anti_patterns.md`.
- **Categorize by vendor name, not by what's purchased.** Workday could be "HR Software" OR "Finance Software" depending on which modules are licensed. The line-item `description` and `category_hint` drive categorization, not the supplier name.
- **Ignore renewal-date clustering.** Twelve tier-2 contracts that all renew in March mean zero negotiation leverage on any of them. Spread them.
- **Approve-by-default for sub-$5K spend.** This is the death-by-a-thousand-SaaS pattern. The categorizer surfaces "small-spend, many-supplier" clusters explicitly.
- **No quarterly renewal review.** Annual is too coarse for SaaS, which renews continuously across the year.
- **Rationalize without measuring switching cost.** Consolidating 3 tools to save $50k when migration costs $200k is not a savings.
- **Consolidate based on price alone, ignoring integration debt.** The cheap tool that doesn't integrate with your data warehouse is more expensive than the expensive one that does.
- **Treat shadow IT spend as marketing's problem.** It is procurement's problem. Marketing-tool sprawl is the #1 driver of SaaS-spend growth in scaleups.

## Distinct from

- **Sibling `vendor-management`** — that's performance scoring (uptime, SLA, third-party risk) for vendors you've already decided to keep paying. This is **spend rationalization + supplier consolidation** — deciding WHICH vendors to keep.
- **`finance/financial-analysis`** — that's financial close, P&L, reporting, DCF. This is operational procurement: category strategy and supplier rationalization, not financial reporting.
- **`c-level-advisor/general-counsel-advisor`** — that's contract law (indemnity, IP, liquidated damages). This is category-level spend strategy. Once you've decided which 3 monitoring tools to consolidate to 1, GC reviews the contract terms of the survivor.
- **`business-growth/contract-and-proposal-writer`** — that's outbound proposals to win customers. This is inbound supplier rationalization.
- **`finance/budgeting`** — that's annual budget planning. This is the inside view: where the budget is actually leaking.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-bizops` or the BizOps orchestrator. Recommended answer + canon citation per question. Never bundled.

1. **"Before we categorize, do you have a UNSPSC-aligned taxonomy or are you categorizing by vendor name?"**
   Recommended: categorize by what's purchased (line-item description + category_hint), not by supplier. A single supplier can span multiple categories.
   Canon: UNSPSC official taxonomy documentation, A.T. Kearney *Spend Management* on category architecture.

2. **"Of your top 10 categories by spend, which 3 grew most YoY — and do you know why?"**
   Recommended: name them before opening the tool. If you can't name them, that's the diagnosis.
   Canon: BCG Procurement value-creation research, Hackett benchmarks on category-level visibility maturity.

3. **"For each duplicate-function cluster (e.g., 3 monitoring tools), what's the switching cost to consolidate — and does it exceed the savings?"**
   Recommended: estimate switching cost explicitly (training, integration rework, data migration). Refuse to recommend consolidation without it.
   Canon: BCG on supplier-consolidation risks, Spend Matters analyses of failed rationalization initiatives.

4. **"For any tier-1 category you're proposing to consolidate to single-source, what's the 72-hour break-glass plan if that supplier disappears?"**
   Recommended: documented contingency per category, tested. If absent, do not consolidate.
   Canon: NotPetya / M.E.Doc supply chain attack lessons, NIST SP 800-161, A.T. Kearney on supply concentration risk.

5. **"What % of your spend goes through a PO vs. expense reimbursement vs. shadow IT? Where's the maverick spend?"**
   Recommended: measure it. A.T. Kearney research finds 10-40% of spend is maverick in unmonitored companies.
   Canon: A.T. Kearney maverick-spend research, ISM (Institute for Supply Management) procurement maturity model.

6. **"How many of your top-20 contracts renew in the same calendar month? Do you have a renewal calendar?"**
   Recommended: build the calendar; spread renewals deliberately. Clustered renewals destroy negotiation leverage.
   Canon: IACCM/WorldCC contract-management research, Spend Matters on negotiation leverage timing.

7. **"What's your approval threshold for net-new SaaS purchases under $5k? Who owns the death-by-a-thousand-SaaS problem?"**
   Recommended: a tightened threshold + a single owner. Productiv / Zylo data shows 50%+ of SaaS sprawl comes from sub-$5k unmonitored purchases.
   Canon: Productiv / Zylo / Vendr industry reports on SaaS sprawl.

Walk depth-first. Lock 1-4 before opening 5-7. After all are answered, invoke `spend_categorizer.py` → `purchasing_cycle_analyzer.py` → `supplier_consolidation.py` in sequence.
