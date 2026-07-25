# R&D Program Finance Canon

Reference for the accounting and budgeting rules that govern internal R&D spend. Pairs with `program_budget_planner.py` and `capex_vs_opex_router.py`.

## The central question: research vs development

The accounting treatment of R&D hinges on a phase distinction that the two major frameworks handle differently:

- **IFRS (IAS 38)** — *Research* costs are always **expensed**. *Development* costs **must be capitalized** once all six conditions are met: (1) technical feasibility, (2) intention to complete, (3) ability to use or sell, (4) probable future economic benefit, (5) adequate resources to complete, (6) reliable measurement of expenditure. This is not optional under IFRS — if the criteria are met, capitalization is required.
- **US GAAP (ASC 730)** — R&D is **expensed as incurred**, full stop, with narrow exceptions. The main exception is software: **ASC 985-20** (software to be sold) capitalizes costs after *technological feasibility*; **ASC 350-40** (internal-use software) capitalizes during the application-development stage.

This divergence is why the router takes a `--standard {ifrs,usgaap}` flag: the same cost item can be EXPENSE under US GAAP and CAPITALIZE-CANDIDATE under IFRS.

## F&A / indirect cost (the budgeting half)

Direct costs are traceable to the program (personnel, supplies). **Facilities & Administrative (F&A)**, a.k.a. indirect or overhead, covers shared costs (building, utilities, administration). For federally funded research, F&A is governed by **Uniform Guidance (2 CFR 200)**: organizations negotiate a rate (the NICRA — Negotiated Indirect Cost Rate Agreement) or use the **de minimis 10%** rate. F&A applies to the **Modified Total Direct Cost (MTDC)** base, which *excludes* capital equipment, the portion of each subaward over $25,000, tuition, and patient-care costs. The budget planner enforces this MTDC exclusion.

## Why disclosure matters

A budget number is only as trustworthy as its rate basis and escalation assumption. Two budgets for the same program can differ 40%+ purely on the F&A rate and the base. Every output of the planner ships an assumptions block for exactly this reason.

## Sources

1. IAS 38, *Intangible Assets* — IASB (research vs development, paragraphs 54-67).
2. FASB ASC 730, *Research and Development*; ASC 985-20, *Software — Costs of Software to Be Sold, Leased, or Marketed*; ASC 350-40, *Internal-Use Software*.
3. 2 CFR 200 (Uniform Guidance), Subpart E — Cost Principles, esp. §200.414 (Indirect F&A costs) and the MTDC definition (§200.1).
4. Cost Accounting Standards (CAS), 48 CFR 9904 — for federally funded R&D contractors.
5. KPMG / PwC / Deloitte IFRS-vs-US-GAAP comparison guides (R&D and intangibles chapters).
6. AICPA Accounting & Valuation Guide, *Research and Development*.
