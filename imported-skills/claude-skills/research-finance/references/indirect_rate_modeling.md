# Indirect (F&A) Rate Modeling

Deep reference for the F&A rate — the single most error-prone input in an R&D budget. Pairs with `program_budget_planner.py`.

## What the F&A rate actually is

The F&A rate recovers shared costs that cannot be traced to a single program. It is composed of two pools:

- **Facilities** — depreciation on buildings and equipment, interest on facility debt, operations & maintenance, library, utilities.
- **Administration** — general administration, departmental administration, sponsored-projects administration, student services (in universities).

The rate is computed as (indirect pool ÷ allocation base) and applied to that base on each program.

## The base matters as much as the rate

A 55% rate on a $1M total budget is *not* $550k of F&A — because the rate applies only to the **MTDC base**, which excludes:

- Capital equipment (typically items > $5,000 with > 1-year life)
- The portion of **each** subaward exceeding $25,000 (the first $25k is in the base; the rest is exempt)
- Tuition remission
- Patient-care costs
- Rental of off-site facilities, scholarships, participant support

So a budget heavy in equipment and large subawards has a much smaller F&A base than its headline total. The planner models this exclusion explicitly.

## Negotiated vs de minimis

- **NICRA** — the Negotiated Indirect Cost Rate Agreement, established with a cognizant federal agency. This is the authoritative rate for federally funded work.
- **De minimis 10%** — under 2 CFR 200.414(f), an entity that has never had a negotiated rate may elect a flat 10% of MTDC. Simpler, almost always lower than a negotiated research rate.

## Fringe and the loading stack

Personnel costs load in layers: base salary → **fringe** (benefits, often 25-35%) → then F&A applies to salary+fringe (both are in the MTDC base). Modeling fringe separately from F&A avoids double counting or under-recovery.

## Sources

1. 2 CFR 200.414, *Indirect (F&A) costs*, and Appendix III (IHEs) / Appendix IV (nonprofits).
2. 2 CFR 200.1, definition of *Modified Total Direct Cost (MTDC)*.
3. NIH Grants Policy Statement, indirect-cost chapter; DHHS Cost Allocation Services NICRA guidance.
4. Cost Accounting Standards Board, 48 CFR 9904 (CAS 410, 418 on allocation).
5. COGR (Council on Governmental Relations), *Indirect Cost / F&A* primers and white papers.
6. Federal Demonstration Partnership materials on subaward and MTDC treatment.
