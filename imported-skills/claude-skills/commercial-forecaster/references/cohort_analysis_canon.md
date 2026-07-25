# Cohort Analysis Canon

Source material behind `cohort_arr_projector.py`'s NRR/GRR projection and the leaky-cohort callout.

## Core principle

A consolidated NRR number is an **ARR-weighted average that hides 5-15 percentage points of
dispersion across cohorts**. The consolidated number lags the underlying leak by 2-3 quarters
because (a) larger / older cohorts dominate the weighted average and (b) leaks compound silently.

The skill flags any cohort whose mean NRR falls ≥ 5 pp below the trailing-cohort average — that
is the level at which the leak is signal, not noise.

---

## Why cohort decomposition matters

Imagine four cohorts:

| Cohort | Starting ARR | Mean NRR Q1-Q4 |
|---|---:|---:|
| 2025-Q1 | $1.2M | 100% |
| 2025-Q2 | $1.5M | 100% |
| 2025-Q3 | $1.8M | 101% |
| 2025-Q4 | $2.1M | **85%** |

The consolidated ARR-weighted NRR for Q+1 looks roughly: (1.2×100 + 1.5×100 + 1.8×101 + 2.1×85) / 6.6
= ~95%. **That looks fine.** It even looks reasonable for a SaaS company.

But the 2025-Q4 cohort is bleeding 15pp below the trailing cohorts. Two quarters from now, when that
cohort becomes the dominant weight (because it was the largest), the consolidated number will collapse
to ~85%. The CFO who didn't see this coming will be unhappy.

This is why the consolidated number is a **lagging indicator** and the cohort heatmap is the
**forensic tool**.

---

## NRR vs. GRR — definitions used by this skill

- **GRR (Gross Retention Rate)** — the percentage of starting ARR retained in a cohort, excluding
  expansion. Ceiling is 100%. Anything < 100% is churn + contraction.
- **NRR (Net Retention Rate)** — GRR + expansion ARR. Can exceed 100% when expansion outpaces
  churn. The "best in SaaS" number.
- **Per-cohort projection** — for each cohort, project NRR and GRR forward over the horizon using
  per-quarter retention and expansion inputs (or the default curve when missing).
- **Consolidated** — ARR-weighted average across cohorts per quarter.

---

## Source register (≥ 7 cited)

### 1. Andrew Chen — a16z (andrewchen.com)

The canonical introduction to cohort retention curves:
- The "smiling curve" (retention dips then recovers) is the rare healthy pattern; most products
  produce a "frowning curve" that hides in averages
- Cohort decomposition is the discipline that catches a product/market-fit erosion 2 quarters
  before NPS or aggregate retention does

### 2. Brian Balfour — Reforge (brianbalfour.com)

The retention-driven growth framework:
- "Retention is the single most underrated lever in growth math"
- Cohorts must be decomposed by acquisition source, persona, and pricing tier — a single cohort
  variable is insufficient
- Expansion-driven NRR > 110% requires structural product loops, not just sales motion

### 3. David Skok — *For Entrepreneurs* (matrixpartners.com)

Cohort analysis as the SaaS forensic standard:
- The "logo retention" / "dollar retention" / "net dollar retention" hierarchy
- Cohort heatmaps are the diagnostic for both retention and expansion
- Recommended floor for cohort-level GRR: 90% for SMB SaaS, 95%+ for enterprise

### 4. Madhavan Ramanujam — *Monetizing Innovation* (Simon-Kucher)

The pricing-retention nexus:
- Customers who feel they overpaid in Q1 churn in Q3-Q4 — cohort decomposition reveals pricing
  misalignment with delayed signal
- A leaky cohort is often a pricing problem, not a product problem
- Cohort + pricing-tier decomposition is the technique that finds the leak's source

### 5. OpenView Partners — Cohort benchmarks (openviewpartners.com)

The numeric benchmarks underneath the skill's defaults:
- Top-quartile SaaS Q1 GRR: 93-95%
- Top-quartile cohort expansion Q1: 5-8%, Q4: 10-15%
- Bottom-quartile cohorts often hide 10+ pp below the consolidated number

### 6. Lenny Rachitsky — Lenny's Newsletter (lennysnewsletter.com)

Modern practitioner canon on cohort retention curves:
- "Show me your cohort retention curves and I'll tell you if you have product-market fit"
- The shape of the curve (flat vs. declining vs. smiling) is more diagnostic than any single number
- Cohort retention dispersion is a leading indicator for ARR forecasting accuracy

### 7. Reforge — Retention + Engagement program (reforge.com)

The systematic framework that operationalizes Balfour / Chen:
- Cohorts decomposed by 4 lenses: acquisition source, persona, lifecycle stage, pricing tier
- "Retention frameworks should be a board metric, not a product metric"
- Cohort heatmaps as standard quarterly artifact

### 8. Patrick Campbell / ProfitWell (now Paddle) — Cohort-driven retention research

The discipline of cohort decomposition for retention forecasting:
- Average NRR can stay flat for 2-3 quarters while a recent cohort is leaking
- "If you can't tell me your NRR by acquisition cohort, you don't know your NRR"
- Source of the skill's 5 pp leak-threshold default

---

## Leak detection rule (used by this skill)

A cohort is flagged **leaky** if:

- Its mean NRR across the projection horizon is **≥ 5 percentage points below** the mean NRR of
  all earlier-acquired cohorts (the "trailing-cohort average").

The 5 pp threshold is calibrated from Campbell / ProfitWell research: at < 5 pp, the gap is within
normal cohort-to-cohort variance; at ≥ 5 pp, the gap is signal that compounds quickly into the
consolidated number.

---

## Default retention curves (used when per-quarter data is missing)

When a cohort is provided without per-quarter retention/expansion data, the skill applies these
conservative defaults derived from OpenView benchmarks:

- **GRR curve**: 92% in Q1, decaying ~1 pp per quarter, with a floor of 85%
- **Expansion curve**: 4% in Q1, ramping +2 pp per quarter, capped at 12%

These are **priors, not prescriptions**. Always supply your real per-cohort data when available.

---

## Hard rules surfaced from canon

1. **Never present consolidated NRR without the cohort heatmap.** The consolidated number is the
   lagging indicator; the heatmap is the forensic tool.

2. **Decompose cohorts by acquisition quarter at minimum.** Better: + acquisition source, pricing
   tier, persona, segment.

3. **A leaky cohort signals a problem to investigate, not a number to discount.** Root-cause first:
   pricing mismatch? sales-motion drift? product-fit erosion? competitive incursion?

4. **Expansion-driven NRR > 110% requires product loops.** If your expansion is sales-led only,
   you're one comp-plan change away from collapse.

5. **Above $50M ARR, cohort decomposition is malpractice to skip.**
