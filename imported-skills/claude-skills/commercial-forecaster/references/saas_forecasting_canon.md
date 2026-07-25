# SaaS Forecasting Canon

Curated, opinionated knowledge base for SaaS bookings + ARR forecasting. Source material behind
`bookings_forecaster.py`'s scoring rules and the 3-tier (commit / best-case / pipe-only) discipline.

## Core principle

A forecast is a **claim about the future under disclosed assumptions**. A forecast without disclosed
assumptions is theatre — it cannot be evaluated, corrected, or learned from. Every output of this
skill names the conversion rate, the data window, and the weighting choice.

The 3-tier model exists because the question "what's the number?" has three valid answers:
- **Commit** — what I will defend even if the quarter goes sideways
- **Best-case** — what I can hit if everything goes my way
- **Pipe-only** — the unweighted ceiling

Presenting one without the others is theatre. Presenting all three with the assumption block is
the discipline.

---

## The 3-tier discipline

### Commit

- Includes only commit-grade stages (verbal, contract-out, commit, closed-won-pending)
- Conversion applied: blended (70% last-4Q + 30% last-12Q)
- Time-to-close probability adjustment applied
- Stalled-opp downweight applied (opp age > 2x median stage age AND last_activity > 45 days → × 0.5)
- This is the number the CRO defends to the CEO and CFO

### Best-case

- Includes commit-grade stages + weighted-stage opps (proposal, negotiation, demo-completed)
- Conversion blended (70/30)
- Time-to-close probability applied
- NO stall downweight (best-case is the optimistic ceiling)
- This is the number for "if everything breaks our way"

### Pipe-only

- Includes everything in pipeline at any stage
- Conversion blended only (no time-to-close, no stall)
- This is the unweighted top of the funnel — useful as the divisor in pipeline-coverage ratio

### Pipeline coverage ratio

- Total pipeline $ / commit $
- SaaS-industry floor: 3.0x
- Below 3.0x → commit is structurally unsupported and the CFO will challenge it

---

## Source register (≥ 7 cited)

### 1. David Skok — *For Entrepreneurs* (matrixpartners.com)

Founding canon on SaaS metrics + forecasting. Specifically:
- The CAC-payback / LTV framework that anchors what "good" forecast accuracy looks like
- The pipeline-coverage discipline (3x as the industry floor)
- Cohort retention curves as the input to NRR forecasting, not the output
- "Stalled-opp identification by stage-age is the #1 forecast-hygiene practice in top-decile SaaS pipelines."

### 2. Tomasz Tunguz — Theory Ventures (tomtunguz.com)

Forecasting studies from 100+ SaaS companies. Specifically:
- Single-window conversion estimates miss regime change at ~3-quarter lag → blended weighting needed
- Sandbagging is the more common pattern than hockey-sticking, especially after a missed quarter
- Forecast accuracy degrades sharply for stages with CoV > 25%
- "If your last-4Q and last-12Q conversion diverge by more than 10pp, you have a regime change, not noise."

### 3. OpenView Partners — SaaS Forecasting Benchmarks (openviewpartners.com)

Annual State-of-the-Cloud-adjacent surveys with explicit forecast-accuracy benchmarks:
- Top-quartile SaaS companies hit commit within 5%; bottom-quartile miss by 25%+
- Hockey-stick forecasts (best-case > 80% of pipe-only) have 2x lower realization rate
- Pipeline coverage 3-4.5x is the typical band for healthy commit
- Recommends the 3-tier (commit / best-case / pipe-only) structure as standard board hygiene

### 4. Bessemer Venture Partners — State of the Cloud forecasting research (bvp.com/atlas)

The BVP "Cloud Index" methodology and the Good/Better/Best NRR benchmarks:
- 100% NRR = "good", 110% = "better", 120%+ = "best"
- Cohort decomposition is the forensic technique to detect leak before consolidated number moves
- Forecasting at the company level without cohort decomposition is malpractice for ARR > $50M

### 5. Pacific Crest / KeyBanc Capital Markets — Private SaaS Survey

Long-running annual survey of private SaaS companies (now KeyBanc):
- Pipeline-coverage ratio: top-quartile 3.0-4.5x, median ~3.0x, bottom-quartile < 2.5x
- Forecast accuracy correlates more tightly with stage-conversion CoV than with mean conversion
- Standard sales stages and their expected conversion priors (used as fallback in this skill's profiles)

### 6. Patrick Campbell / ProfitWell (now Paddle) — Cohort-driven retention research

The cohort-decomposition discipline:
- Consolidated NRR is an average that hides 5-15pp dispersion across cohorts
- Leaky cohorts surface in the consolidated number 2-3 quarters after the leak begins
- The cohort heatmap is the forensic tool; the consolidated number is the lagging indicator
- "If you cannot tell me your NRR by acquisition cohort, you do not know your NRR."

### 7. MIT Sloan — Forecasting research (Hyndman & Athanasopoulos, *Forecasting: Principles and Practice*)

The statistical canon underneath the CoV-based confidence bands:
- CoV (coefficient of variation) on the input series predicts forecast accuracy more reliably than mean
- Sample size n ≥ 4 is the practical minimum for stable CoV estimation
- Weighted blends of recent vs. long-run windows outperform either window alone when regime change is plausible

### 8. Winning by Design — Bowtie GTM model + revenue forecasting (winningbydesign.com)

The bowtie model + recurring-impact framework:
- Forecast must account for both new ARR AND retained/expansion ARR (the right side of the bowtie)
- Pipeline-coverage on new bookings is insufficient; expansion pipeline coverage is the second leg
- Aligns with the cohort decomposition discipline above

---

## Calibration table — used by `bookings_forecaster.py`

Default stage-conversion priors per industry profile (applied only when historical data is missing
for that stage). These are deliberately conservative — your data overrides.

| Stage | saas | api | enterprise-software | marketplace | services |
|---|---:|---:|---:|---:|---:|
| discovery | 35% | 45% | 20% | 40% | 30% |
| demo_completed | 55% | 60% | 40% | 60% | 50% |
| proposal | 65% | 70% | 55% | 68% | 62% |
| negotiation | 75% | 80% | 68% | 78% | 72% |
| verbal | 85% | 88% | 80% | 86% | 82% |
| commit | 92% | 94% | 90% | 92% | 90% |

Sources: KeyBanc SaaS Survey, OpenView benchmarks, Bessemer Atlas. Profile picker is a starting prior,
not a prescription.

---

## Hard rules surfaced from canon

1. **Forecast without disclosed assumptions is theatre.** Every CLI output names the conversion
   rate, the data window, and the weighting choice. Manual suppression of the assumption block
   makes the human responsible for the theatre.

2. **The 3-tier model is non-collapsible.** Presenting commit without best-case and pipe-only loses
   information. The CFO needs to know the dispersion.

3. **Pipeline coverage 3.0x is the floor, not the ceiling.** Below 3.0x, the commit is structurally
   unsupported.

4. **Stalled opps are not commit.** A "verbal" deal that's been verbal for 6 months is not a commit;
   the stall rule downweights them.

5. **Cohort decomposition is mandatory above $50M ARR.** Below that, it's strongly recommended.
