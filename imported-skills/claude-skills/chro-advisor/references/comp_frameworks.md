# Compensation Frameworks Reference

Salary bands, equity design, total comp modeling, comp philosophy, and raise/refresh processes.

---

## Comp Philosophy — The Foundation

Before building bands, define your philosophy. Ambiguity in comp philosophy = pay equity lawsuits and trust erosion.

**The five decisions:**

### 1. What market percentile do you target?
- **P25 (below market):** Only viable with exceptional mission, equity, or growth opportunity. Flight risk is high after 18 months.
- **P50 (market median):** Standard for most Series A–B companies. Competitive without premium.
- **P75 (above market):** Premium talent strategy. Used by high-margin or talent-intensive businesses. Netflix model.
- **P90+:** Top-of-market for specific functions (ML at AI companies, senior engineers at FAANG feeders).

**Common hybrid:** P50 base + above-market equity = total comp at P65–75.

### 2. What's in your total comp package?
Define each component explicitly:
- **Base salary** — cash, market-benchmarked
- **Variable / bonus** — % of base, tied to what criteria
- **Equity** — options vs. RSUs, vesting schedule, refresh cadence
- **Benefits** — health, retirement, PTO policy
- **Learning & development budget**
- **Remote/location allowances**

### 3. Are bands public internally?
Recommended: Yes. Pay transparency reduces equity complaints, builds trust, and forces you to maintain clean bands.

### 4. How often do you refresh bands?
Minimum: annually. High-growth markets: every 6 months (engineering specifically in hot markets).

### 5. How do you handle individual negotiation?
Options:
- **Fixed bands, no negotiation** (Buffer model) — simple, fair, loses some candidates
- **Band range with manager discretion** — most common, requires calibration guardrails
- **Individual negotiation within band** — flexible, creates pay equity drift over time

---

## Salary Bands: Construction

### Step 1: Define levels

Standard IC levels (adapt to company):
| Level | Title example | Scope |
|-------|--------------|-------|
| L1 | Junior / Associate | Execution with guidance |
| L2 | Mid-level | Independent execution |
| L3 | Senior | Leads workstreams, mentors L1-L2 |
| L4 | Staff / Principal | Cross-team technical leadership |
| L5 | Distinguished / Fellow | Company-wide technical direction |

Management track:
| Level | Title | Scope |
|-------|-------|-------|
| M1 | Manager | Team of 4–8 ICs |
| M2 | Senior Manager | Manager of managers or larger team |
| M3 | Director | Function or large org |
| M4 | VP | Business unit, company-wide |
| M5 | SVP / C-Suite | Executive |

### Step 2: Gather market data

**Data sources (by quality):**
1. **Radford / Aon** — Gold standard. Expensive ($10K+/year). Worth it at Series B+.
2. **Levels.fyi** — Excellent for engineering. Free. Self-reported but large sample.
3. **Glassdoor Salary** — Broad coverage. Less precise for startups.
4. **Pave / Carta Total Comp** — VC-backed companies. Good peer benchmarking.
5. **LinkedIn Salary** — Free tier. Reasonable signal for G&A roles.
6. **Offer letter data** — What candidates are bringing from other companies. Real-time signal.

**What to pull:** P25, P50, P75, P90 for each role × level × geography.

### Step 3: Set band structure

**Band width (range within a level):**
- IC bands: 80–120% of midpoint (i.e., ±20% from center)
- Manager bands: 85–115% of midpoint
- Wider bands allow room for differentiation within level; narrower bands reduce pay equity drift

**Band overlap between levels:**
- 10–20% overlap is normal (top of L2 overlaps with bottom of L3)
- > 30% overlap: your levels are too close together
- No overlap: new hires jump too much between levels (compression risk)

**Example engineering band structure (US, Series B company, P50 target):**

| Level | Band Min | Midpoint | Band Max |
|-------|----------|----------|----------|
| L1 Software Engineer | $90K | $105K | $125K |
| L2 Software Engineer | $115K | $135K | $160K |
| L3 Senior SWE | $150K | $175K | $205K |
| L4 Staff SWE | $195K | $225K $260K |
| M1 Eng Manager | $175K | $205K | $235K |
| M2 Sr Eng Manager | $215K | $250K | $285K |
| M3 Director, Eng | $255K | $300K | $345K |

*Adjust by 15–25% for non-SF/NYC markets. Adjust -40% to -60% for European markets.*

### Step 4: Place employees in bands

**Compa-ratio** = Employee salary / Band midpoint

| Compa-ratio | Interpretation |
|------------|---------------|
| < 0.85 | Below range — immediate risk |
| 0.85–0.95 | Developing in role |
| 0.95–1.05 | Fully performing (target zone) |
| 1.05–1.15 | Senior/expert in role |
| > 1.15 | Above range — flag for review |

**Audit report:** Run quarterly. Flag anyone below 0.85 (flight risk) or above 1.15 (overpaid for level, or needs promotion).

---

## Equity Frameworks for Startups

### Option Basics

**ISO vs NSO:**
- ISO (Incentive Stock Options): For employees. Favorable tax treatment if held 1+ year post-exercise.
- NSO (Non-Qualified Stock Options): For advisors, contractors, sometimes employees. Taxed as ordinary income on exercise.

**Strike price:** Set to 409A valuation at grant. Lower is better for employees. Early employees win on strike price.

**Vesting schedule standards:**
- 4-year vest, 1-year cliff: Standard
- 4-year vest, 6-month cliff: Startup market adapting to faster pace
- 1-year cliff means: nothing until 12 months; monthly or quarterly after

**Post-termination exercise window (PTEW):**
- Standard: 90 days. Often too short for employees who can't afford exercise.
- Better: 1–5 years or until IPO. Use as a talent differentiator.
- Companies extending PTEW: Stripe, Airbnb (pre-IPO), Square, most employee-friendly startups.

### Equity Grant Ranges by Stage and Level

*Expressed as % of fully diluted shares at grant. Ranges vary significantly by market, stage, and funding.*

**Seed stage:**
| Role | Equity % |
|------|----------|
| Co-founder | 20–40% |
| First engineering hire | 0.5–1.5% |
| First non-technical exec hire | 0.25–0.75% |
| IC (L2-L3) | 0.1–0.4% |
| IC (L3-L4) | 0.2–0.6% |

**Series A:**
| Role | Equity % |
|------|----------|
| VP / Head of function | 0.3–0.75% |
| Director | 0.1–0.3% |
| Senior IC (L3) | 0.05–0.15% |
| Mid IC (L2) | 0.02–0.08% |
| Junior IC (L1) | 0.01–0.05% |

**Series B:**
| Role | Equity % |
|------|----------|
| VP / Head of function | 0.1–0.3% |
| Director | 0.05–0.15% |
| Senior IC (L3) | 0.02–0.07% |
| Mid IC (L2) | 0.01–0.03% |

*At Series B+, equity is increasingly expressed in dollar value (grant value = X shares × current 409A). Use Carta or Pulley to model dilution.*

### Equity Refresh Program

**Why it matters:** Employees hired at Series A with 4-year vesting will be fully vested by Series B. No unvested equity = no retention hook.

**When to refresh:**
- After every significant funding round
- Annually for high performers (top 20%)
- After promotion (role-commensurate top-up)
- Counter-offer situations (use carefully — signals you underpaid initially)

**Refresh models:**
1. **Anniversary grant:** Annual cliff-free refresh for all employees above a performance threshold
2. **Evergreen model:** Continuous vesting maintained — refresh annually so employee always has 2–3 years remaining
3. **Event-based:** Refresh tied to milestones (promotion, funding, annual review cycle)

**Dilution awareness:** Every refresh dilutes existing shareholders. Model pool usage quarterly. Replenish option pool before it drops below 10–12% of fully diluted shares.

---

## Total Comp Modeling

### Components of Total Comp

```
Total Compensation = Base Salary
                   + Annual Bonus (target %)
                   + Equity Value (annualized grant / vesting period)
                   + Benefits (employer-paid premiums, retirement match)
                   + Allowances (home office, internet, L&D, commuter)
```

### Annualizing Equity Value

For comparison to cash compensation:

```
Annual equity value = (Grant shares × Current 409A price) / Vesting years
```

Example: 10,000 options at $2 strike, current 409A = $8, 4-year vest
- Grant value at current 409A = 10,000 × $8 = $80,000
- Annual value = $80,000 / 4 = $20,000/year
- If base is $150K, total comp is ~$170K/year

*Note: For recruiting purposes, you can use last preferred share price (VC price) to show upside — but be transparent about the difference between 409A and preferred.*

### Benefits Valuation

Frequently undervalued in offers. Quantify explicitly:
| Benefit | Typical employer cost |
|---------|----------------------|
| Health insurance (employee) | $4K–8K/year |
| Health insurance (family) | $15K–25K/year |
| 401K match (4% of salary) | $5K–10K/year |
| L&D budget ($2K/year) | $2K/year |
| Home office stipend ($500) | $500/year |

A $140K offer with family health coverage + 4% 401K match is worth $165K+ total.

---

## Raise and Refresh Process

### Annual Compensation Review Cycle

**Recommended cadence:**
- October/November: Market data refresh, band updates
- November/December: Manager merit recommendations
- December/January: Calibration and approvals
- January/February: Effective date for new salaries + equity grants

**Budget allocation:**
- **Merit budget** (performance-based raises): 3–5% of total payroll typically
- **Market adjustment budget** (fixing below-band salaries): Separate from merit. Non-negotiable to avoid attrition.
- **Promotion budget:** Separate. Promotions should not come from merit pool.

### Merit Increase Guidelines

| Performance Rating | Merit Increase Range |
|-------------------|---------------------|
| 5 – Exceptional | 8–15% |
| 4 – Exceeds | 5–8% |
| 3 – Meets | 2–4% |
| 2 – Needs improvement | 0–1% |
| 1 – Underperforming | 0% (PIP active) |

*Adjust based on compa-ratio. A high performer at P90 of their band gets a smaller increase than a high performer at P50.*

### Compa-Ratio Adjustment Matrix

| Performance \ Compa-Ratio | < 0.90 | 0.90–1.00 | 1.00–1.10 | > 1.10 |
|---------------------------|--------|-----------|-----------|--------|
| Exceptional (5) | 12–15% | 8–12% | 5–8% | 3–5% |
| Exceeds (4) | 8–12% | 5–8% | 3–5% | 1–3% |
| Meets (3) | 5–8% | 3–5% | 2–3% | 0–2% |
| Needs impr (2) | 0–2% | 0–1% | 0% | 0% |

### Promotion vs. Merit — Keep These Separate

**Common mistake:** Using merit budget to fund promotions. This forces a choice between rewarding performance and recognizing level change.

**Promotion increase guidelines:**
- One level (e.g., L2 → L3): 10–20% increase, new equity grant
- Two levels (rare): 20–35% increase, new equity grant at new level
- Manager track (IC → M1): 15–25% increase, new equity grant

**Promotion criteria process:**
1. Manager nominates with written business case
2. Calibration committee reviews cross-functionally
3. HR validates against band (no off-band exceptions without CHRO sign-off)
4. Employee informed before annual review — never surprised at review meeting

### Off-Cycle Adjustments

When to do them:
- Counter-offer situations (see below)
- Competitive intelligence reveals underpay for a specific role
- New market data shows a role significantly under-benchmarked
- Internal equity audit reveals unexplained gaps

**Counter-offer policy:**
Three options:
1. **Match** — Risk: signals you underpay; sets precedent
2. **Partial match** — "We can do X, which is the top of your band" — cleaner
3. **Decline** — Accept the attrition, improve the band for the next hire

**Rule:** If you're regularly in counter-offer conversations, your bands are stale. Fix the bands.

---

## Pay Equity Audit

Run annually. Non-negotiable at Series B+.

**What to audit:**
- Pay gap by gender within each level and function
- Pay gap by ethnicity within each level and function
- Compa-ratio distribution across demographics
- Time-to-promotion by demographic group

**Methodology:**
1. Pull all employee data: level, function, salary, tenure, performance ratings, gender, ethnicity
2. Run regression controlling for level, tenure, and performance
3. Unexplained gap after controls = the problem to fix
4. Flag and remediate within the same review cycle

**Legal exposure:** In many jurisdictions, documented pay gaps without remediation plans are litigation risk. The audit creates a record of intent; remediation closes the risk.

**Remediation budget:** Set aside 0.5–1% of payroll annually for equity adjustments. If you're doing it right, this shrinks over time.
