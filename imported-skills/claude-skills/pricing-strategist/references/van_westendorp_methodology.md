# Van Westendorp Price Sensitivity Meter — Methodology

Reference for `wtp_analyzer.py`. Covers the 4 questions, the 4 intersection points,
sample size discipline, segmentation requirements, and the most common misinterpretations.

---

## The four questions

Each respondent answers, for the product or feature described:

1. **Too cheap** — "At what price would you consider the product so inexpensive that you'd
   doubt its quality and not buy it?"
2. **Bargain** — "At what price would you consider the product a bargain — a great buy for the
   money?"
3. **Getting expensive** — "At what price would you start to feel the product is getting
   expensive, but you'd still consider buying it?"
4. **Too expensive** — "At what price would you consider the product so expensive that you
   would not consider buying it?"

For each respondent, the answers should obey:
`too_cheap ≤ bargain ≤ getting_expensive ≤ too_expensive`

Respondents who violate this ordering are typically screened out before analysis (the tool
flags them as warnings).

---

## The four intersection points

Build cumulative curves on a sorted price grid:

- **% too cheap (≥ price)** — decreasing in price (more respondents say "too cheap" at low prices)
- **% bargain (≥ price)** — decreasing
- **% getting expensive (≤ price)** — increasing
- **% too expensive (≤ price)** — increasing

Then find the four intersections:

| Point | Curves | Interpretation |
|---|---|---|
| **OPP** — Optimal Price Point | too cheap ↔ too expensive | Equal % reject as too cheap and too expensive. Theoretical sweet spot. |
| **IDP** — Indifference Price Point | bargain ↔ getting expensive | Median respondent's perceived "fair" price. |
| **PMC** — Point of Marginal Cheapness | too cheap ↔ getting expensive | Lower bound of acceptable range — below this, quality doubt dominates. |
| **PME** — Point of Marginal Expensiveness | bargain ↔ too expensive | Upper bound of acceptable range — above this, purchase rejection dominates. |

**Range of Acceptable Prices (RAP) = [PMC, PME].**

---

## Sample size discipline

- **N < 30:** Directional only. Tool emits a warning. Do not anchor decisions on these results.
- **N = 30-99:** Acceptable for hypothesis generation; expect noisy intersections.
- **N ≥ 100:** Preferred. ESOMAR conventions cite N=200-400 for stable PSM in B2C; B2B can
  work with smaller but more carefully screened panels.
- **Segmented PSM:** Run separately for ICP vs non-ICP, and per buying-role segment. Aggregate
  PSM averages across segments hide the structure you need.

---

## Common misinterpretations (the high-cost ones)

1. **"PSM gives THE price."** — No. PSM gives a **range**. The number inside the range is a
   commercial decision involving competition, positioning, and margin targets.

2. **"OPP is the optimal price."** — OPP is named misleadingly. It's the point of *equal
   resistance from both sides*, not a profit-maximizing price. The optimal price often sits
   between OPP and PME if the market tolerates upside.

3. **"PSM works on non-customers."** — PSM measures *perceived* price thresholds. Run it on
   the actual ICP. Random survey panels produce intersection points for an imaginary buyer.

4. **"PSM works for any product."** — Original method (van Westendorp, 1976) was built for
   consumer non-durables. It works for SaaS, but breaks for products where the customer cannot
   form a reference price (truly novel categories). Use Newton-Miller-Smith (NMS) refinement
   in those cases — adds purchase-likelihood at each price.

5. **"Higher RAP upper bound = we can charge more."** — Only if your willingness-to-act
   matches willingness-to-state. Always validate with a real purchase test (conjoint, A/B,
   or sales-priced cohort) before anchoring at PME.

---

## Authoritative sources

1. **Peter van Westendorp — "NSS-Price Sensitivity Meter (PSM)" — 29th ESOMAR Congress
   Proceedings, 1976.** The original paper. Establishes the four questions and intersection
   method. Still the canonical reference 50 years later.

2. **Gabor & Granger (1966), Newton, Miller & Smith (NMS).** Extension that adds
   purchase-likelihood at each price. Conjoint.ly and Sawtooth both implement NMS variants
   for novel products without strong reference prices.

3. **Conjoint.ly — "Price Sensitivity Meter (Van Westendorp) Explained"**.
   Practitioner-grade explanation including segmentation guidance and NMS comparison.
   https://conjointly.com/guides/van-westendorp-price-sensitivity-analysis/

4. **Sawtooth Software — Lighthouse Studio documentation on PSM**.
   Industry-standard tooling. Their guidance on respondent screening, monotonicity checks,
   and segmentation is the operational standard most pricing consultancies use.

5. **ESOMAR — Code of Conduct + price-sensitivity research guidance**.
   Sample-size conventions, respondent qualification, ethical pricing research. PSM is
   referenced in their pricing research best-practice papers.

6. **Stan Lipovetsky (2006) — "Van Westendorp Price Sensitivity in statistical modeling,"
   International Journal of Operational Research.** Critique and statistical refinement —
   shows that classical PSM intersections are biased estimators under common response
   distributions. Recommends bootstrap CIs and ordinal regression overlays.

7. **Decision Analyst — "Van Westendorp PSM Handbook"**.
   Operational handbook including a worked example, screening criteria, and segmentation
   templates. https://www.decisionanalyst.com/

8. **Madhavan Ramanujam — Monetizing Innovation (Wiley, 2016), Ch. 4.**
   PSM as one of three WTP techniques (alongside direct WTP and conjoint). Ramanujam's
   guidance: PSM for category baseline, conjoint for feature-level WTP, direct WTP for
   confirmation.

## How this skill uses the methodology

- `wtp_analyzer.py` implements classical PSM intersections using linear interpolation on the
  sorted price grid — the standard approach per van Westendorp (1976) and Sawtooth.
- Tool emits sample-size warnings at N<30 and N<100, per ESOMAR / Decision Analyst conventions.
- Tool checks per-respondent monotonicity (`tc ≤ bg ≤ ge ≤ te`) and reports inconsistent rows.
- Output explicitly frames PSM as a **range**, not a price, and recommends segmented re-runs —
  per the documented misinterpretation patterns above.
- Tool does not implement NMS extension; for novel categories without reference prices, point
  the user to conjoint or NMS-specific tooling.
