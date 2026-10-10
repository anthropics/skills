# Scoring Rubric Reference

## Overview

The scoring system converts qualitative analysis into a structured, comparable output across seven dimensions. Each dimension scores 1–10. These feed into a composite score and a position-sizing recommendation.

**Important**: The score is not the conclusion — it's a structured summary of the conclusion. Do not start with a score and work backwards. Run all eight stages, then score.

---

## The seven dimensions

### 1. Business Quality (1–10)
Does this business generate durable economic value? Is it growing? Does it serve a real need in a way competitors can't easily replicate?

| Score | Criteria |
|---|---|
| 9–10 | Exceptional business. Consistent growth, expanding margins, dominant market position, pricing power demonstrated over years. Hard to imagine this business being less important in 10 years. |
| 7–8 | Strong business with clear competitive differentiation. Growing well. Some concentration or execution risk but structurally sound. |
| 5–6 | Solid business with identifiable strengths but meaningful concerns about concentration, market saturation, or execution. |
| 3–4 | Business with significant challenges. Shrinking market, margin pressure, or unclear competitive positioning. |
| 1–2 | Struggling or speculative. No demonstrated ability to earn above cost of capital. |

**Adjustments**: Penalize for customer concentration >20% in one customer. Penalize for sector in secular decline. Reward for FCF-positive with multi-decade market expansion.

---

### 2. Moat Durability (1–10)
How long can this company sustain returns above cost of capital? Reference `references/moat-framework.md` for full classification.

| Score | Criteria |
|---|---|
| 9–10 | 20+ year visibility. Multiple reinforcing moat types. Buffett-grade franchise. |
| 7–8 | 10–15 year visibility. One dominant moat with clear supporting advantages. Specific threats exist but are manageable. |
| 5–6 | 5–8 year visibility. Real moat but with contested durability. Known specific threats require ongoing monitoring. |
| 3–4 | 2–4 year lead. Fragile moat based on first-mover advantage, regulatory ambiguity, or borrowed access. |
| 1–2 | No identifiable durable moat. Competing on price or execution. |

**Critical adjustment**: If any part of the moat is "rented" (depends on third-party permission that could be revoked) and that permission is under active regulatory or legal threat, cap the score at 5 regardless of other factors.

---

### 3. Financial Strength (1–10)
Is the financial position sound? Is cash generation real? Reference `references/financial-analysis.md` for full checklist.

| Score | Criteria |
|---|---|
| 9–10 | Fortress balance sheet. Net cash. FCF growing faster than revenue. ROIC well above WACC. Zero capital need. |
| 7–8 | Strong cash generation. Manageable leverage (<2x net debt/EBITDA). Expanding margins. |
| 5–6 | Adequate but with concerns — moderate leverage, margin pressure, SBC eroding stated profits, or inconsistent FCF. |
| 3–4 | Financially stretched. Negative FCF or high leverage with unclear path to improvement. |
| 1–2 | Requires external capital to survive. Covenant risk, near-term maturity risk, or existential liquidity concern. |

**Adjustments**: Reward for consistent buyback history that actually reduces share count. Penalize if non-GAAP profit is significantly higher than GAAP and SBC is the main difference. Penalize for revenue concentration >20% in one customer.

---

### 4. Management Quality (1–10)
Is management's track record good? Do they allocate capital well? Are they honest with shareholders?

| Score | Criteria |
|---|---|
| 9–10 | Multi-year track record of beating guidance. Capital allocation is clear and disciplined (buybacks at value, acquisitions with obvious strategic logic). Shareholder communications are specific and honest about risks. |
| 7–8 | Strong execution with minor gaps. Communication is clear. Capital allocation is generally sound. |
| 5–6 | Adequate but with notable concerns — guidance misses, unclear capital allocation, recent management turnover, or defensive IR communications that avoid specific questions. |
| 3–4 | Multiple guidance failures, poor capital allocation (dilutive acquisitions, SBC abuse), or communications that are evasive on key risks. |
| 1–2 | Active concerns about integrity — regulatory investigations implying management misconduct, aggressive accounting, or significant insider selling during bad news. |

**Adjustments**: Active SEC, DOJ, or regulatory investigation caps the score at 6 until resolved, even if underlying execution is strong — the investigation itself is a management quality signal. Insider buying at scale (meaningful amounts, not just options exercise) is a strong positive signal.

---

### 5. Valuation Attractiveness (1–10)
Is the stock priced to deliver attractive returns? This is about the price, not the business.

| Score | Criteria |
|---|---|
| 9–10 | Trades at significant discount to intrinsic value. Multiple contraction already priced in. Margin of safety is large. |
| 7–8 | Modestly undervalued relative to peers and historical multiples. PEG below 1.0. Reverse-DCF shows achievable growth assumptions. |
| 5–6 | Fairly valued. Not expensive but not cheap. Priced for things to go mostly right. Little margin of safety. |
| 3–4 | Modestly overvalued relative to peers. Multiple expansion required for returns. Growth assumptions are optimistic. |
| 1–2 | Significantly overvalued. Current price embeds extraordinary future outcomes. Margin of safety is negative. |

**Practical shortcuts**:
- Forward P/E significantly below the company's own 5-year median → +1–2 points
- PEG below 0.75 → +1 point
- Stock down 30%+ in sector-wide selloff with fundamentals intact → +1 point
- P/S above 20x → –1 point (even for high-growth names)
- GF Value or comparable DCF model showing significant overvaluation → note explicitly even if not fully trusted

---

### 6. Thesis Clarity (1–10)
This scores the **user's** understanding, not the business's fundamentals. Reference `references/behavioral-psychology.md`.

| Score | Criteria |
|---|---|
| 9–10 | Can articulate thesis, bear case, sell triggers, and how this fits their portfolio from first principles. Written sell triggers exist. Has engaged with the strongest opposing arguments. |
| 7–8 | Strong personal understanding with minor gaps. Sell triggers partially formed. Has done primary research (earnings calls, IR materials, short reports). |
| 5–6 | General understanding based on secondary research. Key risks acknowledged. Sell triggers are vague but exist. |
| 3–4 | Limited personal understanding. Thesis is largely borrowed from external sources. Sell triggers unclear. Hasn't engaged with the bear case seriously. |
| 1–2 | Owns or wants to own a position without knowing why. Analysis is rationalization. No sell framework. |

**This score gates the position size recommendation.** A Thesis Clarity score below 5 results in a "do not add" recommendation regardless of how strong the other dimensions are. Capital follows understanding.

---

### 7. Risk/Reward Asymmetry (1–10)
Is the upside meaningfully larger than the downside from here? This is a forward-looking, probabilistic judgment.

To compute: Estimate the upside scenario (12-month or 3-year price target if thesis plays out), the base case, and the bear case. Assign rough probabilities.

| Score | Criteria |
|---|---|
| 9–10 | Upside is 3x+ the downside. Bear case is survivable and recoverable. Multiple paths to win. |
| 7–8 | Upside meaningfully exceeds downside (2x+ ratio). Bear case is painful but not thesis-breaking. |
| 5–6 | Roughly symmetric. Upside and downside are similar in magnitude. Not a fat pitch. |
| 3–4 | Downside exceeds upside. Multiple things must go right for the thesis to work. |
| 1–2 | Highly asymmetric in the wrong direction. More ways to lose than win. |

**Practical note**: A stock trading at reasonable historical multiples with strong fundamentals during a sector-wide selloff often has asymmetric upside. A stock at 20x revenue with a bull case "everything goes perfectly" has poor asymmetry even if the business is great.

---

## Composite scoring

Sum all seven dimension scores. Divide by 7 for the weighted average.

| Composite | Action signal |
|---|---|
| 8.0–10.0 | Strong conviction. Consider full target position. |
| 7.0–7.9 | High conviction. Consider 50–75% of target position. Stage the rest. |
| 6.0–6.9 | Medium conviction. Consider 25–50% of target position. Observe before adding. |
| 5.0–5.9 | Low-medium conviction. Exploratory position only (1–2% max). |
| 3.0–4.9 | Low conviction. Do not initiate. If already holding, reassess whether to hold. |
| Below 3.0 | Avoid. Likely a speculative bet, not an investment. |

---

## Volatility classification

Classify the stock before recommending position size. Sizing maximums differ by class.

| Class | Description | Examples | Max position |
|---|---|---|---|
| Smooth compounder | Low beta, predictable earnings, wide moat, non-cyclical | Visa, MSFT, Costco | 8–12% |
| Quality growth | Medium beta, strong moat, some execution risk | GOOGL, AAPL | 6–10% |
| Volatile growth | High beta (1.5–3.0), exciting fundamentals, significant risk | APP, NVDA, CRWD | 3–6% |
| Cyclical | Earnings tied to macro cycles | FCX, CVX, JPM | 3–5% |
| Turnaround | Currently unprofitable, thesis requires significant change | Varies | 1–3% |
| Speculative | Pre-revenue, binary outcome, loss-making | Early-stage tech | 0.5–1.5% |

**Volatility adjustment to composite score**: If a volatile growth stock scores 6.5/10, the position sizing recommendation is not the same as a smooth compounder scoring 6.5/10. Reduce position size accordingly.

---

## Conviction level — plain language

After computing the composite, also state the conviction level in plain language for the user:

- **High conviction** (composite 7.5+): I've seen the data, I understand the risks, I have a thesis I can defend, and I have a written sell trigger.
- **Medium conviction** (composite 6.0–7.4): The thesis makes sense, the business is strong, but there are specific unresolved questions I'm watching.
- **Low conviction** (composite 4.5–5.9): Interesting enough to have a learning position. Not enough to size up yet.
- **Exploratory** (below 4.5): Watching but not investing, or if already holding, considering exit.

*Conviction level is set by the minimum score across all dimensions, not just the average. A business that scores 9/9/9/9/9/2/9 (thesis clarity = 2) is an exploratory position regardless of what the composite says.*
