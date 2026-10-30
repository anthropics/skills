# Position Sizing Reference

## Core principle

Position sizing is the most underrated tool in investing. Getting the thesis right matters, but getting the size wrong is how correct theses still destroy capital. A stock that drops 50% in a 2% position is a bad day. The same drop in a 20% position is a portfolio catastrophe.

The goal of position sizing is to ensure that being wrong doesn't ruin you, while being right still rewards you meaningfully.

---

## The decision tree

Work through this in order before recommending a size.

### Step 1: Determine maximum position by volatility class

| Volatility Class | Max Position Size |
|---|---|
| Smooth compounder (Visa, MSFT, Costco) | 8–12% |
| Quality growth (GOOGL, AAPL) | 6–10% |
| Volatile growth (high beta, emerging leaders) | 3–6% |
| Cyclical (commodity-linked, macro-sensitive) | 3–5% |
| Turnaround (pre-profitability, thesis requires change) | 1–3% |
| Speculative (pre-revenue, binary outcome) | 0.5–1.5% |

This is a hard cap. Composite score and conviction don't increase the maximum — they determine where within the range to sit.

### Step 2: Apply composite score to find position within range

| Composite Score | Position as % of maximum |
|---|---|
| 8.0–10.0 | 90–100% of maximum |
| 7.0–7.9 | 65–80% of maximum |
| 6.0–6.9 | 35–55% of maximum |
| 5.0–5.9 | 15–30% of maximum |
| Below 5.0 | 0–15% (exploratory or none) |

Example: A volatile growth stock (max 5%) with composite score 6.5 → 35–55% of 5% → 1.75–2.75% target position.

### Step 3: Apply conviction check — the minimum score override

Position size is capped by the **minimum** individual dimension score, not just the composite:

- If **Thesis Clarity** < 5: Cap at 1.5% regardless of other scores
- If **Financial Strength** < 4: Cap at 2.0% (you cannot size into a balance sheet risk)
- If **Risk/Reward** < 4: Cap at 2.0% (downside too large relative to upside)
- If any single dimension is 2 or below: Reduce to exploratory size (≤1%) or decline to recommend

### Step 4: Determine entry structure — never all-in

**Never recommend full-size entry at one price.** Always stage the entry across 2–4 tranches:

| Conviction | Tranche Structure |
|---|---|
| High (7.5+ composite) | 50% initial, 30% at -10%, 20% at -20% |
| Medium (6.0–7.4) | 33% initial, 33% at -10–15%, 33% at further pullback or catalyst |
| Low (5.0–5.9) | 25% to start (this is the learning position), remainder only after thesis confirmation |
| Exploratory (<5.0) | Single small tranche. No ladder planned. |

**Reason for staging**: Two things happen when you stage entries. First, you protect against buying at exactly the wrong moment. Second, and more importantly, the act of setting trigger levels forces you to pre-commit to your thesis when you're calm, rather than making impulse decisions when the price is moving.

### Step 5: State explicit mental sell triggers — written, not vague

The position sizing recommendation is incomplete without written sell triggers. These must be:
- **Specific** (not "if the thesis breaks" — that's not specific)
- **Observable** (tied to data points, not feelings)
- **Pre-committed** (written down before the position is opened or before adding)

Template for sell triggers:

```
EXIT FULL position if:
- [Specific regulatory/legal event]
- [Specific management event — CEO departure + negative context]
- [Gross margin drops below X% for two consecutive quarters]

TRIM by 50% if:
- [Guidance cut of more than X% in a single quarter]
- [Key customer representing >Y% of revenue announces exit]
- [Competitive product launch that addresses core value proposition]

ADD if:
- [Price declines to $X with no new negative fundamental information]
- [Quarterly results beat and guidance raises, stock drops on sentiment]
- [SEC probe resolves without material product changes required]
```

Without written triggers, "hold through volatility" is a phrase, not a strategy. When the stock is down 30% and the news is bad, the human brain is not capable of making good decisions from scratch. The triggers are made now so they don't have to be made then.

---

## Special situations

### Adding to an existing position

Additional considerations beyond the standard framework:

1. **What has changed since you initiated?** If the answer is "nothing, just the price" — pause. A lower price alone is not a reason to add. It must be accompanied by either (a) higher conviction driven by new positive information, or (b) no new negative information to explain the price drop.
2. **What is your total position size after adding?** Make sure the post-add size stays within the volatility class maximum.
3. **Are you adding to a winner or averaging into a loser?** Adding to a winner requires evidence the thesis is playing out. Averaging into a loser requires a specific counter-argument to the reason the stock is down — not just the conviction that it "should" be higher.

### The "learning position" structure

When Thesis Clarity is low (below 5/10), recommend a specific learning position framework:

1. Enter at ≤1.5% of portfolio ("learning size" — large enough to stay engaged, small enough that it doesn't hurt if wrong)
2. Set a re-evaluation date (typically after next quarterly earnings)
3. Explicit condition for adding: "After I have completed [X] research actions and can articulate the thesis in writing, I will reassess sizing"
4. Do not add before the condition is met

This structure is honest about where the user is analytically and prevents the "I'll figure it out as I go" trap, which is how small learning positions become large panic-sells.

---

## Position sizing in portfolio context

Stock-level sizing exists within a portfolio. Before finalizing the recommendation, check:

- **Sector concentration**: If the user already has 15% in tech/software, adding another volatile growth tech name may be appropriate on its own but concentrated at the portfolio level
- **Correlation risk**: Stocks that move together in selloffs should be counted together for concentration purposes
- **Total speculative allocation**: If more than 20% of the portfolio is in volatile-growth or speculative names, the marginal contribution to risk is very high even at "small" individual positions
- **Liquidity needs**: Any capital that might be needed within 2 years should not be in volatile growth names

These are questions to raise with the user, not to answer for them — Claude doesn't know their full financial picture.

---

## A note on why this matters

The research is clean. The process is rigorous. The analysis is good. And then the stock drops 35% because of a sector selloff and the user sells at the low. This happens constantly, and it always happens to investors who are right about the business but wrong about the size.

Position sizing is the bridge between "I'm right about the business" and "I made money." Without it, analytical quality is wasted. Every sizing recommendation should be accompanied by the quiet question: "If I'm 100% right about the business but wrong about the timing by 2 years, can this person hold through the drawdown at this size?" If the answer is no, reduce the size until the answer is yes.
