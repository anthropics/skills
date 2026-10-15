---
name: fisher-investing
description: >
  Apply Philip Fisher growth stock investing methodology from Common Stocks and Uncommon Profits.
  Use this skill whenever a user asks about evaluating whether a company is a growth stock,
  analyzing a company investment quality, when to buy or sell a stock, how to research a company
  using the scuttlebutt method, diversification strategy, or any question involving long-term
  growth investing. Trigger on phrases like is X a growth stock, should I buy or sell X,
  analyze X using Fisher, evaluate X as an investment, growth stock criteria, scuttlebutt research,
  or any company analysis request. Always use this skill for stock evaluation questions.
---

# Philip Fisher Growth Stock Investing Framework

This skill encodes the complete methodology from Philip Fisher's *Common Stocks and Uncommon Profits* (1958, revised 1960). Fisher is one of history's greatest investors — Warren Buffett credits him as a major influence alongside Benjamin Graham.

**Core Philosophy**: Buy exceptional companies at reasonable prices and hold them almost forever. The goal is gains of several hundred percent over years, not small short-term profits. Most great gains come from a very small number of outstanding companies — finding them requires deep research, not superficial statistics.

---

## HOW TO USE THIS SKILL

When the user asks about a company or stock:
1. **Identify the question type** (see routing below)
2. **Load the relevant reference file** for detailed criteria
3. **Apply Fisher's framework systematically**
4. **Give a structured verdict** with reasoning

**Question routing:**
- "Is X a growth stock?" or "Evaluate X" → Apply **The 15 Points** (see `references/fifteen-points.md`)
- "How do I research X?" → Apply **Scuttlebutt Method** (see `references/scuttlebutt.md`)
- "When should I buy X?" → Apply **Buying Timing** (see `references/when-to-buy-sell.md`)
- "Should I sell X?" → Apply **Selling Rules** (see `references/when-to-buy-sell.md`)
- "How many stocks should I own?" → Apply **Diversification** (see `references/donts.md`)
- General pitfalls / mistakes → Apply **Don'ts** (see `references/donts.md`)

---

## QUICK FRAMEWORK SUMMARY

### What Makes a True Growth Stock (The Core Test)

A true Fisher growth stock must score well on most of the 15 Points. There are two essential categories — **no exceptions**:

**Category A — Business Quality (Must be present):**
- Large, expandable market for its products (not a one-time surge)
- Determined R&D pipeline for future growth after current products mature
- Above-average profit margins, OR deliberately thin margins to fuel faster growth
- Outstanding sales organization (production + research are useless without sales)
- Active program to maintain/improve profit margins (not just price increases)

**Category B — Management Quality (Must be present):**
- Unquestionable integrity — this is the one non-negotiable point. If integrity is in doubt, never invest regardless of other scores.
- Long-range outlook on profits (not maximizing current quarter)
- Openly communicates with investors in bad times as well as good
- Depth of management — not dependent on one key person
- Good labor AND executive relations

**Category C — Financial Health (Important but more flexible):**
- Equity financing plans, if needed, won't severely dilute existing shareholders
- Effective cost analysis and accounting controls
- Industry-specific factors considered

### Two Types of Great Growth Companies

Fisher identified two archetypes — both can be outstanding investments:
- **"Fortunate and Able"**: Companies in great industries that grew even bigger than founders imagined (e.g., Alcoa in aluminum)
- **"Fortunate Because They Are Able"**: Companies that *created* their own luck through brilliant management (e.g., Du Pont — started making blasting powder, built an empire through skill and research)

The key insight: **Management quality is the common denominator.** No company grows for decades on luck alone.

---

## SCORING & VERDICT FRAMEWORK

When evaluating a company, score each of the 15 Points as:
- ✅ **Strong** — clearly qualifies
- ⚠️ **Adequate** — passes but with reservations
- ❌ **Weak** — fails to qualify
- ❓ **Unknown** — requires scuttlebutt research to determine

**Verdict guide:**
- 13–15 ✅ → **Outstanding growth stock candidate** — investigate deeply
- 10–12 ✅ with no ❌ on integrity/management → **Solid candidate** — worth further research
- Any ❌ on integrity → **Reject immediately** — no exceptions
- Multiple ❌ on management points → **Not a Fisher growth stock**
- Strong on business but weak on management → **Dangerous — avoid**

---

## KEY PRINCIPLES TO APPLY IN EVERY ANALYSIS

1. **Qualitative over quantitative**: The most important factors (management integrity, R&D effectiveness, sales culture) cannot be captured by ratios. Numbers are a starting point, not a conclusion.

2. **Future matters, not past**: Past EPS and historical price ranges are nearly meaningless. What matters is what earnings will be in 3–5 years and whether the business will still be exceptional then.

3. **P/E ratio nuance**: A consistently exceptional company *should* trade at a premium P/E. A stock trading at 2× the market P/E that has done so for 30 years is NOT overpriced if it continues to deliver. Do not reject a great company just because it looks "expensive" on simple metrics.

4. **Market timing is futile**: Do not wait for economic forecasts to "clear up" before buying. Nobody can reliably predict business cycles. A better approach: buy great companies during temporary troubles they will overcome.

5. **Scuttlebutt before management**: Never approach management first. Build your picture from customers, competitors, suppliers, and ex-employees first. Only visit management when you already have ~50% of what you need to know.

---

## WHEN TO READ THE REFERENCE FILES

- For a **full company evaluation**: read `references/fifteen-points.md` — contains all 15 criteria with detailed application guidance
- For **how to research a company**: read `references/scuttlebutt.md` — Fisher's intelligence-gathering methodology
- For **buy/sell timing**: read `references/when-to-buy-sell.md` — specific entry and exit rules
- For **portfolio construction or investor mistakes**: read `references/donts.md` — 10 common errors and diversification rules

---

## EXAMPLE ANALYSIS STRUCTURE

When asked "Is [Company X] a growth stock?", structure your response as:

**Fisher Growth Stock Analysis: [Company X]**

1. **Business Overview** (what it does, industry dynamics)
2. **15-Point Assessment** (score each point based on available information)
3. **Key Strengths** (what clearly qualifies)
4. **Key Concerns** (what is weak or unknown)
5. **Scuttlebutt Gaps** (what needs further research to determine)
6. **Verdict** (Outstanding / Solid Candidate / Not a Fisher Stock / Insufficient Data)
7. **If buying**: Timing considerations from `references/when-to-buy-sell.md`

Always note what information is unknown and requires scuttlebutt research. Fisher himself says he cannot make a confident judgment without that research — neither should we.
