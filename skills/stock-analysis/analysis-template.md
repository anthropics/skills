# Analysis Output Template

This template defines the structure and tone for the final Stage 8 output — the synthesis delivered to the user after all eight stages are complete. It is a guide, not a rigid script. Adapt based on what the user actually needs.

---

## Header block

```
[COMPANY NAME] ([TICKER]) — Investment Analysis
Price: $X | Your cost: $X | Position: X% of portfolio | Horizon: X years
Analysis date: [date]
```

---

## Section order

### 1. Stage 2 — Business and moat analysis

**What to cover:**
- Which value chain layer does this company sit in?
- What is the actual moat — specific type, not generic claim
- What is "owned" vs. "rented" in the moat
- Who are the real competitors, including non-obvious threats
- Pricing power test (gross margin trend interpretation)
- Moat verdict with durability horizon and score /10

**Tone**: Analytical and specific. Push back on lazy moat characterizations ("they have great AI"). Be honest if the moat is contested.

---

### 2. Stage 3 — Financial stress-test

**What to cover:**
- Key headline numbers (revenue, margins, FCF, balance sheet snapshot)
- What the numbers are telling you that headlines don't say
- At least one stress scenario (what does the stock look like if margins compress 15–20%?)
- Margin sustainability question — is the current margin a floor or a ceiling?
- Financial strength verdict and score /10

**Tone**: Forensic, not celebratory. Strong financials are noted but high margins are always paired with a sustainability question.

---

### 3. Stage 4 — Competitive and sector context

**What to cover:**
- 2–3 key competitor comparisons (growth, margin, valuation)
- The sector re-rating context (is the whole sector down, or is this specific?)
- Hyperscaler / platform threat analysis
- Is there a cheaper way to express the same thesis?

**Tone**: Broad view. Put the company in context before concluding anything.

---

### 4. Stage 5 — Valuation

**What to cover:**
- Current multiples vs. company's own 5-year history
- Current multiples vs. peer comparison
- What growth rate the current multiple implies
- Reverse-DCF sanity check (what does the stock need to deliver X% IRR?)
- Valuation verdict and score /10

**Format tip**: Use a compact table for multiples:

```
Metric      | Current | 5-yr median | Read
------------|---------|-------------|------
Forward P/E | 24x     | 41x         | Below median
P/S (fwd)   | 17x     | 6x          | Expensive
PEG         | 0.7     | —           | Attractive if growth holds
```

---

### 5. Stage 6 — Behavioral bias audit

**What to cover:**
- The five mandatory questions from `references/behavioral-psychology.md`
- Which specific biases are detected in this situation
- The "zero-shares" test result
- Whether the user has a written sell trigger (and if not, help them build one)
- Thesis clarity verdict and score /10

**Tone**: Direct and caring. The bias audit is an act of service, not judgment. The goal is to surface the expensive mistake before it's made, not to make the user feel bad. Be warm but do not soften the hard truths.

**Important**: If the user admits they don't understand the stock well, this section becomes the most important of the entire output. Do not bury this. Bring it forward. The recommendation changes when Thesis Clarity < 5.

---

### 6. Stage 7 — Hard questions

**Format**: 3–5 specific, uncomfortable questions that directly confront the weakest part of the thesis. Write them as direct questions, then follow each with your own analytical answer (since the user may not have the answer yet).

```
1. [The hardest question]
   → [Your answer, including what you don't know]

2. [Second hardest question]
   → [Your answer]
```

---

### 7. Stage 8 — Score and position sizing

**Score table:**

```
Dimension              | Score /10 | Reasoning
-----------------------|-----------|----------
Business quality       | X         | [1-2 sentence justification]
Moat durability        | X         | [1-2 sentence justification]
Financial strength     | X         | [1-2 sentence justification]
Management quality     | X         | [1-2 sentence justification]
Valuation attractiveness| X        | [1-2 sentence justification]
Thesis clarity         | X         | [1-2 sentence justification]
Risk/reward asymmetry  | X         | [1-2 sentence justification]

Weighted composite: X.X / 10
```

**Volatility classification**: [Class] — state the classification and max position size ceiling

**Conviction level**: [High / Medium / Low / Exploratory] — one sentence explanation

**Position sizing recommendation**: Specific. Not "consider adding." Specific tranches and conditions.

```
Current position: X% (appropriate / too large / too small given the analysis)

Recommendation: [Hold / Do not add / Consider trimming / Add in stages]

If adding:
  Tranche 1: [Amount] at [condition or current price]
  Tranche 2: [Amount] at [price or catalyst condition]
  Tranche 3: [Amount] at [further pullback or specific event]

  Absolute maximum for this name: X% of equity portfolio

Written sell triggers:
  Exit fully if: [specific event]
  Trim 50% if: [specific event]
  Hold through if: [price-only decline with no new fundamental negative]

Re-evaluation schedule:
  Next check: [date or event — typically next earnings]
  Ongoing: [quarterly or after each material news event]
```

---

### 8. Summary in plain English

End with a 3–5 sentence plain-language summary that a non-analyst could understand. No jargon. No score references. Just the honest bottom line.

This summary is often the thing the user will remember. Make it accurate, make it actionable, and make it honest.

---

### 9. Standard disclaimer

Always close with this disclaimer, written as a genuine note — not a legal boilerplate:

*This analysis is a structured framework for thinking, not personalized financial advice. Your individual financial situation — tax circumstances, income stability, other holdings, timeline to needing capital — matters more than any single-stock analysis can account for. Specific legal and regulatory risks (like an active SEC investigation) are sources of genuine uncertainty that professional analysts cannot confidently handicap. Treat this as a starting point for your own thinking, not an endpoint.*

---

## Tone calibration

**Across the whole output:**
- Warm and service-oriented, not impressive-sounding
- Honest about uncertainty — "I don't know" is a valid and important answer
- Direct when the user is making a mistake — not cruel, not soft
- Never condescending — the user is trusting Claude with real money
- Avoid false precision — a rating of 6.5/10 that implies exactness is misleading. Ranges and hedging are fine.
- Do not over-complicate. The most valuable thing Claude can provide is clear thinking, not impressive-looking analysis.

**On the hard findings:**
If the analysis reveals that the user is about to make a mistake — adding before understanding the business, sizing up in a stock with an active regulatory threat, averaging into a loser using loss-recovery rationalization — say it clearly. Say it gently. Say it once. But say it. That is the highest-value service this skill can deliver.

**On uncertainty:**
Use phrases like:
- "The structural case suggests..."
- "The balance of evidence points to..."
- "This is genuinely uncertain — here's what you'd need to be true..."
- "I don't know how this resolves, and anyone who says they do is overconfident..."

Never use: "This will happen," "This is definitely a buy," "You should X."
