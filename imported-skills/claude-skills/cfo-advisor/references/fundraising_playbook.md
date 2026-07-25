# Fundraising Playbook

From timing to close. What investors actually look for, how valuation works, and the term sheet clauses that matter.

---

## 1. When to Raise

**Optimal timing:**
```
Target: 18-24 months runway post-close
Minimum: 12 months runway post-close (leaves no buffer for slip)

Start process when: 9-12 months runway remaining
  → 3-6 months for process (typically 4-5 months for Series A/B)
  → Leaves 3-6 months buffer if process drags

Never start when: < 6 months runway
  → You're negotiating from desperation
  → Investors can smell it
  → Terms get worse, or you don't close at all
```

**Rule:** Your leverage is maximum when you don't *need* to raise. Raise from a position of momentum, not necessity.

---

## 2. What Investors Look For at Each Stage

### Pre-seed
- Team (are these people credible for this problem?)
- Problem clarity (is the problem real and meaningful?)
- Early signal (any customers paying, waitlist, prototype)
- Market size (worth building a VC-scale company?)

**Typical ask:** $500K–$2M | **Typical valuation:** $3M–$10M pre-money

### Seed
- Product-market signal (customers using and paying)
- Founding team with domain expertise
- ARR: $100K–$1M (or strong usage for PLG)
- Clear hypothesis for what Series A looks like

**Typical ask:** $2M–$5M | **Typical valuation:** $8M–$20M pre-money

### Series A

Investors are buying a *repeatable sales motion*. Not just customers — a machine.

**What they need to see:**
- ARR: $1M–$5M growing > 100% YoY
- LTV:CAC > 2.5x (and improving)
- Net Dollar Retention > 100%
- CAC Payback < 18 months
- Gross margin > 65%
- At least 5-10 reference customers (not just lighthouse)
- Sales motion that converts without the founder closing every deal

**Typical ask:** $8M–$15M | **Typical valuation:** $25M–$60M pre-money

### Series B

Investors are buying *scalable go-to-market*. Can you pour fuel on the fire?

**What they need to see:**
- ARR: $5M–$20M growing > 100% YoY
- LTV:CAC > 3x, CAC Payback < 18 months
- Sales capacity model (hiring plan → pipeline → revenue)
- NDR > 110% (expansion motion working)
- Some proof of market expansion (new segments, geographies, use cases)
- Path to category leadership

**Typical ask:** $15M–$40M | **Typical valuation:** $60M–$200M pre-money

### Series C and Beyond

Investors are buying *market leadership* and *path to profitability*.

**What they need to see:**
- ARR: $20M+ (often $30-50M for credible Series C)
- Rule of 40 > 40 (or credible path)
- Gross margin > 70%
- NDR > 115%
- Evidence of market leadership (brand, win rates, analyst mentions)
- Clear path to $100M+ ARR

---

## 3. Valuation Methods

### Revenue Multiples (Primary Method for SaaS)

```
Pre-money Valuation = ARR × Revenue Multiple

Revenue multiple benchmarks (2024-2025):
  > 100% YoY growth:  8x–15x ARR
  50-100% YoY growth: 4x–8x ARR
  20-50% YoY growth:  2x–4x ARR
  < 20% YoY growth:   1x–2x ARR

Adjustments:
  NDR > 120%:          +1x–2x premium
  Gross margin > 75%:  +0.5x–1x premium
  Burn multiple < 1x:  +0.5x–1x premium
  Capital efficient:   Investors pay up for efficiency
  Declining growth:    Compress multiple aggressively
```

### The Investor's Math (Know This)

Every VC has a required return. Work backwards from their constraints:

```
Investor targets: 3x fund return
Fund size: $200M, check size: $15M (initial), $25M (with follow-on)
Ownership at exit needed: 15%
At 15% ownership: needs $25M / 15% = $167M post-money valuation
Exit needed to return 3x on that check: $25M × 10 = $250M company value
  (10x because most deals fail, winners must carry the fund)

Implication: If you think you'll exit for $150M, that VC will pass or price you accordingly.
```

This is why Series A investors rarely lead rounds where they can't see a $300M+ exit path. It's not about your business being bad — it's about fund math.

### Comparable Company Analysis

For later stages (Series B+):

```
1. Find 5-10 comparable public SaaS companies
2. Calculate their EV/NTM Revenue multiples (use latest data)
3. Apply a private market discount (typically 20-40% vs public comps)
4. Adjust for your growth rate relative to comps

Example (2024):
  Public SaaS comps: 6x NTM Revenue (median)
  Private discount: 30%
  Adjusted: ~4.2x
  Your NTM Revenue: $8M
  Implied valuation: ~$33M pre-money
```

### DCF (Late Stage Only)

DCF is unreliable for early-stage startups (terminal value dominates, growth rate assumptions are fantasy). Use it as a sanity check at Series C+, not as the primary valuation method.

---

## 4. Term Sheet Breakdown

### Liquidation Preference (Most Important Economic Term)

This determines who gets paid first in an exit — and how much.

```
1x Non-Participating Preferred (BEST for founders):
  Investor gets 1x money back OR converts to common (their choice).
  At acquisition: investor takes larger of {1x invested} or {% ownership × proceeds}
  Example: $10M invested, exits at $100M, owns 20%
    Option A: $10M (1x)
    Option B: $20M (20% of $100M)
    Investor takes $20M. Founders split $80M.

1x Participating Preferred (WORSE for founders):
  Investor gets 1x money back AND participates in remaining proceeds.
  Example: same scenario
    $10M (1x) + 20% of remaining $90M = $10M + $18M = $28M
    Founders split $72M instead of $80M
    Cost to founders: $8M (10% of exit value)

2x Participating (RED FLAG):
  Investor gets 2x back AND participates.
  Only accept under duress. Push hard against this.

Full Ratchet Anti-Dilution (AVOID):
  Down-round triggers full repricing of investor shares to new (lower) price.
  Founders get massively diluted. Never accept if alternatives exist.
```

### Anti-Dilution Protection

```
Broad-based weighted average (standard):
  Adjusts investor conversion price based on all dilutive securities.
  Most founder-friendly anti-dilution. Accept this.

Narrow-based weighted average (slightly worse):
  Same mechanism but uses smaller denominator.
  Gives investors slightly more protection. Usually acceptable.

Full ratchet (avoid):
  Price drops to whatever the new round prices at.
  Devastating in down rounds. Fight this.
```

### Pro-Rata Rights

```
Standard pro-rata: Investor can maintain their % ownership in future rounds.
  Reasonable. Accept for major investors.

Super pro-rata: Investor can increase their % in future rounds.
  Caps your ability to bring in new lead investors.
  Avoid unless the investor is exceptional and you want them in future rounds.

Major investor threshold: Typically investors with > $500K–$1M check get pro-rata.
  Don't give pro-rata to every small check — clogs future rounds.
```

### Board Composition

```
Seed (3 members):     2 founders, 1 lead investor
Series A (5 members): 2 founders, 2 investors, 1 independent
Series B (5-7 seats): Watch for investor majority — negotiate hard

Rule: Founders should retain majority through Series A.
      Independent director should be your choice, not investor's.
      Never accept investor majority before Series C.

Board observer rights: Common for smaller investors. No vote but present in meetings.
                       Limit to 1-2 observers or meetings become unwieldy.
```

### Other Terms That Matter

```
Drag-along: Majority can force minority shareholders to vote for acquisition.
  Standard and reasonable. Check what threshold triggers drag.

Information rights: Investors get financial statements.
  Standard. Monthly for major investors, quarterly for others.

Redemption rights: Investors can force buyback after X years.
  Push to remove or add carve-outs for insufficient funds.

No-shop clause: You can't shop the term sheet to other investors.
  Standard (14-30 days). Reasonable.

Exclusivity: Stronger version of no-shop. Sometimes includes no other fundraise discussions.
  Acceptable for 30 days; push back on > 45 days.
```

---

## 5. Cap Table Management

### Dilution Planning Model

Run this before every round. Know your number before walking into any negotiation.

```
         Pre-Seed    Post-Seed    Post-A    Post-B    Post-C
Founder A  45.0%      36.0%       26.5%     21.2%     18.7%
Founder B  45.0%      36.0%       26.5%     21.2%     18.7%
Angel 1     5.0%       4.0%        2.9%      2.4%      2.1%
Angel 2     5.0%       4.0%        2.9%      2.4%      2.1%
Seed Fund      -      12.0%        8.8%      7.1%      6.2%
Option Pool    -       8.0%       12.0%     10.0%      8.0%
Series A       -          -       20.4%     16.3%     14.4%
Series B       -          -           -     19.5%     17.2%
Series C       -          -           -         -     12.6%

Round size / pre-money:
Pre-Seed: $500K / $9M pre = 5% dilution
Seed: $2M / $8M pre = 20% dilution (includes 8% pool)
Series A: $10M / $38M pre = 20.8% dilution (pool refresh to 12%)
Series B: $20M / $80M pre = 20% dilution
Series C: $30M / $170M pre = 15% dilution
```

**Option pool shuffle:** Investors often require you to create/expand the option pool *before* the round closes, which dilutes existing shareholders (not the incoming investor). Model this explicitly — a 20% round with a 5% pool expansion is really 24%+ dilution to founders.

### Cap Table Hygiene

```
Tools: Carta, Pulley, Capshare (all acceptable)
Never: Track cap table in a spreadsheet past seed stage. Errors compound.

Keep it clean:
  - Repurchase departed co-founder shares immediately (don't let unvested shares linger)
  - Convert SAFEs to equity cleanly at each priced round
  - Document every grant with a board resolution
  - Cliff + vesting for ALL employees and founders (standard: 1-year cliff, 4-year vest)
  - 409A valuation required before every option grant (IRS requirement)
```

---

## 6. Data Room Preparation

### Core Documents (Required)

```
Financial:
  □ 3 years historical financials (or all history if < 3 years)
  □ Monthly P&L and cash flow (last 24 months)
  □ Current financial model (18-24 months forward)
  □ Budget vs actual (last 4 quarters)
  □ Cap table (fully diluted, with all SAFEs/convertibles modeled)
  □ Bank statements (last 3-6 months)

Legal:
  □ Certificate of incorporation + all amendments
  □ All prior financing documents (SAFEs, convertible notes, stock purchase agreements)
  □ Cap table (Carta/Pulley export)
  □ IP assignment agreements (all founders and employees)
  □ Material contracts (top 10 customers, key vendors)
  □ Employee list (titles, start dates, salaries, equity grants)

Product & Business:
  □ Product demo / walkthrough video
  □ Architecture overview (for technical investors)
  □ Customer case studies (3-5 named references)
  □ NPS / CSAT data
  □ Competitive landscape analysis

Metrics:
  □ MRR/ARR by month (all history)
  □ Cohort retention chart
  □ CAC by channel
  □ LTV by cohort
  □ NPS trend
```

### What Investors Actually Check First

In order of typical priority during due diligence:

1. **Cap table** — Is it clean? Any concerning structures?
2. **Cohort retention** — Is churn improving or deteriorating?
3. **Revenue quality** — What % is recurring? Any one-time or non-recurring?
4. **Top 10 customers** — Concentration risk? Any logos at risk?
5. **Bank statements** — Does cash match what was reported?
6. **IP assignments** — Does the company own its IP? (Founders who didn't assign IP kill deals)

### Red Flags That Kill Deals

- Missing IP assignment agreements for founders (most common deal killer at early stage)
- Cap table with > 20 angels/small investors (messy, hard to get consent for future rounds)
- Customer concentration > 30% in single customer without explanation
- Revenue recognition issues (booking ARR on contracts that allow easy cancellation)
- Cohort data that gets worse in later cohorts
- Bank balance doesn't match reported cash position

---

## 7. Investor Communication Cadence

### During Fundraise

```
Week 1-2:   Warm intro sourcing, LP/network mapping
Week 3-6:   First meetings (aim for 20-30 first meetings)
Week 7-10:  Partner meetings, deep dives, due diligence
Week 11-14: Term sheets, negotiation
Week 15-18: Legal, closing
```

**Parallel process is essential.** Never negotiate with one investor at a time. Competition is your leverage.

### Post-Close: Investor Updates

Monthly investor update (send within 10 days of month-end):

```
Subject: [Company] Monthly Update — [Month Year]

Highlights (3 bullets max):
  • [Biggest win]
  • [Biggest learning/challenge]
  • [What we're focused on next month]

Metrics:
  ARR: $X (+X% MoM)
  Net new ARR: $X
  Gross margin: X%
  Cash: $X (X months runway)
  Headcount: X

Asks (be specific):
  • Looking for intro to [persona/company] for [specific reason]
  • Need advisor with experience in [specific area]
  • [Other concrete ask]
```

**Why this matters:** Investors who are informed and engaged are better positioned to help when you need it. The investor who hasn't heard from you in 6 months is less likely to write a bridge check or make a warm intro when you ask.

---

## Key Formulas

```python
# Post-money valuation
post_money = pre_money + investment_amount

# Investor ownership %
ownership_pct = investment_amount / post_money

# Dilution to existing shareholders
dilution = investment_amount / post_money  # as a fraction

# New shares issued
new_shares = (investment_amount / post_money) * total_post_shares
# equivalent: new_shares = pre_money_shares * (investment_amount / pre_money)

# Option pool expansion impact (pool shuffle)
# Creating X% option pool pre-close dilutes founders:
pool_shares_needed = target_pct * (pre_shares + new_round_shares + pool_shares_needed)
# Solve: pool_shares_needed = target_pct * (pre_shares + new_round_shares) / (1 - target_pct)

# LTV:CAC ratio
ltv_cac = ltv / cac  # target: > 3x

# CAC payback (months)
payback_months = cac / (arpa * gross_margin_pct)
```
