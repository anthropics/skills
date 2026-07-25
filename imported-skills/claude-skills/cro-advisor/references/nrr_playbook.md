# NRR Playbook

Net Revenue Retention is the single most important metric for a SaaS company's health and valuation. A company with 120% NRR grows even if it closes zero new deals. A company with 80% NRR is filling a bucket with a hole in it.

---

## NRR Deep Dive

### The Fundamental Formula

```
NRR = (Opening MRR + Expansion MRR - Contraction MRR - Churned MRR) / Opening MRR

Example:
  Opening MRR:     $1,000,000
  Expansion:       +$150,000
  Contraction:     -$30,000
  Churn:           -$80,000
  Closing MRR:     $1,040,000
  NRR = $1,040,000 / $1,000,000 = 104%
```

### NRR vs. GRR

| Metric | Formula | What It Tells You |
|--------|---------|------------------|
| **GRR** | (Opening - Contraction - Churn) / Opening | Retention floor — how much you keep without any expansion |
| **NRR** | (Opening + Expansion - Contraction - Churn) / Opening | Net health — expansion offsetting churn |
| **Logo Retention** | (Customers start - Customers churned) / Customers start | Volume retention, ignores revenue weight |

**GRR is the floor. NRR is the ceiling.**

If GRR is 80% and NRR is 105%, your expansion is covering 25 points of churn. That's fragile — any expansion slowdown turns NRR negative. The fix is GRR, not more upsell.

### Benchmarks by Segment

| Segment | Good GRR | Good NRR | Exceptional NRR |
|---------|---------|---------|----------------|
| SMB-focused | 80-85% | 95-105% | > 110% |
| Mid-Market | 85-90% | 105-115% | > 120% |
| Enterprise | 90-95% | 115-130% | > 140% |

Enterprise NRR can exceed 140% because large accounts expand substantially and rarely churn entirely — they may downgrade but full logo churn is rare if the product is embedded.

### NRR by Cohort

Don't just measure NRR across the full base — measure it by customer cohort (month of acquisition).

```
Jan 2024 Cohort:
  Opening MRR (Jan 2024):  $50,000
  MRR at Jan 2025:         $62,000
  12-month NRR:             124%

Feb 2024 Cohort:
  Opening MRR (Feb 2024):  $45,000
  MRR at Feb 2025:         $38,000
  12-month NRR:             84%  ← problem cohort
```

Cohort analysis reveals:
- Whether a specific acquisition channel brings lower-quality customers
- Whether a product change or pricing shift affected retention
- Whether specific sales reps or time periods created bad-fit deals

---

## Churn Anatomy

Not all churn is equal. Know the breakdown before prescribing solutions.

### Churn Types

| Type | Definition | Primary Cause | Fix |
|------|-----------|--------------|-----|
| **Logo churn** | Customer cancels entirely | No value, poor fit, champion left, competitor | Root cause analysis, ICP tightening |
| **Revenue churn** | ARR lost (cancels + downgrades combined) | Same as logo + downgrade triggers | Address both volume and revenue |
| **Involuntary churn** | Failed payment, expired card | Billing friction | Dunning improvement (quick win: 20-30% recovery) |
| **Voluntary churn** | Active cancellation decision | Explicit dissatisfaction, competitor win | Exit interview + intervention program |
| **Contraction** | Downgrade, seat reduction | Overpurchased, budget cut, team reduction | Right-sizing program, annual contracts |

### Churn Root Cause Framework

Run this analysis quarterly on all churned accounts:

**Step 1: Categorize by reason**
- No value realized (never activated or adopted)
- Value realized but budget cut (external, not product)
- Switched to competitor (why? what did they offer?)
- Champion left company (relationship loss, not product failure)
- Company shutdown / acquisition (unavoidable)

**Step 2: Look for patterns**
- Which ICP signals predict churn? (company size, vertical, acquisition channel)
- Which product behaviors predict churn? (no login in 30 days, never completed onboarding)
- Which time periods have highest churn? (months 3, 6, 12 are typical cliff points)

**Step 3: Act on the patterns**
- ICP pattern → tighten qualification criteria
- Behavior pattern → build early warning health score
- Time cliff → build intervention playbooks for months 2, 5, 11

### Exit Interview Protocol

Talk to every churned customer if ACV > $10K. For smaller, do quarterly batch surveys.

Questions:
1. "What was the primary reason for your decision to cancel?"
2. "What would have needed to be true for you to stay?"
3. "What did you switch to, and what drove that decision?"
4. "Was there a specific moment when you decided to leave?"

Rules:
- CSM who owned the account should NOT conduct the exit interview (too much relationship bias)
- Use a neutral party or the VP CS
- Document verbatim, not paraphrased
- Feed patterns back to Product and Sales monthly

---

## Customer Health Scoring

A health score predicts churn 60-90 days before it happens. Without one, you're reactive.

### Health Score Components

Score each account 0-100 across weighted signals:

| Signal | Weight | Red (0-33) | Yellow (34-66) | Green (67-100) |
|--------|--------|-----------|---------------|---------------|
| **Product usage** (DAU/WAU, feature adoption depth) | 35% | < 20% seats active | 20-60% seats active | > 60% seats active |
| **Engagement** (QBR attendance, champion responsiveness) | 20% | No response 60+ days | 30-60 days | Active, < 30 days |
| **NPS / CSAT** | 20% | Score < 6 | Score 6-7 | Score 8-10 |
| **Support volume** (negative signal: high volume = friction) | 15% | > 10 tickets/month | 3-10/month | < 3/month |
| **Contract signals** (time to renewal, expansion in motion) | 10% | < 60 days to renewal, no expansion discussion | 60-90 days, passive | > 90 days, expansion active |

**Composite score:**
- 70-100: Healthy. Renewal confident. Identify expansion opportunity.
- 50-69: At-risk. CSM check-in required. Executive sponsor loop-in if < 60 days to renewal.
- 0-49: Red alert. Immediate intervention. VP CS or CEO call if strategic account.

### Health Score Automation

Trigger alerts automatically:
```
Score drops > 20 points in 30 days → CSM immediate outreach (same day)
No product login in 14 days → Automated email + CSM flag (within 24 hours)
Champion leaves company → Executive outreach (within 24 hours)
Support escalation → CSM loop-in (within 2 hours)
Renewal < 90 days + score < 60 → VP CS review (weekly)
Seat utilization < 30% → Adoption intervention playbook triggered
```

### Leading Indicators vs. Lagging Indicators

| Leading (predict future churn) | Lagging (confirm past churn) |
|-------------------------------|------------------------------|
| Login frequency declining | Cancellation submitted |
| Feature adoption stalling at basic level | Non-renewal at contract end |
| NPS score trend (not just snapshot) | Downgrade executed |
| No QBR scheduled in 90+ days | Champion departure |
| Support escalations increasing | Competitor mentioned in support |

Build your health score from leading indicators. Lagging indicators tell you what already happened.

---

## Expansion Revenue Strategies

Expansion is cheaper than acquisition. CAC for expansion is typically 20-30% of new logo CAC.

### Expansion Motion 1: Seat Expansion

**Trigger signals:**
- Usage by unlicensed users (shared logins, "can you add my colleague?")
- Team growth visible on LinkedIn (company hiring in target department)
- Champion promotes to a new role with bigger team
- Power users at license limit consistently

**Playbook:**
1. Pull monthly usage report showing which features unlicensed users are using
2. Frame as: "Your team is getting value from X — you could be capturing that for the full team"
3. Offer a team expansion proposal at renewal + 10% volume discount for seat adds
4. Never penalize users for sharing logins before the conversation — that's a data asset

### Expansion Motion 2: Upsell (Tier Upgrade)

**Trigger signals:**
- Customer consistently hitting usage/feature limits
- Security or compliance requirement that requires higher tier
- New stakeholder joining who needs admin controls
- API usage growing rapidly (engineering team engagement)

**Playbook:**
1. Build a "value realized" report before the upsell conversation (ROI proof)
2. Use QBR as the venue: "You've achieved X. Here's what's possible at the next level."
3. Frame the upgrade as unlocking more of what's already working
4. Time to renewal: start upsell conversation 90-120 days before renewal

### Expansion Motion 3: Cross-sell

**Trigger signals:**
- Strategic account with adjacent problem your product can solve
- New product launch that complements existing usage
- Customer explicitly asks about a capability in your roadmap or adjacent product

**Playbook:**
1. Land with core product; build relationship and prove value
2. Cross-sell only after health score is green and NPS > 7
3. Introduce the new product through a champion, not a cold pitch
4. Pilot pricing: bundle into renewal at modest uplift vs. separate sale
5. Cross-sell owner: CSM or AE (define explicitly — joint ownership = no ownership)

### Expansion Sequencing

Don't try all three simultaneously. Sequence matters:

```
Month 0-3:   Activation focus — ensure core value delivered
Month 3-6:   Seat expansion — grow usage within existing team
Month 6-9:   Upsell conversation — unlock advanced features
Month 9-12:  Cross-sell OR renewal + multi-year lock-in
```

### NRR Modeling

Target breakdown for 115% NRR:

```
GRR:                  88% (12% lost to churn/contraction)
Expansion rate:       27% (upsell + cross-sell + seat expansion)
NRR:                  88% + 27% = 115%

To reach 120% NRR:
  Option A: Improve GRR to 92% (reduce churn), keep expansion at 28%
  Option B: Keep GRR at 88%, improve expansion to 32%
  Option C: Both, incrementally

Option A is usually easier and more durable. Fix the hole first.
```

---

## Customer Success Integration

CS and Revenue are not separate functions. NRR lives at their intersection.

### CS Team Structure (aligned to NRR)

| CS Model | When to Use | NRR Focus |
|----------|------------|-----------|
| **High-touch CSM** | ACV > $25K | Named accounts, QBRs, executive relationships |
| **Tech-touch / pooled** | ACV $5K-25K | Automated health scoring, office hours, community |
| **Self-serve** | ACV < $5K | In-app guidance, knowledge base, email sequences |

**CSM coverage ratios:**
- High-touch: 1 CSM per $2M-4M ARR managed
- Tech-touch: 1 CSM per $5M-10M ARR managed
- Self-serve: Product and automation (no dedicated CSM)

### CS Compensation (aligned to NRR)

Don't pay CSMs a flat salary — align incentive to retention and expansion:

```
CS compensation structure:
  Base: 70% of OTE
  Variable: 30% of OTE

Variable tied to:
  GRR / NRR vs. target (50% of variable)
  Health score improvement (25% of variable)
  Expansion ARR facilitated (25% of variable)

Do NOT pay CS commission on expansion ARR the same way AEs earn it.
This creates conflict: CS will push expansion before the customer is ready.
Instead, bonus for expansion milestones — it's a different incentive structure.
```

### QBR (Quarterly Business Review) Framework

QBRs are the primary vehicle for expansion and churn prevention in enterprise accounts.

**QBR agenda (60-90 minutes):**
1. **Their goals, our progress** — review what they said success looked like at kickoff (10 min)
2. **Usage and adoption data** — product metrics presented in business language, not feature language (15 min)
3. **Value delivered** — ROI proof: time saved, revenue influenced, risk reduced (10 min)
4. **Challenges and blockers** — what's preventing more adoption? (10 min)
5. **Roadmap preview** — upcoming features relevant to their use case (10 min)
6. **Next 90 days** — joint success plan with owner and due dates (10 min)
7. **Expansion opportunity** — if health score is green and timing is right (10 min)

**QBR anti-patterns:**
- Leading with your product roadmap (they don't care; start with their results)
- Bringing too many people from your side without matching seniority
- Presenting at a VP without bringing the economic buyer
- Skipping QBRs for "healthy" accounts (health can change fast)
- No confirmed next step at the end

---

## Cohort-Based Retention Analysis

Aggregate NRR hides the signal. Cohort analysis reveals it.

### Retention Curve Analysis

Plot retention by months since acquisition for each quarterly cohort:

```
Month 0:  100% (starting revenue)
Month 3:  First cliff — early adopters who didn't activate churn here
Month 6:  Second cliff — customers who never expanded, running out of runway
Month 12: Renewal cliff — annual contract renewal decision
Month 18: Mature customers — churn rate stabilizes significantly

Healthy curve: Drops sharply in months 1-3, flattens after month 6
Problem curve: Continues declining linearly through month 12+ (no value anchor)
```

### Reading Cohort Data

| Pattern | Interpretation | Action |
|---------|---------------|--------|
| Early churn (months 1-3) | Onboarding / activation failure | Fix time-to-value, improve onboarding |
| Mid-cycle churn (months 4-8) | Value not deepening | Adoption program, check product fit |
| Annual renewal churn (month 12) | Buying committee didn't renew | Executive engagement, earlier renewal process |
| Flat after month 6 | Sticky product, low expansion | Increase upsell motion |
| Growing after month 6 | Expansion working | Scale the upsell playbook |

### Cohort Segmentation Variables

Slice retention cohorts by:
- **Acquisition channel** (inbound vs. outbound vs. PLG vs. partner)
- **Sales rep** (which reps close durable deals vs. churny deals)
- **Deal size** (SMB churn rate typically 2-3x enterprise)
- **Industry vertical** (some verticals have structurally higher churn)
- **Product tier at signup** (self-serve → converted vs. directly contracted)
- **Geographic market** (international markets often have different retention profiles)

The most actionable finding is usually by acquisition channel or sales rep — both are directly controllable.

### Churn Prevention Intervention Playbooks

**Playbook 1: Low Activation (no login in first 14 days)**
```
Day 7:   Automated email: "Getting started" + specific next step
Day 14:  CSM outreach: "I noticed you haven't logged in — can I help?"
Day 21:  Escalate to CSM manager if no response
Day 30:  Executive outreach for ACV > $25K; flag as at-risk
```

**Playbook 2: Usage Cliff (DAU drops > 50% in 30 days)**
```
Trigger:  Automated health score alert
Day 1:    CSM reviews usage report, identifies likely cause
Day 2:    CSM outreach: "We noticed your team's usage changed — is everything okay?"
Day 7:    If no response: schedule 30-min call with champion
Day 14:   If unresponsive: VP CS loop-in + executive reach out
```

**Playbook 3: Champion Departure**
```
Trigger:  LinkedIn alert or internal report of champion leaving
Day 1:    Email to departed champion (warm handoff ask)
Day 1:    Email to new stakeholder (introduction from AE or VP CS)
Day 3:    Schedule onboarding call for new stakeholder
Day 14:   QBR with new stakeholder to establish relationship
Day 30:   Health score review — flag if engagement hasn't recovered
```

**Playbook 4: Pre-Renewal (90 days out, health score < 70)**
```
Day -90: CSM completes account health review, escalates if < 70
Day -75: Executive sponsor from vendor side joins renewal call
Day -60: Value delivered report prepared (ROI proof)
Day -45: Renewal proposal sent with expansion option
Day -30: Follow-up on any open objections or requirements
Day -14: Final confirm or escalate to VP Sales
```
