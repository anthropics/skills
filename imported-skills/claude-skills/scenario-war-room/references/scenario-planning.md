# Scenario Planning Reference

## Shell's Scenario Planning Methodology

Shell invented modern scenario planning in the 1970s after the oil crisis. Core insight: **scenarios are not forecasts — they're tools for thinking.**

### Shell's Principles (adapted for startups)
1. **Scenarios are mutually exclusive, collectively exhaustive** — they cover the space of possibilities without overlapping
2. **2x2 matrix** — pick 2 critical uncertainties (not risks — uncertainties); cross them to get 4 scenarios
3. **Name the scenarios** — named scenarios are remembered; numbered ones aren't
4. **Identify predetermined elements** — things that will happen regardless of scenario (regulatory changes, tech trends)
5. **Early indicators** — each scenario has signals you can monitor today

### Shell's 2x2 for Startups
Critical uncertainties for early-stage SaaS:

| | Market grows fast | Market grows slow |
|---|---|---|
| **We raise successfully** | "Blue Ocean" — execute hard | "Ramp Carefully" — efficiency focus |
| **We bridge/delay raise** | "Scrappy Growth" — ramen profitability | "Survival Mode" — cut to core |

Build your war room sessions around whichever quadrant is most relevant right now.

---

## Monte Carlo Thinking for Startups

Monte Carlo = running thousands of simulations with random variables to understand probability distributions.

You don't need software. Apply the mental model:

### The Mental Monte Carlo Process
1. **Identify the key variables** (3-5 max)
2. **Assign ranges** — not point estimates
   - CAC: $6K–$12K (uniform distribution)
   - Close rate: 20%–40% (normal, mean 30%)
   - Churn: 5%–20% (right-skewed — bad tail is worse)
3. **Run mental scenarios** — pick low/mid/high for each
4. **Identify the combinations that kill you** — which variable combinations make runway hit zero?
5. **Focus hedging on** the 20% of combinations that account for 80% of kill scenarios

### Practical Monte Carlo Heuristic
For revenue forecasting, always state:
- **P90** (90% confidence you'll exceed this)
- **P50** (median case)
- **P10** (only 10% chance you'll exceed this — your "stretch")

Boards respect ranges. Point estimates are usually wrong and make you look naive.

---

## Pre-Mortem Technique

A pre-mortem asks: *"It's 12 months from now. We failed. Why?"*

It's the opposite of planning (which asks why you'll succeed). It surfaces hidden risks that optimism suppresses.

### Running a Pre-Mortem
**Setup:**
- Time: 90 minutes
- Participants: leadership team
- Facilitator: neutral (COO, or external)
- Assumption: "It's [date 12 months out]. The company failed / missed its major goal. This is real."

**Phase 1 — Silence (10 minutes):**
Each person writes their top 3 reasons the failure happened. No discussion.

**Phase 2 — Round Robin (30 minutes):**
Each person shares one reason per turn. Facilitator captures on whiteboard. No debate yet.

**Phase 3 — Cluster (20 minutes):**
Group similar causes. Identify the top 5 clusters.

**Phase 4 — Probability & Impact (20 minutes):**
For each cluster: P(likely) × impact = risk score. Rank.

**Phase 5 — Mitigation (10 minutes):**
Top 3 risks: what one action would most reduce each?

### Pre-Mortem Prompt Variants
- "It's March 2027. We ran out of money. Why?"
- "It's Q4. We lost 3 enterprise customers in 60 days. What happened?"
- "It's next year. Our top competitor took 40% of the market. How?"
- "It's 18 months from now. Half the engineering team left. What triggered it?"

---

## Cascade Effect Mapping

Cascades are where most startups get surprised. The first hit is expected — the second and third aren't.

### Cascade Mapping Format
Draw as a chain:

```
INITIAL EVENT
    ↓ [immediate effect: domain, severity, timeline]
SECONDARY EFFECT
    ↓ [cascade mechanism: how A causes B]
TERTIARY EFFECT
    ↓ [cascade mechanism]
END STATE [runway impact, ARR impact, team impact]
```

### Common Cascade Patterns

**Revenue → Cash → People:**
```
Customer churns ($400K ARR)
    ↓ CFO: runway drops 14→9 months; bridge needed
    ↓ CHRO: hiring freeze; morale drops; attrition risk
    ↓ CTO: roadmap slips; key engineers leave for certainty
    ↓ CPO: product quality drops; more churn risk
    ↓ CRO: harder to win new logos without product velocity
END STATE: Death spiral if not interrupted at step 2
```

**Fundraise → Operations → Product:**
```
Fundraise delayed 6 months
    ↓ CFO: bridge at unfavorable terms; equity dilution
    ↓ COO: freeze all non-essential spend; process degrades
    ↓ CPO: roadmap cut to 40% of planned scope
    ↓ CTO: no infra investment; tech debt accelerates
    ↓ CRO: product gaps start losing deals to feature-complete competitors
END STATE: Weaker position at next raise; lower valuation
```

**People → Product → Revenue:**
```
Lead engineer + 2 seniors leave (30% of eng team)
    ↓ CTO: velocity drops 50%; critical features slip Q3→Q4
    ↓ CPO: Q4 launch cancelled; roadmap confidence collapses
    ↓ CRO: 3 enterprise deals cite product timeline → delays/losses
    ↓ CFO: $600K pipeline at risk; raises needed earlier
END STATE: Fundraise from position of weakness; team morale spiral
```

### Identifying Cascade Break Points
Every cascade has a point where intervention is cheapest. Find it:
- Step 1: Very expensive to prevent (existential)
- Step 2: Moderate cost (management action)
- Step 3: Cheap (early signal response)

Always try to interrupt at Step 2 or earlier.

---

## Trigger-Based Contingency Plans

Triggers are measurable signals you commit to acting on **before** the scenario fully materializes.

### Trigger Design Principles
1. **Measurable** — not "things look bad" but "cash below $800K"
2. **Leading, not lagging** — triggers should fire 60-90 days before the crisis
3. **Pre-committed responses** — when trigger fires, the action is already decided
4. **Owner assigned** — who watches for this trigger?

### Trigger Examples

**Cash / Runway:**
```
Trigger: Cash drops below $1M (or runway < 6 months)
Pre-committed response:
  - CFO: activate credit line within 48 hours
  - CEO: begin bridge conversations with existing investors
  - COO: implement 20% spend reduction plan (already drafted)
Owner: CFO (weekly cash report to CEO)
```

**Customer Health:**
```
Trigger: Any customer >10% ARR shows 3 of: [sponsor gone dark, usage -25%, 
         no renewal discussion by 90 days before contract end, missed QBR]
Pre-committed response:
  - CRO: executive escalation call within 48 hours
  - CPO: product health review scheduled
  - CEO: direct outreach if escalation fails
Owner: CRO (health score dashboard, weekly)
```

**Fundraise:**
```
Trigger: <3 term sheets after 8 weeks of active process
Pre-committed response:
  - CEO: expand process to 10 additional firms
  - CFO: model bridge scenarios; draft bridge terms
  - COO: prepare 90-day cost reduction plan
Owner: CEO (weekly fundraise status)
```

---

## How Many Scenarios to Model

**Answer: 3-4 max per planning cycle.**

The math: 3 scenarios × 6 domains × 3 severity levels = 54 combinations. That's already overwhelming. More scenarios don't improve decisions — they paralyze them.

### The Right 3-4 Scenarios
1. **Most likely adverse scenario** — what actually keeps you up at night
2. **Market/macro scenario** — something outside your control
3. **Black swan** — low probability, existential if it hits
4. **Compound scenario** — your top 2 adverse events happening simultaneously

### What Kills Scenario Planning
- **Too many scenarios** — decision paralysis
- **Only modeling what's comfortable** — survivorship bias
- **No pre-committed responses** — it's just worry, not planning
- **Not revisiting** — scenarios from 12 months ago are often irrelevant
- **Treating scenarios as forecasts** — they're possibilities, not predictions
- **Confusing risk with uncertainty** — risk has known probabilities; uncertainty doesn't
