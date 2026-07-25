# OKR Cascade Framework

A practical guide to Objectives and Key Results (OKRs) and how to cascade them across organizational levels.

---

## Table of Contents

- [What Are OKRs](#what-are-okrs)
- [The Cascade Model](#the-cascade-model)
- [Writing Effective Objectives](#writing-effective-objectives)
- [Defining Key Results](#defining-key-results)
- [Alignment Scoring](#alignment-scoring)
- [Common Pitfalls](#common-pitfalls)
- [OKR Cadence](#okr-cadence)

---

## What Are OKRs

**Objectives and Key Results (OKRs)** are a goal-setting framework that connects organizational strategy to measurable outcomes.

### Components

| Component | Definition | Characteristics |
|-----------|------------|-----------------|
| **Objective** | What you want to achieve | Qualitative, inspirational, time-bound |
| **Key Result** | How you measure progress | Quantitative, specific, measurable |

### OKR Formula

```
Objective: [Inspirational goal statement]
├── KR1: [Metric] from [current] to [target] by [date]
├── KR2: [Metric] from [current] to [target] by [date]
└── KR3: [Metric] from [current] to [target] by [date]
```

### Example

```
Objective: Become the go-to solution for enterprise customers

KR1: Increase enterprise ARR from $5M to $8M
KR2: Improve enterprise NPS from 35 to 50
KR3: Reduce enterprise onboarding time from 30 days to 14 days
```

---

## The Cascade Model

OKRs cascade from company strategy down to individual teams, ensuring alignment at every level.

### Cascade Structure

```
┌─────────────────────────────────────────┐
│           COMPANY LEVEL                 │
│  Strategic objectives set by leadership │
│  Owned by: CEO, Executive Team          │
└───────────────┬─────────────────────────┘
                │
                ▼
┌─────────────────────────────────────────┐
│          PRODUCT LEVEL                  │
│  How product org contributes to company │
│  Owned by: Head of Product, CPO         │
└───────────────┬─────────────────────────┘
                │
                ▼
┌─────────────────────────────────────────┐
│            TEAM LEVEL                   │
│  Specific initiatives and deliverables  │
│  Owned by: Product Managers, Tech Leads │
└─────────────────────────────────────────┘
```

### Contribution Model

Each level contributes a percentage to the level above:

| Level | Typical Contribution | Range |
|-------|---------------------|-------|
| Product → Company | 30% | 20-50% |
| Team → Product | 25% per team | 15-35% |

**Note:** Contribution percentages should be calibrated based on:
- Number of teams
- Relative team size
- Strategic importance of initiatives

### Alignment Types

| Alignment | Description | Goal |
|-----------|-------------|------|
| **Vertical** | Each level supports the level above | >90% of objectives linked |
| **Horizontal** | Teams coordinate on shared objectives | No conflicting goals |
| **Temporal** | Quarterly OKRs support annual goals | Clear progression |

---

## Writing Effective Objectives

### The 3 Cs of Objectives

| Criterion | Description | Example |
|-----------|-------------|---------|
| **Clear** | Unambiguous intent | "Improve customer onboarding" not "Make things better" |
| **Compelling** | Inspires action | "Delight enterprise customers" not "Serve enterprise" |
| **Challenging** | Stretches capabilities | Achievable but requires effort |

### Objective Templates by Strategy

**Growth Strategy:**
```
- Accelerate user acquisition in [segment]
- Expand market presence in [region/vertical]
- Build sustainable acquisition channels
```

**Retention Strategy:**
```
- Create lasting value for [user segment]
- Improve product experience for [use case]
- Maximize customer lifetime value
```

**Revenue Strategy:**
```
- Drive revenue growth through [mechanism]
- Optimize monetization for [segment]
- Expand revenue per customer
```

**Innovation Strategy:**
```
- Pioneer [capability] in the market
- Establish leadership through [innovation area]
- Build competitive differentiation
```

**Operational Strategy:**
```
- Improve delivery efficiency by [mechanism]
- Scale operations to support [target]
- Reduce operational friction in [area]
```

### Objective Anti-Patterns

| Anti-Pattern | Problem | Better Alternative |
|--------------|---------|-------------------|
| "Increase revenue" | Too vague | "Grow enterprise ARR to $10M" |
| "Be the best" | Not measurable | "Achieve #1 NPS in category" |
| "Fix bugs" | Too tactical | "Improve platform reliability" |
| "Launch feature X" | Output, not outcome | "Improve [metric] through [capability]" |

---

## Defining Key Results

### Key Result Anatomy

```
[Verb] [metric] from [current baseline] to [target] by [deadline]
```

### Key Result Types

| Type | Characteristics | When to Use |
|------|-----------------|-------------|
| **Metric-based** | Track a number | Most common, highly measurable |
| **Milestone-based** | Track completion | For binary deliverables |
| **Health-based** | Track stability | For maintenance objectives |

### Metric Categories

| Category | Examples |
|----------|----------|
| **Acquisition** | Signups, trials started, leads generated |
| **Activation** | Onboarding completion, first value moment |
| **Retention** | D7/D30 retention, churn rate, repeat usage |
| **Revenue** | ARR, ARPU, conversion rate, LTV |
| **Engagement** | DAU/MAU, session duration, actions per session |
| **Satisfaction** | NPS, CSAT, support tickets |
| **Efficiency** | Cycle time, automation rate, cost per unit |

### Key Result Scoring

| Score | Status | Description |
|-------|--------|-------------|
| 0.0-0.3 | Red | Significant gap, needs intervention |
| 0.4-0.6 | Yellow | Partial progress, on watch |
| 0.7-0.9 | Green | Strong progress, on track |
| 1.0 | Complete | Target achieved |

**Note:** Hitting 0.7 is considered success for stretch goals. Consistently hitting 1.0 suggests targets aren't ambitious enough.

---

## Alignment Scoring

The OKR cascade generator calculates alignment scores across four dimensions:

### Scoring Dimensions

| Dimension | Weight | What It Measures |
|-----------|--------|------------------|
| **Vertical Alignment** | 40% | % of objectives with parent links |
| **Horizontal Alignment** | 20% | Cross-team coordination on shared goals |
| **Coverage** | 20% | % of company KRs addressed by product |
| **Balance** | 20% | Even distribution of work across teams |

### Alignment Score Interpretation

| Score | Grade | Interpretation |
|-------|-------|----------------|
| 90-100% | A | Excellent alignment, well-cascaded |
| 80-89% | B | Good alignment, minor gaps |
| 70-79% | C | Adequate, needs attention |
| 60-69% | D | Poor alignment, significant gaps |
| <60% | F | Misaligned, requires restructuring |

### Target Benchmarks

| Metric | Target | Red Flag |
|--------|--------|----------|
| Vertical alignment | >90% | <70% |
| Horizontal alignment | >75% | <50% |
| Coverage | >80% | <60% |
| Balance | >80% | <60% |
| Overall | >80% | <65% |

---

## Common Pitfalls

### OKR Anti-Patterns

| Pitfall | Symptom | Fix |
|---------|---------|-----|
| **Too many OKRs** | 10+ objectives per level | Limit to 3-5 objectives |
| **Sandbagging** | Always hit 100% | Set stretch targets (0.7 = success) |
| **Task lists** | KRs are tasks, not outcomes | Focus on measurable impact |
| **Set and forget** | No mid-quarter reviews | Check-ins every 2 weeks |
| **Cascade disconnect** | Team OKRs don't link up | Validate parent relationships |
| **Metric gaming** | Optimizing for KR, not intent | Balance with health metrics |

### Warning Signs

- All teams have identical objectives (lack of specialization)
- No team owns a critical company objective (gap in coverage)
- One team owns everything (unrealistic load)
- Objectives change weekly (lack of commitment)
- KRs are activities, not outcomes (wrong focus)

---

## OKR Cadence

### Quarterly Rhythm

| Week | Activity |
|------|----------|
| **Week -2** | Leadership sets company OKRs draft |
| **Week -1** | Product and team OKR drafting |
| **Week 0** | OKR finalization and alignment review |
| **Week 2** | First check-in, adjust if needed |
| **Week 6** | Mid-quarter review |
| **Week 10** | Pre-quarter reflection |
| **Week 12** | Quarter close, scoring, learnings |

### Check-in Format

```
Weekly/Bi-weekly Status Update:

1. Confidence level: [Red/Yellow/Green]
2. Progress since last check-in: [specific updates]
3. Blockers: [what's in the way]
4. Asks: [what help is needed]
5. Forecast: [expected end-of-quarter score]
```

### Annual Alignment

Quarterly OKRs should ladder up to annual goals:

```
Annual Goal: Become a $100M ARR business

Q1: Build enterprise sales motion (ARR: $25M → $32M)
Q2: Expand into APAC region (ARR: $32M → $45M)
Q3: Launch self-serve enterprise tier (ARR: $45M → $65M)
Q4: Scale and optimize (ARR: $65M → $100M)
```

---

## Quick Reference

### OKR Checklist

**Before finalizing OKRs:**
- [ ] 3-5 objectives per level (not more)
- [ ] 3-5 key results per objective
- [ ] Each KR has a current baseline and target
- [ ] Vertical alignment validated (parent links)
- [ ] No conflicting objectives across teams
- [ ] Owners assigned to every objective
- [ ] Check-in cadence defined

**During the quarter:**
- [ ] Bi-weekly progress updates
- [ ] Mid-quarter formal review
- [ ] Adjust forecasts based on learnings
- [ ] Escalate blockers early

**End of quarter:**
- [ ] Score all key results (0.0-1.0)
- [ ] Document learnings
- [ ] Celebrate wins
- [ ] Carry forward or close incomplete items

---

*See also: `strategy_types.md` for strategy-specific OKR templates*
