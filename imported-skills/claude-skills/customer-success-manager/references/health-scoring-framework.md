# Health Scoring Framework

Complete methodology for multi-dimensional customer health scoring in SaaS customer success.

---

## Overview

Customer health scoring is the foundation of proactive customer success management. A well-calibrated health score enables CSMs to prioritise their portfolio, identify emerging risks before they become churn events, and allocate resources where they will have the greatest impact.

This framework uses a weighted, multi-dimensional approach that scores customers across four key areas: usage, engagement, support, and relationship. Each dimension contributes to an overall health score (0-100) that classifies accounts as Green (healthy), Yellow (needs attention), or Red (at risk).

---

## Scoring Dimensions

### 1. Usage (Weight: 30%)

Usage metrics are the strongest leading indicator of customer health. Customers who are not using the product are not deriving value and are at elevated churn risk.

| Metric | Definition | Scoring Method |
|--------|-----------|----------------|
| Login Frequency | Percentage of expected login days with actual logins | (actual / target) * 100, capped at 100 |
| Feature Adoption | Percentage of available features actively used | (adopted / available) * 100, capped at 100 |
| DAU/MAU Ratio | Daily active users divided by monthly active users | (actual / target) * 100, capped at 100 |

**Sub-weights within Usage:**
- Login Frequency: 35%
- Feature Adoption: 40%
- DAU/MAU Ratio: 25%

**Why 30% weight:** Usage is the most objective, data-driven signal. Declining usage almost always precedes churn. However, some customers may have seasonal usage patterns, which is why it is not weighted even higher.

### 2. Engagement (Weight: 25%)

Engagement measures how actively the customer participates in the relationship beyond just product usage.

| Metric | Definition | Scoring Method |
|--------|-----------|----------------|
| Support Ticket Volume | Number of support tickets in the period | Inverse score: (1 - actual/max) * 100 |
| Meeting Attendance | Percentage of scheduled meetings attended | (actual / target) * 100, capped at 100 |
| NPS Score | Net Promoter Score response (0-10) | (actual / target) * 100, capped at 100 |
| CSAT Score | Customer Satisfaction score (1-5) | (actual / target) * 100, capped at 100 |

**Sub-weights within Engagement:**
- Support Ticket Volume: 20% (inverse -- fewer tickets is better)
- Meeting Attendance: 30%
- NPS Score: 25%
- CSAT Score: 25%

**Why 25% weight:** Engagement signals complement usage data. A customer who attends meetings but does not use the product may be in an evaluation phase. A customer who uses the product but skips meetings may be becoming self-sufficient -- or disengaging.

### 3. Support (Weight: 20%)

Support health measures the quality of the customer's support experience, which directly impacts satisfaction and renewal likelihood.

| Metric | Definition | Scoring Method |
|--------|-----------|----------------|
| Open Tickets | Number of currently unresolved tickets | Inverse score: (1 - actual/max) * 100 |
| Escalation Rate | Percentage of tickets escalated | Inverse score: (1 - actual/max) * 100 |
| Avg Resolution Time | Average hours to resolve tickets | Inverse score: (1 - actual/max) * 100 |

**Sub-weights within Support:**
- Open Tickets: 35%
- Escalation Rate: 35%
- Resolution Time: 30%

**Why 20% weight:** Support issues are lagging indicators -- they tell you there is already a problem. However, unresolved support issues are a strong predictor of churn, especially when combined with declining engagement.

### 4. Relationship (Weight: 25%)

Relationship health measures the strength and depth of the human connection between the customer and your organisation.

| Metric | Definition | Scoring Method |
|--------|-----------|----------------|
| Executive Sponsor Engagement | Engagement level of exec sponsor (0-100) | (actual / target) * 100, capped at 100 |
| Multi-Threading Depth | Number of stakeholder contacts | (actual / target) * 100, capped at 100 |
| Renewal Sentiment | Qualitative sentiment assessment | Mapped to score: positive=100, neutral=60, negative=20, unknown=50 |

**Sub-weights within Relationship:**
- Executive Sponsor Engagement: 35%
- Multi-Threading Depth: 30%
- Renewal Sentiment: 35%

**Why 25% weight:** Relationship strength is the most important defence against competitive displacement. A customer with strong relationships will give you more chances to fix problems. A customer with weak relationships may leave without warning.

---

## Classification Thresholds

### Standard Thresholds

| Classification | Score Range | Meaning | Action |
|---------------|-------------|---------|--------|
| Green | 75-100 | Customer is healthy and achieving value | Standard cadence, focus on expansion |
| Yellow | 50-74 | Customer needs attention | Increase touch frequency, investigate root causes |
| Red | 0-49 | Customer is at risk | Immediate intervention, create save plan |

### Segment-Adjusted Thresholds

Enterprise customers typically have higher expectations and more complex deployments, which means a higher bar for "healthy." SMB customers may have simpler use cases and lower engagement expectations.

| Segment | Green Threshold | Yellow Threshold | Red Threshold |
|---------|----------------|------------------|---------------|
| Enterprise | 75-100 | 50-74 | 0-49 |
| Mid-Market | 70-100 | 45-69 | 0-44 |
| SMB | 65-100 | 40-64 | 0-39 |

### Segment-Specific Benchmarks

Each metric target is calibrated per segment. Enterprise customers are expected to have higher login frequency, attendance, and sponsor engagement. SMB customers have lower targets but still meaningful thresholds.

**Example Calibration:**
- Enterprise login frequency target: 90% (high-touch, deeply embedded)
- Mid-Market login frequency target: 80% (balanced engagement)
- SMB login frequency target: 70% (self-serve oriented)

---

## Trend Analysis

A single health score snapshot is useful. A health score trend is actionable.

### Trend Classification

| Trend | Criteria | Implication |
|-------|----------|-------------|
| Improving | Current > Previous by 5+ points | Positive trajectory, reinforce what is working |
| Stable | Within +/- 5 points | Maintain current approach |
| Declining | Current < Previous by 5+ points | Investigate and intervene |
| No Data | No previous period available | Establish baseline |

### Trend Priority Matrix

| Current Score | Trend | Priority |
|--------------|-------|----------|
| Green | Declining | HIGH -- intervene before it drops further |
| Yellow | Declining | CRITICAL -- trajectory leads to Red |
| Yellow | Improving | MEDIUM -- reinforce positive momentum |
| Red | Improving | HIGH -- support the recovery |
| Red | Stable | CRITICAL -- needs new intervention approach |

---

## Calibration Guidelines

### When to Recalibrate

1. **After major product changes**: New features may change what "good usage" looks like
2. **Seasonal patterns**: Some industries have cyclical usage (retail holiday season, fiscal year end)
3. **Portfolio composition changes**: If you add many SMB customers, the overall averages shift
4. **After churn events**: Review whether the health score predicted the churn

### Calibration Process

1. Export health scores for all customers over the past 12 months
2. Identify all churn events in the same period
3. Calculate the average health score of churned customers 90, 60, and 30 days before churn
4. Adjust thresholds so that churned customers would have been classified as Yellow or Red at least 60 days before churn
5. Validate with a holdout set of recent data

### Common Calibration Pitfalls

- **Threshold creep**: Gradually lowering Green thresholds to make the portfolio look healthier
- **Over-weighting lagging indicators**: Support metrics react after the damage is done
- **Ignoring segment differences**: Using one threshold for all segments
- **Sentiment bias**: Over-relying on subjective renewal sentiment

---

## Implementation Checklist

1. Define data sources for each metric (CRM, product analytics, support system)
2. Establish data refresh frequency (daily for usage, weekly for engagement)
3. Configure segment benchmarks for your customer base
4. Set initial thresholds using industry defaults (provided above)
5. Run a 30-day pilot with manual review of edge cases
6. Calibrate thresholds based on pilot results
7. Automate scoring and alerting
8. Review and recalibrate quarterly

---

**Last Updated:** February 2026
