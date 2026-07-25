# Attribution Guide

Multi-touch attribution setup, analysis, and reporting.

---

## Table of Contents

- [Attribution Models](#attribution-models)
- [HubSpot Attribution Setup](#hubspot-attribution-setup)
- [Google Analytics Configuration](#google-analytics-configuration)
- [Reporting Dashboards](#reporting-dashboards)
- [A/B Testing Framework](#ab-testing-framework)

---

## Attribution Models

### Model Comparison

| Model | Credit Distribution | Best For |
|-------|---------------------|----------|
| First-Touch | 100% to first interaction | Awareness campaigns |
| Last-Touch | 100% to last interaction | Direct response, BOFU |
| Linear | Equal across all touchpoints | Simple full-funnel view |
| Time Decay | More credit to recent touches | Long sales cycles |
| W-Shaped | 40% first, 20% middle, 40% last | Hybrid PLG/Sales-Led |

### Recommended Model: W-Shaped

For Series A hybrid motion:
- 40% credit to first touch (awareness)
- 20% distributed across middle touches
- 40% credit to last touch (conversion)

**Rationale:** Balances discovery and closing influence.

---

## HubSpot Attribution Setup

### Enable Attribution Reports

1. Navigate to Marketing → Reports → Attribution
2. Select attribution model (W-Shaped recommended)
3. Define conversion event (deal created, SQL stage)
4. Set lookback window (90 days typical)

### Attribution Report Types

| Report | Purpose | Frequency |
|--------|---------|-----------|
| Revenue Attribution | Credit revenue to channels | Monthly |
| Content Attribution | Credit to content assets | Weekly |
| Campaign Attribution | Credit to campaigns | Per campaign |

### Custom Attribution Report

Create: Marketing → Reports → Create Report

**Metrics:**
- Marketing-sourced pipeline $
- Marketing-influenced revenue
- CAC by channel
- ROAS by campaign

**Dimensions:**
- Channel (Organic, Paid, Email, Social, Referral)
- Campaign
- Region (US, EU, Canada)
- Funnel stage (TOFU, MOFU, BOFU)

**Validation:** Run report for past 90 days. Verify all channels appear with data.

---

## Google Analytics Configuration

### GA4 Events to Track

**Engagement Events:**
```
page_view        (auto-tracked)
scroll           (75% depth)
video_play       (product demos)
file_download    (whitepapers, eBooks)
```

**Conversion Events:**
```
sign_up          (free trial, account)
demo_request     (calendar booking)
contact_form     (inbound interest)
pricing_view     (pricing page visit)
```

### Custom Dimensions

| Dimension | Source | Purpose |
|-----------|--------|---------|
| User Type | CRM sync | Free vs Paid |
| Plan Type | CRM sync | Starter, Pro, Enterprise |
| Lead Status | HubSpot | MQL, SQL, Customer |
| Campaign ID | UTM | HubSpot campaign |

### GA4 + HubSpot Integration

1. Install HubSpot tracking code (includes GA4)
2. Or use Google Tag Manager for advanced tracking
3. Sync GA4 audiences → HubSpot lists for retargeting
4. Import GA4 conversions to Google Ads

**Validation:** Real-time report shows events firing. Conversion events marked correctly.

---

## Reporting Dashboards

### Weekly Performance Dashboard

| Metric | Purpose | Target |
|--------|---------|--------|
| Visits | Traffic volume | +10% WoW |
| Unique visitors | Reach | +5% WoW |
| Bounce rate | Engagement | <50% |
| MQLs | Lead volume | Weekly target |
| SQLs | Pipeline | Weekly target |
| Conversion rate | Efficiency | >2% |

### Monthly Executive Dashboard

| KPI | Formula | Target |
|-----|---------|--------|
| Marketing-Sourced Pipeline | Sum of new pipeline $ | $X/month |
| Marketing-Sourced Revenue | Closed-won from marketing | $Y/month |
| Blended CAC | Total spend / customers | <$Z |
| MQL→SQL Rate | SQLs / MQLs | >15% |
| Pipeline Velocity | Avg days in pipeline | <60 days |
| ROMI | Revenue / Marketing spend | >3:1 |

### Dashboard Build Process

1. Define KPIs with leadership
2. Create data sources in HubSpot
3. Build visualizations (charts, tables)
4. Set up automated refresh
5. Schedule weekly/monthly distribution

**Validation:** Dashboard shows last 7 days data. All metrics calculating correctly.

---

## A/B Testing Framework

### ICE Prioritization

**Formula:** ICE = (Impact × Confidence × Ease) ÷ 3

| Factor | Rating | Description |
|--------|--------|-------------|
| Impact | 1-10 | Effect on primary metric |
| Confidence | 1-10 | Certainty of success |
| Ease | 1-10 | Implementation difficulty |

### Test Template

```
Hypothesis: [Adding a case study carousel to pricing will
            increase demo requests by 20%]

Metric: [Demo requests from /pricing page]
Sample Size: [1000 visitors per variant]
Duration: [2 weeks or until significance]
Success Criteria: [20% lift, 95% confidence]

Variant A (Control): [Current pricing page]
Variant B (Treatment): [Pricing page + case study carousel]

Tools: [HubSpot A/B test or Google Optimize]
```

### Statistical Requirements

- Minimum confidence: 95%
- Minimum sample: 1000 visitors per variant
- Minimum duration: 2 weeks
- Do not stop tests early (false positives)

### Common Test Categories

**Landing Page:**
- Headline variations
- CTA copy and color
- Form length
- Social proof placement
- Hero image type

**Ad Creative:**
- Format (static vs video)
- Messaging angle
- Audience targeting
- Landing page destination

**Email:**
- Subject line length
- Personalization depth
- Send time
- CTA placement

### Test Velocity Target

Series A: 4-6 tests per month
- Realistic win rate: 30-40%
- Document all results (wins and losses)
- Build testing knowledge base

**Validation:** Test reaches statistical significance before declaring winner.
