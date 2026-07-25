---
name: "customer-success-manager"
description: Monitors customer health, predicts churn risk, and identifies expansion opportunities using weighted scoring models for SaaS customer success. Use when analyzing customer accounts, reviewing retention metrics, scoring at-risk customers, or when the user mentions churn, customer health scores, upsell opportunities, expansion revenue, retention analysis, or customer analytics. Runs three Python CLI tools to produce deterministic health scores, churn risk tiers, and prioritized expansion recommendations across Enterprise, Mid-Market, and SMB segments.
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: business-growth
  domain: customer-success
  updated: 2026-02-06
  python-tools: health_score_calculator.py, churn_risk_analyzer.py, expansion_opportunity_scorer.py
  tech-stack: customer-success, saas-metrics, health-scoring
---

# Customer Success Manager

Production-grade customer success analytics with multi-dimensional health scoring, churn risk prediction, and expansion opportunity identification. Three Python CLI tools provide deterministic, repeatable analysis using standard library only -- no external dependencies, no API calls, no ML models.

---

## Table of Contents

- [Input Requirements](#input-requirements)
- [Output Formats](#output-formats)
- [How to Use](#how-to-use)
- [Scripts](#scripts)
- [Reference Guides](#reference-guides)
- [Templates](#templates)
- [Best Practices](#best-practices)
- [Limitations](#limitations)

---

## Input Requirements

All scripts accept a JSON file as positional input argument. See `assets/sample_customer_data.json` for complete schema examples and sample data.

### Health Score Calculator

Required fields per customer object: `customer_id`, `name`, `segment`, `arr`, and nested objects `usage` (login_frequency, feature_adoption, dau_mau_ratio), `engagement` (support_ticket_volume, meeting_attendance, nps_score, csat_score), `support` (open_tickets, escalation_rate, avg_resolution_hours), `relationship` (executive_sponsor_engagement, multi_threading_depth, renewal_sentiment), and `previous_period` scores for trend analysis.

### Churn Risk Analyzer

Required fields per customer object: `customer_id`, `name`, `segment`, `arr`, `contract_end_date`, and nested objects `usage_decline`, `engagement_drop`, `support_issues`, `relationship_signals`, and `commercial_factors`.

### Expansion Opportunity Scorer

Required fields per customer object: `customer_id`, `name`, `segment`, `arr`, and nested objects `contract` (licensed_seats, active_seats, plan_tier, available_tiers), `product_usage` (per-module adoption flags and usage percentages), and `departments` (current and potential).

---

## Output Formats

All scripts support two output formats via the `--format` flag:

- **`text`** (default): Human-readable formatted output for terminal viewing
- **`json`**: Machine-readable JSON output for integrations and pipelines

---

## How to Use

### Quick Start

```bash
# Health scoring
python scripts/health_score_calculator.py assets/sample_customer_data.json
python scripts/health_score_calculator.py assets/sample_customer_data.json --format json

# Churn risk analysis
python scripts/churn_risk_analyzer.py assets/sample_customer_data.json
python scripts/churn_risk_analyzer.py assets/sample_customer_data.json --format json

# Expansion opportunity scoring
python scripts/expansion_opportunity_scorer.py assets/sample_customer_data.json
python scripts/expansion_opportunity_scorer.py assets/sample_customer_data.json --format json
```

### Workflow Integration

```bash
# 1. Score customer health across portfolio
python scripts/health_score_calculator.py customer_portfolio.json --format json > health_results.json
# Verify: confirm health_results.json contains the expected number of customer records before continuing

# 2. Identify at-risk accounts
python scripts/churn_risk_analyzer.py customer_portfolio.json --format json > risk_results.json
# Verify: confirm risk_results.json is non-empty and risk tiers are present for each customer

# 3. Find expansion opportunities in healthy accounts
python scripts/expansion_opportunity_scorer.py customer_portfolio.json --format json > expansion_results.json
# Verify: confirm expansion_results.json lists opportunities ranked by priority

# 4. Prepare QBR using templates
# Reference: assets/qbr_template.md
```

**Error handling:** If a script exits with an error, check that:
- The input JSON matches the required schema for that script (see Input Requirements above)
- All required fields are present and correctly typed
- Python 3.7+ is being used (`python --version`)
- Output files from prior steps are non-empty before piping into subsequent steps

---

## Scripts

### 1. health_score_calculator.py

**Purpose:** Multi-dimensional customer health scoring with trend analysis and segment-aware benchmarking.

**Dimensions and Weights:**
| Dimension | Weight | Metrics |
|-----------|--------|---------|
| Usage | 30% | Login frequency, feature adoption, DAU/MAU ratio |
| Engagement | 25% | Support ticket volume, meeting attendance, NPS/CSAT |
| Support | 20% | Open tickets, escalation rate, avg resolution time |
| Relationship | 25% | Executive sponsor engagement, multi-threading depth, renewal sentiment |

**Classification:**
- Green (75-100): Healthy -- customer achieving value
- Yellow (50-74): Needs attention -- monitor closely
- Red (0-49): At risk -- immediate intervention required

**Usage:**
```bash
python scripts/health_score_calculator.py customer_data.json
python scripts/health_score_calculator.py customer_data.json --format json
```

### 2. churn_risk_analyzer.py

**Purpose:** Identify at-risk accounts with behavioral signal detection and tier-based intervention recommendations.

**Risk Signal Weights:**
| Signal Category | Weight | Indicators |
|----------------|--------|------------|
| Usage Decline | 30% | Login trend, feature adoption change, DAU/MAU change |
| Engagement Drop | 25% | Meeting cancellations, response time, NPS change |
| Support Issues | 20% | Open escalations, unresolved critical, satisfaction trend |
| Relationship Signals | 15% | Champion left, sponsor change, competitor mentions |
| Commercial Factors | 10% | Contract type, pricing complaints, budget cuts |

**Risk Tiers:**
- Critical (80-100): Immediate executive escalation
- High (60-79): Urgent CSM intervention
- Medium (40-59): Proactive outreach
- Low (0-39): Standard monitoring

**Usage:**
```bash
python scripts/churn_risk_analyzer.py customer_data.json
python scripts/churn_risk_analyzer.py customer_data.json --format json
```

### 3. expansion_opportunity_scorer.py

**Purpose:** Identify upsell, cross-sell, and expansion opportunities with revenue estimation and priority ranking.

**Expansion Types:**
- **Upsell**: Upgrade to higher tier or more of existing product
- **Cross-sell**: Add new product modules
- **Expansion**: Additional seats or departments

**Usage:**
```bash
python scripts/expansion_opportunity_scorer.py customer_data.json
python scripts/expansion_opportunity_scorer.py customer_data.json --format json
```

---

## Reference Guides

| Reference | Description |
|-----------|-------------|
| `references/health-scoring-framework.md` | Complete health scoring methodology, dimension definitions, weighting rationale, threshold calibration |
| `references/cs-playbooks.md` | Intervention playbooks for each risk tier, onboarding, renewal, expansion, and escalation procedures |
| `references/cs-metrics-benchmarks.md` | Industry benchmarks for NRR, GRR, churn rates, health scores, expansion rates by segment and industry |

---

## Templates

| Template | Purpose |
|----------|---------|
| `assets/qbr_template.md` | Quarterly Business Review presentation structure |
| `assets/success_plan_template.md` | Customer success plan with goals, milestones, and metrics |
| `assets/onboarding_checklist_template.md` | 90-day onboarding checklist with phase gates |
| `assets/executive_business_review_template.md` | Executive stakeholder review for strategic accounts |

---

## Best Practices

1. **Combine signals**: Use all three scripts together for a complete customer picture
2. **Act on trends, not snapshots**: A declining Green is more urgent than a stable Yellow
3. **Calibrate thresholds**: Adjust segment benchmarks based on your product and industry per `references/health-scoring-framework.md`
4. **Prepare with data**: Run scripts before every QBR and executive meeting; reference `references/cs-playbooks.md` for intervention guidance

---

## Limitations

- **No real-time data**: Scripts analyze point-in-time snapshots from JSON input files
- **No CRM integration**: Data must be exported manually from your CRM/CS platform
- **Deterministic only**: No predictive ML -- scoring is algorithmic based on weighted signals
- **Threshold tuning**: Default thresholds are industry-standard but may need calibration for your business
- **Revenue estimates**: Expansion revenue estimates are approximations based on usage patterns

---

**Last Updated:** February 2026
**Tools:** 3 Python CLI tools
**Dependencies:** Python 3.7+ standard library only
