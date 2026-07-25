# Quality KPI Framework

Quality performance indicators, targets, and monitoring guidelines for QMS effectiveness.

---

## Table of Contents

- [KPI Categories](#kpi-categories)
- [Core Quality KPIs](#core-quality-kpis)
- [Customer Quality KPIs](#customer-quality-kpis)
- [Compliance KPIs](#compliance-kpis)
- [Cost of Quality](#cost-of-quality)
- [Dashboard Templates](#dashboard-templates)

---

## KPI Categories

### KPI Hierarchy

| Level | Audience | Update Frequency | Example |
|-------|----------|------------------|---------|
| Strategic | Board, C-suite | Quarterly | Quality cost ratio |
| Tactical | Department heads | Monthly | CAPA closure rate |
| Operational | Team leads | Weekly/Daily | First pass yield |

### KPI Selection Criteria

| Criterion | Requirement |
|-----------|-------------|
| Measurable | Quantifiable with available data |
| Actionable | Team can influence the metric |
| Relevant | Aligned to quality objectives |
| Timely | Can be measured at useful frequency |
| Owned | Clear accountability assigned |

---

## Core Quality KPIs

### Process Performance

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| First Pass Yield | % units passing without rework | >95% | (Units passed first time / Total units) × 100 |
| Process Capability (Cpk) | Process performance vs. spec | >1.33 | min((USL-μ)/(3σ), (μ-LSL)/(3σ)) |
| Nonconformance Rate | NC events per production volume | <1% | (NC count / Total units) × 100 |
| Right First Time | % activities completed correctly first time | >98% | (Correct completions / Total attempts) × 100 |

### CAPA Effectiveness

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| CAPA Closure Rate | % CAPAs closed on time | >90% | (On-time closures / Due closures) × 100 |
| CAPA Effectiveness Rate | % CAPAs effective at verification | >85% | (Effective CAPAs / Verified CAPAs) × 100 |
| Average CAPA Age | Mean days from open to close | <60 days | Sum(Close date - Open date) / Count |
| Overdue CAPA Rate | % CAPAs past due date | <10% | (Overdue CAPAs / Open CAPAs) × 100 |
| Recurrence Rate | % issues recurring after CAPA | <5% | (Recurred issues / Closed CAPAs) × 100 |

### Audit Performance

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Audit Schedule Compliance | % audits completed per schedule | >95% | (Audits completed / Audits scheduled) × 100 |
| Finding Closure Rate | % findings closed on time | >90% | (On-time closures / Due closures) × 100 |
| Repeat Finding Rate | % findings recurring from prior audits | <10% | (Repeat findings / Total findings) × 100 |
| Major NC Rate | Major NCs per audit | <1 | Total major NCs / Total audits |

### Document Control

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Document Review Compliance | % documents reviewed on schedule | >95% | (On-time reviews / Due reviews) × 100 |
| Change Request Cycle Time | Days from request to implementation | <30 days | Average(Implementation - Request date) |
| Obsolete Document Incidents | Uses of obsolete documents | 0 | Count of incidents |

---

## Customer Quality KPIs

### Complaint Management

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Complaint Rate | Complaints per units sold | <0.1% | (Complaints / Units sold) × 100 |
| Complaint Response Time | Days to acknowledge complaint | <24 hours | Average(Response date - Receipt date) |
| Complaint Investigation Time | Days to complete investigation | <30 days | Average(Close date - Receipt date) |
| Complaint Closure Rate | % complaints closed on time | >90% | (On-time closures / Due closures) × 100 |

### Customer Satisfaction

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Customer Satisfaction Score | Survey-based satisfaction rating | >4.0/5.0 | Average of survey scores |
| Net Promoter Score (NPS) | Customer loyalty indicator | >50 | % Promoters - % Detractors |
| Return Rate | % units returned by customers | <1% | (Units returned / Units sold) × 100 |
| Warranty Claim Rate | Warranty claims per units sold | <0.5% | (Claims / Units under warranty) × 100 |

### Field Quality

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Field Failure Rate | Failures in customer use | <0.1% | (Field failures / Units in field) × 100 |
| Mean Time Between Failures | Average operating time before failure | Varies | Total operating hours / Number of failures |
| Service Call Rate | Service calls per installed base | <5%/year | (Service calls / Installed units) × 100 |

---

## Compliance KPIs

### Regulatory Compliance

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Regulatory Submission Success | % submissions accepted first time | >90% | (Accepted submissions / Total submissions) × 100 |
| Inspection Readiness Score | Self-assessment compliance score | >90% | (Compliant items / Total items) × 100 |
| Reportable Event Timeliness | % events reported within required time | 100% | (On-time reports / Required reports) × 100 |
| Registration Currency | % registrations current | 100% | (Current registrations / Required registrations) × 100 |

### Certification Status

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Certification Maintenance | Active certifications vs. required | 100% | (Active certs / Required certs) × 100 |
| Surveillance Audit Outcomes | Pass rate on surveillance audits | 100% | (Passed audits / Conducted audits) × 100 |
| Certification NC Rate | NCs per certification audit | <3 minor, 0 major | Count per audit |

### Training Compliance

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Training Completion Rate | % required training completed | >95% | (Completed / Required) × 100 |
| Training Currency | % employees with current training | >98% | (Current / Total requiring) × 100 |
| Training Effectiveness | % passing competency assessments | >90% | (Passed / Assessed) × 100 |

---

## Cost of Quality

### Cost Categories

| Category | Definition | Examples |
|----------|------------|----------|
| Prevention | Costs to prevent defects | Training, quality planning, process validation |
| Appraisal | Costs to detect defects | Inspection, testing, audits, calibration |
| Internal Failure | Costs of defects found internally | Rework, scrap, re-inspection, downgrading |
| External Failure | Costs of defects found by customer | Returns, complaints, warranty, recalls |

### Cost of Quality KPIs

| KPI | Definition | Target | Calculation |
|-----|------------|--------|-------------|
| Total Cost of Quality | Sum of all quality costs | <5% of revenue | Prevention + Appraisal + Failure costs |
| Prevention/Appraisal Ratio | Prevention vs. detection investment | >1.0 | Prevention costs / Appraisal costs |
| Failure Cost Ratio | Failure costs as % of CoQ | <30% | (Internal + External failure) / Total CoQ |
| Quality Cost Trend | Change in CoQ over time | Decreasing | (Current CoQ - Prior CoQ) / Prior CoQ |

### Cost Collection Categories

```
COST OF QUALITY WORKSHEET

Period: [Start] to [End]

PREVENTION COSTS:
| Category | Description | Amount |
|----------|-------------|--------|
| Quality planning | QMS development, quality planning | $ |
| Training | Quality training programs | $ |
| Process validation | Validation activities | $ |
| Supplier qualification | Supplier quality programs | $ |
| Preventive maintenance | Equipment maintenance | $ |
| SUBTOTAL PREVENTION | | $ |

APPRAISAL COSTS:
| Category | Description | Amount |
|----------|-------------|--------|
| Incoming inspection | Supplier material inspection | $ |
| In-process inspection | Production quality checks | $ |
| Final inspection | Finished goods testing | $ |
| Audit costs | Internal and external audits | $ |
| Calibration | Equipment calibration | $ |
| SUBTOTAL APPRAISAL | | $ |

INTERNAL FAILURE COSTS:
| Category | Description | Amount |
|----------|-------------|--------|
| Scrap | Scrapped materials and product | $ |
| Rework | Labor and materials to correct | $ |
| Re-inspection | Repeat inspection costs | $ |
| Downgrading | Revenue loss from downgrading | $ |
| Root cause analysis | Investigation costs | $ |
| SUBTOTAL INTERNAL FAILURE | | $ |

EXTERNAL FAILURE COSTS:
| Category | Description | Amount |
|----------|-------------|--------|
| Returns processing | Handling returned product | $ |
| Warranty costs | Warranty claims and repairs | $ |
| Complaint handling | Investigation and resolution | $ |
| Recalls | Recall execution costs | $ |
| Liability | Legal and settlement costs | $ |
| SUBTOTAL EXTERNAL FAILURE | | $ |

TOTAL COST OF QUALITY: $
AS % OF REVENUE: %
```

---

## Dashboard Templates

### Executive Quality Dashboard

```
EXECUTIVE QUALITY DASHBOARD
Period: [Month/Quarter]

KEY METRICS AT A GLANCE:
┌─────────────────┬─────────┬─────────┬─────────┐
│ Metric          │ Target  │ Actual  │ Trend   │
├─────────────────┼─────────┼─────────┼─────────┤
│ Customer Sat    │ >4.0    │ [X.X]   │ [↑/↓/→] │
│ Complaint Rate  │ <0.1%   │ [X.XX%] │ [↑/↓/→] │
│ First Pass Yield│ >95%    │ [XX%]   │ [↑/↓/→] │
│ CAPA Closure    │ >90%    │ [XX%]   │ [↑/↓/→] │
│ Audit Findings  │ <3/audit│ [X.X]   │ [↑/↓/→] │
│ Quality Cost    │ <5%     │ [X.X%]  │ [↑/↓/→] │
└─────────────────┴─────────┴─────────┴─────────┘

ALERTS:
[ ] Critical: [Any critical issues requiring immediate attention]
[ ] Warning: [Issues approaching threshold]
[ ] Info: [Notable improvements or changes]

QUALITY OBJECTIVES PROGRESS:
| Objective | Target | YTD | Status |
|-----------|--------|-----|--------|
| [Obj 1] | [Target] | [Actual] | [On Track/Behind] |
```

### Operational Quality Dashboard

```
OPERATIONAL QUALITY DASHBOARD
Week/Month: [Period]

PRODUCTION QUALITY:
├── First Pass Yield: [XX%] (Target: 95%)
├── Rework Rate: [X.X%] (Target: <2%)
├── Scrap Rate: [X.X%] (Target: <1%)
└── NC Count: [XX] (Prior: [XX])

CAPA STATUS:
├── Open CAPAs: [XX]
│   ├── Critical: [X]
│   ├── Major: [XX]
│   └── Minor: [XX]
├── Overdue: [X] [!ALERT if >0]
├── Avg Age: [XX] days
└── Closed This Period: [XX]

AUDIT STATUS:
├── Audits Completed: [X] of [X] scheduled
├── Open Findings: [XX]
│   ├── Major: [X]
│   └── Minor: [XX]
└── Overdue Actions: [X]

COMPLAINTS:
├── Received: [XX]
├── Open: [XX]
├── Avg Response Time: [X.X] days
└── Top Category: [Category]
```

### KPI Target Setting Guidelines

| Performance Level | Action |
|-------------------|--------|
| >110% of target | Consider raising target |
| 100-110% of target | Maintain current target |
| 90-100% of target | Monitor closely |
| 80-90% of target | Improvement plan required |
| <80% of target | Immediate intervention |

### Review Frequency by KPI Type

| KPI Type | Review Frequency | Trend Period |
|----------|------------------|--------------|
| Safety/Compliance | Daily monitoring | Weekly |
| Production | Daily/Weekly | Monthly |
| Customer | Weekly/Monthly | Quarterly |
| Strategic | Monthly/Quarterly | Annual |
| Cost | Monthly | Quarterly |
