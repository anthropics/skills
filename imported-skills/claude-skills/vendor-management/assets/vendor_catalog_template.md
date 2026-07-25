# Vendor Catalog Template

The vendor-management skill's three Python tools all read the same JSON shape (with some fields used by only one tool). This template gives you the schema, the 5-vendor sample, and quick-start instructions.

## Quick start

1. Copy the JSON below to `vendor_catalog.json` in your working directory.
2. Replace the sample vendors with your real catalog.
3. Run the three tools:

```bash
python scripts/vendor_scorer.py            --input vendor_catalog.json --profile saas       --output scorecard.md
python scripts/sla_compliance_tracker.py   --input sla_records.json                          --output sla_report.md
python scripts/vendor_risk_classifier.py   --input vendor_catalog.json --profile saas       --output risk_matrix.md
```

(SLA records are a separate file — see the SLA shape below.)

## Vendor catalog JSON schema

Each vendor in the catalog is one object in a top-level JSON array.

| Field | Type | Used by | Notes |
|---|---|---|---|
| `name` | string | all 3 | Display name |
| `category` | string | scorer, classifier | e.g., `identity`, `data-warehouse`, `crm`, `analytics` |
| `annual_spend` | number (USD) | scorer, classifier | Annualized total cost |
| `contract_end_date` | ISO 8601 string | (informational) | Useful for downstream sorting |
| `criticality` | enum | scorer, classifier | `tier-1` / `tier-2` / `tier-3` |
| `uptime_pct` | number (0-100) | scorer | Last 12 months |
| `support_response_hours_p90` | number | scorer | P90 first-response, hours |
| `incident_count_last_12m` | integer | scorer | Material incidents (not every page-fault) |
| `security_certs` | list of strings | scorer, classifier | See cert enum below |
| `renewal_terms` | enum | scorer | `auto-renew` / `manual-renew` / `evergreen` / `fixed-term` |
| `data_access` | list of strings | classifier | See data-access enum below |
| `break_glass_plan` | boolean | classifier | Do you have a documented backup plan? |

### Security cert enum

Use any combination of:

- `SOC2` (Type I)
- `SOC2-Type-II`
- `ISO27001`
- `HIPAA`
- `PCI-DSS`
- `FedRAMP`
- `GDPR-DPA`
- `CCPA`

### Data access enum

Use any combination of:

- `PHI` (Protected Health Information, HIPAA)
- `PII` (Personally Identifiable Information)
- `cardholder` (PCI scope)
- `source-code`
- `financial-records`
- `employee-records`
- `customer-emails`
- `logs-only`
- `no-customer-data`

## 5-vendor sample catalog

Copy this to `vendor_catalog.json`:

```json
[
  {
    "name": "Okta",
    "category": "identity",
    "annual_spend": 180000,
    "contract_end_date": "2026-09-30",
    "criticality": "tier-1",
    "uptime_pct": 99.91,
    "support_response_hours_p90": 4.5,
    "incident_count_last_12m": 3,
    "security_certs": ["SOC2-Type-II", "ISO27001", "FedRAMP", "GDPR-DPA"],
    "renewal_terms": "manual-renew",
    "data_access": ["PII", "employee-records"],
    "break_glass_plan": true
  },
  {
    "name": "Snowflake",
    "category": "data-warehouse",
    "annual_spend": 420000,
    "contract_end_date": "2027-01-15",
    "criticality": "tier-1",
    "uptime_pct": 99.97,
    "support_response_hours_p90": 2.0,
    "incident_count_last_12m": 1,
    "security_certs": ["SOC2-Type-II", "ISO27001", "HIPAA", "GDPR-DPA"],
    "renewal_terms": "fixed-term",
    "data_access": ["PII", "PHI", "financial-records"],
    "break_glass_plan": false
  },
  {
    "name": "LegacyCRM",
    "category": "crm",
    "annual_spend": 95000,
    "contract_end_date": "2026-06-30",
    "criticality": "tier-2",
    "uptime_pct": 98.20,
    "support_response_hours_p90": 38.0,
    "incident_count_last_12m": 11,
    "security_certs": ["SOC2"],
    "renewal_terms": "auto-renew",
    "data_access": ["PII", "customer-emails"],
    "break_glass_plan": false
  },
  {
    "name": "ChartingTool",
    "category": "analytics",
    "annual_spend": 8000,
    "contract_end_date": "2026-08-01",
    "criticality": "tier-3",
    "uptime_pct": 99.50,
    "support_response_hours_p90": 14.0,
    "incident_count_last_12m": 2,
    "security_certs": ["SOC2", "GDPR-DPA"],
    "renewal_terms": "evergreen",
    "data_access": ["logs-only"],
    "break_glass_plan": true
  },
  {
    "name": "BoutiqueQA",
    "category": "qa-services",
    "annual_spend": 220000,
    "contract_end_date": "2026-12-31",
    "criticality": "tier-3",
    "uptime_pct": 99.00,
    "support_response_hours_p90": 22.0,
    "incident_count_last_12m": 6,
    "security_certs": [],
    "renewal_terms": "auto-renew",
    "data_access": ["source-code", "PII"],
    "break_glass_plan": false
  }
]
```

## SLA records JSON schema

The SLA tracker takes a **separate** file (`sla_records.json`) where each record is one SLA per vendor (a vendor can have multiple).

| Field | Type | Notes |
|---|---|---|
| `vendor` | string | Must match the vendor catalog `name` |
| `sla_metric` | string | e.g., `uptime_pct`, `support_p90_response_hours`, `ticket_resolution_hours` |
| `target` | number | Contractual target |
| `actual_last_month` | number | Most recent month |
| `actual_last_quarter` | number | Trailing quarter |
| `breach_count_12m` | integer | Number of breach events in 12 months |

### Sample SLA records

```json
[
  {
    "vendor": "Okta",
    "sla_metric": "uptime_pct",
    "target": 99.99,
    "actual_last_month": 99.95,
    "actual_last_quarter": 99.91,
    "breach_count_12m": 3
  },
  {
    "vendor": "Snowflake",
    "sla_metric": "uptime_pct",
    "target": 99.9,
    "actual_last_month": 99.98,
    "actual_last_quarter": 99.97,
    "breach_count_12m": 1
  },
  {
    "vendor": "LegacyCRM",
    "sla_metric": "support_p90_response_hours",
    "target": 8.0,
    "actual_last_month": 36.0,
    "actual_last_quarter": 38.0,
    "breach_count_12m": 11
  },
  {
    "vendor": "ChartingTool",
    "sla_metric": "uptime_pct",
    "target": 99.5,
    "actual_last_month": 99.6,
    "actual_last_quarter": 99.5,
    "breach_count_12m": 0
  },
  {
    "vendor": "BoutiqueQA",
    "sla_metric": "ticket_resolution_hours",
    "target": 24.0,
    "actual_last_month": 30.0,
    "actual_last_quarter": 28.0,
    "breach_count_12m": 6
  }
]
```

## Tips for populating the catalog

- **Pull from your SaaS-management tool** (Vendr, Tropic, Zylo, BetterCloud) if you have one — it usually covers `name`, `category`, `annual_spend`, `contract_end_date`, `renewal_terms`.
- **Uptime & incidents** come from the vendor's status page archive or your monitoring tool (StatusGator, Datadog).
- **`data_access`** requires asking the vendor what data they actually touch. Don't guess — ask, and put it in writing.
- **`break_glass_plan: true`** should mean you have a **documented** 72-hour backup plan, not "we think we could figure it out."
- For tier-1 vendors, run the catalog quarterly. For tier-2, semi-annually. For tier-3, at renewal.
