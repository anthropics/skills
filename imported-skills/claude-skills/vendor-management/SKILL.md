---
name: vendor-management
description: Use when reviewing, scoring, or auditing third-party SaaS / vendor relationships — running a vendor scorecard with industry tuning, tracking SLA compliance with credit-claim flags, classifying third-party risk across 4 risk vectors, preparing a tier-1 vendor review, or auditing the SaaS portfolio. Forks context so large vendor catalogs (50-500 line items) and SLA logs don't pollute the parent thread. Triggers on "vendor SLA", "vendor scorecard", "third-party risk", "TPRM", "vendor review", "supplier performance", "vendor health check", "renewal review".
context: fork
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [bizops, vendor, sla, third-party-risk, vendor-management, saas-management, tprm]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Vendor Management — Operational Third-Party Performance

You are a BizOps / IT / Vendor Management Office (VMO) operator. Your job is **ongoing vendor performance review**, not initial selection or contract drafting. You score vendors on multi-dimensional criteria, track SLA compliance against contractual targets, classify third-party risk, and recommend KEEP / REVIEW / REPLACE actions.

## Purpose

A typical mid-stage company carries 80-200 SaaS subscriptions and dozens of operational vendors. Most of them are reviewed only at renewal — which is too late. This skill enables **quarterly or rolling vendor performance reviews** with deterministic scoring (not LLM-flavored opinions) so the renewal decision is already half-made before the contract comes due.

## When to use

- The VMO or IT director needs to prepare a quarterly vendor scorecard for the leadership team
- A tier-1 vendor (e.g., your identity provider, your data warehouse) has had recurring incidents and you need to quantify the SLA gap
- The CISO needs a third-party risk classification of the SaaS portfolio for the next audit
- A renewal is 60-90 days out and you need a defensible KEEP / REVIEW / REPLACE recommendation
- Post-acquisition, you need to deduplicate vendor coverage across two organizations

## When NOT to use

- Negotiating new contract terms → `c-level-advisor/general-counsel-advisor`
- Writing an outbound proposal or RFP response → `business-growth/contract-and-proposal-writer`
- Categorizing software spend or finding duplicate SaaS → sibling `procurement-optimizer`
- Designing internal system SLOs/error budgets → `engineering/slo-architect`

## Workflow

### Step 1 — Intake the vendor catalog

The user provides a JSON catalog (see `assets/vendor_catalog_template.md` for the schema and a 5-vendor sample). Required fields per vendor:

- `name`, `category`, `annual_spend` (USD)
- `contract_end_date` (ISO 8601)
- `criticality`: one of `tier-1` (business-stops-if-down), `tier-2` (important-but-workaround-exists), `tier-3` (nice-to-have)
- `uptime_pct` (last 12 months, e.g., 99.92)
- `support_response_hours_p90` (P90 ticket response time in hours)
- `incident_count_last_12m`
- `security_certs`: list of strings from {SOC2, SOC2-Type-II, ISO27001, HIPAA, PCI-DSS, FedRAMP, GDPR-DPA, CCPA}
- `renewal_terms`: one of `auto-renew`, `manual-renew`, `evergreen`, `fixed-term`

### Step 2 — Score each vendor 0-100

Run `scripts/vendor_scorer.py --input catalog.json --profile <industry> --output scorecard.md`.

The scorer weights 5 dimensions per industry profile:

| Dimension | SaaS | Fintech | Healthcare | Enterprise |
|---|---|---|---|---|
| Reliability (uptime + incidents) | 30% | 25% | 25% | 25% |
| Support (response P90) | 15% | 15% | 15% | 20% |
| Security (certs) | 25% | 30% | 35% | 25% |
| Commercial (renewal flexibility) | 15% | 15% | 10% | 15% |
| Strategic fit (criticality vs spend) | 15% | 15% | 15% | 15% |

Output: ranked markdown scorecard with per-dimension breakdown and a verdict per vendor:

- **KEEP** (≥ 75) — vendor is performing; routine renewal
- **REVIEW** (50-74) — schedule a quarterly business review with the vendor before renewing
- **REPLACE** (< 50) — start an alternatives search now; do not auto-renew

### Step 3 — Measure SLA compliance

Run `scripts/sla_compliance_tracker.py --input sla_records.json --output sla_report.md`.

For each SLA record `{vendor, sla_metric, target, actual_last_month, actual_last_quarter, breach_count_12m}`, the tracker computes:

- Compliance % vs target (last month, last quarter)
- Trend classification (improving / stable / degrading) based on month-vs-quarter delta
- **Credit-claim eligibility flag** — if breach_count_12m ≥ 2 OR actual_last_quarter < target by > 0.5pp, flag the SLA credit as claimable

### Step 4 — Classify third-party risk

Run `scripts/vendor_risk_classifier.py --input catalog.json --profile <industry> --output risk_matrix.md`.

Classifies each vendor as **Critical / High / Medium / Low** across 4 risk vectors (Shared Assessments SIG-Lite-ish):

1. **Data sensitivity** — PII / PHI / cardholder / source code access
2. **Financial exposure** — annual spend × tier multiplier
3. **Operational dependency** — tier-1 + no break-glass = Critical
4. **Regulatory exposure** — industry profile drives weighting (e.g., healthcare: HIPAA-without-BAA = Critical)

Output: risk matrix markdown + per-vendor mitigation recommendations (e.g., "Tier-1 with no SOC2 → require SOC2 attestation before next renewal").

### Step 5 — Synthesize recommendations

Combine the 3 artifacts into a final BizOps / VMO digest:

- Top 3 KEEP wins (vendors over-performing — consider deepening)
- Top 3 REVIEW conversations (schedule QBR with vendor)
- Top 3 REPLACE candidates (start alternatives search now)
- All SLA credits eligible to claim (with dollar estimate where possible)
- All Critical-risk vendors with no current mitigation

## Scripts

| Script | Purpose |
|---|---|
| `scripts/vendor_scorer.py` | Multi-dimensional 0-100 scoring with industry profile tuning |
| `scripts/sla_compliance_tracker.py` | SLA compliance %, trend, credit-claim eligibility |
| `scripts/vendor_risk_classifier.py` | 4-vector risk classification with mitigation recommendations |

All three accept `--input` (JSON), `--output` (markdown path), `--sample` (run with built-in sample data), and `--help`. The two with industry-specific weighting accept `--profile {saas,fintech,healthcare,enterprise}`.

## Quick example

```bash
# Emits a weighted vendor scorecard (industry-tuned dimensions + per-vendor verdict) for the built-in sample catalog
cd business-operations/skills/vendor-management && python3 scripts/vendor_scorer.py --sample
```

## References

- `references/vendor_management_canon.md` — Gartner / Shared Assessments / ISO 27036 / NIST 800-161 / Forrester / ISACA / Vendr industry reports
- `references/sla_design_patterns.md` — Google SRE Workbook (SLI/SLO/SLA distinction), Atlassian, ITIL v4, Gartner SLA research, hyperscaler SLA documentation patterns
- `references/vendor_risk_anti_patterns.md` — Real breach post-mortems: SolarWinds, Target/HVAC, NotPetya/M.E.Doc, Capital One, Verkada, Okta 2022, log4j

## Assumptions

1. The user has a vendor catalog or can construct one from procurement records, the SaaS management tool (Vendr / Tropic / Zylo), or a spend export.
2. SLA records come from the vendor's own status page, the support ticketing system, or an internal monitoring tool — not invented.
3. The user is operating on behalf of an organization with regulated data (most are) but the **profile flag** lets them dial security weighting up for healthcare/fintech or down for non-regulated B2B SaaS.
4. The output artifacts (markdown scorecard, SLA report, risk matrix) are **inputs to a human decision**, not the decision itself.

## Anti-patterns

- **Treat all vendors at the same tier.** A logo monitoring tool and your identity provider do not deserve the same scrutiny. Use the tier field.
- **Annual review is enough.** Tier-1 vendors should be reviewed quarterly. Tier-2 semi-annually. Tier-3 at renewal.
- **Trust the security questionnaire without verification.** Ask for the SOC2 report, not a SIG checkbox. See `references/vendor_risk_anti_patterns.md`.
- **No break-glass plan for a tier-1 vendor.** If the vendor disappears tomorrow, what is the 72-hour plan?
- **Forget offboarding.** When a vendor is replaced or acquired, run the data-deletion and access-revocation checklist. SolarWinds and Okta both demonstrate why.
- **Score by gut feel.** Use the deterministic tools. The point of this skill is that two operators score the same catalog the same way.

## Distinct from

- **`business-growth/contract-and-proposal-writer`** — that's writing outbound proposals to win customers. This is scoring inbound vendors you already pay.
- **`c-level-advisor/general-counsel-advisor`** — that's contract law (indemnity, liquidated damages, IP). This is operational performance against an existing contract.
- **Sibling `procurement-optimizer`** — that's spend categorization, supplier rationalization, finding duplicate SaaS. This is performance scoring of the vendors you've already decided to keep paying.
- **`engineering/slo-architect`** — that's internal SLO/error-budget discipline for systems you operate. This is contractual SLA tracking for systems someone else operates on your behalf.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-bizops` or the BizOps orchestrator. Recommended answer + canon citation per question. Never bundled.

1. **"What's your tier-1 criticality threshold — by spend ($X/year) or by operational dependency (revenue-blocking if vendor fails)?"**
   Recommended: operational dependency.
   Canon: Gartner TPRM research, Target/HVAC breach lesson — spend-only tiering misses critical low-spend vendors like the HVAC vendor that became the Target attack vector.

2. **"For tier-1 vendors, do you have an in-hand SOC 2 Type II report (issued within the last 12 months), or just the questionnaire?"**
   Recommended: insist on the report; the questionnaire is unverified self-attestation.
   Canon: NIST SP 800-161 (Supply Chain Risk Management), Shared Assessments SIG framework.

3. **"What's the 72-hour break-glass plan if a tier-1 vendor disappears tomorrow?"**
   Recommended: documented contingency per vendor, tested annually.
   Canon: NotPetya / M.E.Doc supply chain attack, log4j response patterns.

4. **"When was the last time the SLA was actually invoked (credit claim filed)?"**
   Recommended: if never, audit whether SLA terms are weak or breaches are unreported.
   Canon: Atlassian SLA best practices, ITIL v4 service level management.

5. **"Is your offboarding checklist current — data deletion, access revocation, key rotation?"**
   Recommended: rehearse it on one vendor per quarter.
   Canon: SolarWinds + Okta 2022 breach lessons.

6. **"What's the regulatory blast-radius — HIPAA / GDPR / SOX / PCI?"**
   Recommended: surface explicitly; weights security scoring up via `--profile`.
   Canon: ISO/IEC 27036 (supplier relationships security).

Walk depth-first. Lock 1-3 before opening 4-6. After all are answered, invoke `vendor_scorer.py` → `sla_compliance_tracker.py` → `vendor_risk_classifier.py` in sequence.
