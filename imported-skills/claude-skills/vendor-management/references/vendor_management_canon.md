# Vendor Management — Canon

This reference distills the operating frameworks for ongoing third-party / vendor management. It is **not** a contract-negotiation guide (see `c-level-advisor/general-counsel-advisor`) and **not** a procurement-spend optimization guide (see sibling `procurement-optimizer`).

The canon spans seven authoritative sources spanning analyst research, formal standards, industry frameworks, and operator practice.

## 1. Gartner — Vendor Management & TPRM research

Gartner is the most-cited source for vendor segmentation models. Key concepts to internalize:

- **Strategic / Tactical / Operational vendor tiers** map roughly to tier-1 / tier-2 / tier-3 in this skill.
- **Vendor Performance Management (VPM)** vs Vendor Risk Management (VRM): performance is operational SLA + value tracking; risk is data / financial / regulatory exposure. Both belong in the VMO portfolio.
- Source: Gartner — *Magic Quadrant for IT Vendor Risk Management Solutions* (annual, since 2017). https://www.gartner.com/en/documents — search "IT Vendor Risk Management".

## 2. Shared Assessments — SIG and SIG-Lite

The **Standardized Information Gathering (SIG) Questionnaire** is the de-facto industry standard for vendor risk assessment. SIG-Lite is the abbreviated 200-question version used for low-and-medium-risk vendors; full SIG runs to ~1,800 questions.

- SIG Core domains: information security, privacy, business resilience, fourth-party management, compliance, asset management.
- The risk classifier in this skill uses a SIG-Lite-*ish* simplification — 4 vectors instead of 18 domains. For tier-1 critical vendors, the full SIG is appropriate.
- Source: Shared Assessments Program. https://sharedassessments.org/sig/

## 3. ISO/IEC 27036 — Information security for supplier relationships

A formal ISO standard (parts 1-4) covering the full lifecycle of supplier security relationships:

- **27036-1**: Overview and concepts
- **27036-2**: Common requirements (the workhorse part for vendor management)
- **27036-3**: ICT supply chain security
- **27036-4**: Cloud service customer/provider relationships

Useful when a vendor claims ISO27001 — the matching 27036 control set tells you what supplier-relationship clauses the auditor expected them to operate against.

- Source: ISO/IEC 27036 series. https://www.iso.org/standard/59648.html

## 4. NIST SP 800-161 (Rev. 1) — Cybersecurity Supply Chain Risk Management (C-SCRM)

The U.S. federal standard for supply-chain risk. Even commercial orgs use 800-161 as a checklist:

- 8 foundational practices (e.g., integrate C-SCRM into acquisition, use a risk-based approach, identify and protect critical assets).
- Detailed control overlays mapped to NIST SP 800-53 controls.
- Strong framework for **fourth-party** risk (vendors-of-your-vendors) — often where the actual breach originates (SolarWinds being the canonical example).

- Source: NIST SP 800-161 Rev. 1 (May 2022). https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-161r1.pdf

## 5. Forrester — Third-Party Risk Management Wave

Forrester's TPRM Wave is the second-most-cited analyst source (after Gartner) and tends to be more practitioner-flavored:

- Forrester's framing: **continuous monitoring** beats point-in-time annual assessments. The SLA compliance tracker in this skill is built on this premise.
- Key metric Forrester pushes: **mean time to detect (MTTD)** for third-party incidents — most orgs are > 60 days, which is too long for tier-1 vendors.

- Source: Forrester — *The Forrester Wave: Third-Party Risk Management Platforms* (biennial). https://www.forrester.com/research/

## 6. ISACA — TPRM framework + COBIT 2019 alignment

ISACA (the auditor body behind CISM and COBIT) publishes a pragmatic TPRM framework that aligns to **COBIT 2019** controls:

- COBIT APO10 ("Managed Vendors") is the relevant process domain: vendor selection, contract management, performance, risk, and termination.
- ISACA's TPRM guidance is heavy on **audit evidence** — what artifacts to keep so a SOC2 / ISO27001 auditor can verify your TPRM is operating.

- Source: ISACA — *Third Party Risk Management Audit Program* + COBIT 2019. https://www.isaca.org/resources/cobit and https://www.isaca.org/bookstore

## 7. Vendr & Tropic — Industry SaaS-management reports (annual)

Two leading SaaS-management vendors publish annual reports that quantify the operational reality of SaaS sprawl. They're not academic, but they're the only source that benchmarks actual companies:

- **Vendr SaaS Trends Report** — typical company has 130-200 SaaS subscriptions, average 30% YoY growth in software spend, ~20% redundancy at large orgs. https://www.vendr.com/blog
- **Tropic State of SaaS Spend Report** — auto-renew traps cost the average mid-market company ~7% of total SaaS spend annually. https://www.tropicapp.io/resources
- Both reports emphasize: **the renewal date is too late** to start vendor review. Quarterly rolling review is the operating cadence to aim for.

## How this canon maps to the tools in this skill

| Tool | Primary canon |
|---|---|
| `vendor_scorer.py` | Gartner VPM + Vendr/Tropic operational benchmarks |
| `sla_compliance_tracker.py` | Forrester continuous monitoring + Atlassian/ITIL service level patterns (see `sla_design_patterns.md`) |
| `vendor_risk_classifier.py` | Shared Assessments SIG + ISO 27036 + NIST SP 800-161 |

When in doubt: SIG-Lite is the floor for tier-2 and -3 vendors; full SIG + ISO 27036 + 800-161 for tier-1.
