# Evidence Management — Unified Pool + Reuse Leverage

This reference answers exactly one decision: **how do we collect compliance evidence once and satisfy multiple frameworks, without losing audit-grade traceability?**

Pair with `scripts/evidence_pool_generator.py` for the deterministic evidence catalogue.

## The Evidence Reuse Problem

Most multi-framework compliance programs accidentally collect the same evidence multiple times. Each framework's auditor wants:

- A documented procedure (the "what should happen")
- Records that the procedure was followed (the "what actually happened")
- Evidence of management oversight (the "did anyone check?")

When ISO 27001, SOC 2, and ISO 42001 audits ask for "access review records," teams often produce three different exports of the same Okta data with different formatting because three different control owners assembled them.

The fix: a **unified evidence pool** with explicit (artefact, framework, control) mapping. Collect once; cite multiple times.

## The Reuse-Leverage Score

Every evidence artefact gets a **reuse-leverage score** = number of distinct (framework, control) tuples it satisfies. Higher score = higher priority to build first.

From the `evidence_pool_generator.py` curated catalogue, the top-leverage artefacts (when all 9 frameworks are enabled):

| Artefact | Leverage |
|---|---|
| Risk register | 9+ mappings |
| Supplier inventory + reviews + DPAs | 8+ |
| Incident log + post-mortems + notifications | 11+ |
| Data inventory + provenance + consent | 9+ |
| Policy set (AI + info-sec + privacy + code-of-conduct) | 8+ |
| Tamper-evident logs centralized | 7+ |
| Training records | 6+ |

**Implementation order:** build high-leverage artefacts first. The risk register alone unlocks evidence for 9+ controls across 4+ frameworks.

## Evidence Acquisition Cost

The catalogue tracks acquisition cost per artefact: low / medium / high.

| Cost | Examples | Time to build |
|---|---|---|
| **Low** | Quarterly access review records, change records, management review records | 1-2 weeks (often automated from existing IT systems) |
| **Medium** | Asset register, supplier inventory, training records, crypto records, vuln scans | 2-6 weeks (requires inventory + classification) |
| **High** | Risk register, BCP/DR exercises, data inventory + consent register, secure SDLC | 6-12 weeks (requires cross-functional process design) |

**Strategy:** in year 1, prioritize low-cost high-leverage artefacts (e.g., management review records, change records). Build high-cost high-leverage artefacts in parallel (risk register, data inventory).

## Retention by Framework

Retention requirements vary per framework. Use the longest applicable retention:

| Framework | Typical retention |
|---|---|
| ISO 27001 | 3 years for audit evidence (or as policy specifies) |
| SOC 2 | 1 year minimum; 3 years recommended |
| ISO 42001 | 3 years (Clause 7.5 documented information) |
| EU AI Act | 10 years for declaration of conformity (Article 18); other docs 6 years |
| GDPR | Varies by data type; data subject records 3 years; breach records indefinite |
| ISO 13485 | Lifecycle of device + period defined by regulator (often 5+ years) |
| EU MDR | Device lifetime + 10 years (Article 10) |
| FDA QSR | 2 years past commercial distribution (21 CFR 820.180) |

**Default policy:** 36 months for most artefacts; 60 months for personal-data and policy-set artefacts; 120 months for EU AI Act declarations of conformity.

## Evidence Freshness

Auditors want recent evidence, not stale. Freshness expectations:

- Operational records (access reviews, change records, incident records): within last 90-180 days
- Quarterly artefacts: at least 1 record from current quarter
- Annual artefacts (training records, supplier reviews, BCP exercises): within last 12 months
- Policies: reviewed annually (review records demonstrate freshness)

**Stale evidence = effective gap.** An ISO 27001 A.5.15 quarterly access review that was last conducted 8 months ago is a major nonconformity even if the review existed historically.

## Evidence Owner Assignment

Each artefact has a primary owner. Typical pattern:

| Artefact type | Primary owner | Secondary |
|---|---|---|
| Access reviews | IT / Security | Compliance |
| Asset register | Security | DPO |
| Risk register | Compliance officer | Risk manager |
| Supplier inventory | Procurement | Compliance + DPO |
| Incident log | Security / IR team | Compliance |
| Logs (centralized) | Platform / SRE | Security |
| Change records | Engineering / Platform | Compliance |
| BCP/DR | Platform / SRE | Compliance |
| Training records | HR / People Ops | Compliance |
| Data inventory + consent | DPO / Data team | Engineering |
| Internal audit records | Compliance officer | Internal auditor |
| Management review records | Compliance officer + Exec | All function heads |
| Policy set | Compliance officer + Exec | All policy owners |
| Crypto records | Security | Platform |
| Vuln scans + patches | Security | Engineering |

**Single accountable owner per artefact** is critical. Joint ownership without accountability is the most common cause of stale evidence.

## Evidence Storage Architecture

Patterns observed in mature programs:

1. **GRC platform (Drata, Vanta, OneTrust, Hyperproof, etc.)** — the most common pattern; integrates with operational tools (Okta, AWS, GitHub) and auto-pulls evidence. Centralizes audit-trail.
2. **Compliance-team-managed repository** — folder per framework with subdivision per control; manual evidence assembly. Works for small programs; doesn't scale.
3. **Hybrid** — automated evidence (logs, access reviews, change records) in GRC platform; manual evidence (policies, management review minutes, training records) in document management system. Most common at growth-stage.

Compliance OS does not prescribe a storage pattern — but it does require:
- Single index of evidence (the unified pool)
- Per-evidence audit trail (who created, who approved, when)
- Per-evidence retention timer
- Per-evidence freshness alert

## Evidence Pool Quality Indicators

Healthy pool:

| Indicator | Healthy value |
|---|---|
| Average reuse leverage | ≥ 4 |
| Stale evidence (past expected freshness) | 0% |
| Orphan controls (no evidence assigned) | 0 |
| Unowned artefacts | 0 |
| Retention compliance | 100% |

Unhealthy pool:

- Many low-leverage artefacts (each satisfies only 1 framework) — likely silo'd collection
- High stale rate — operational discipline broken
- Orphan controls — gap in coverage that will surface at next audit

## Evidence Pool Audit (the meta-audit)

Once a year, audit the evidence pool itself:

1. Sample 10% of artefacts; verify they exist + are owned + are fresh
2. Sample 10% of controls; verify each has at least one evidence artefact assigned
3. Verify retention compliance — look for old evidence that should be deleted (GDPR retention) and recent evidence that should be retained longer
4. Verify framework coverage — are all enabled frameworks adequately represented?

This audit-of-audit is the most underappreciated discipline in mature multi-framework programs.

## When This Reference Doesn't Help

- **Specific GRC platform configuration.** Tooling-specific; market evolves rapidly.
- **Evidence retention for novel data types (e.g., AI training data).** Sector-specific; engage counsel.
- **Cross-framework specific mapping.** See `cross_framework_overlap.md`.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 27001:2022 Clause 7.5** — Documented information requirements
- **ISO/IEC 42001:2023 Clause 7.5** — AI-specific documented information
- **AICPA AT-C 205** — Examination engagements (SOC 2 evidence standards)
- **NIST SP 800-53A Rev 5** — Assessing Security and Privacy Controls (per-control evidence types)
- **NIST SP 800-92** — Guide to Computer Security Log Management
- **ISO/IEC 19011:2018 Clause 6.4** — Conducting audit activities (evidence collection)
- **IIA IPPF Performance Standard 2330** — Documenting Information (engagement records)
- **GDPR Article 30** — Records of processing activities (retention + evidence)
- **EU AI Act Article 18** — Document retention (10 years post-market for declaration of conformity)
- **FDA 21 CFR 820.180** — General requirements for records (2 years past commercial distribution)
- **DAMA-DMBOK 2** — Data Management Body of Knowledge (data-quality + provenance frameworks)
