# Evidence Artefact Reuse Index — Which Evidence Type Satisfies Most Controls Across Frameworks

This reference answers exactly one decision: **which evidence artefacts have the highest reuse leverage across the 12 supported frameworks, and what's the priority order for building them in a multi-framework programme?**

Pair with `scripts/evidence_pool_generator.py` for the operational catalogue. This document is the empirically-derived ranking + reasoning.

## Methodology

Reuse leverage = count of distinct (framework, control) tuples that one evidence artefact satisfies. Computed by tracing artefact-to-control mappings across:

- ISO/IEC 27001:2022 Annex A
- ISO/IEC 42001:2023 Annex A
- ISO 13485:2016 + ISO 14971:2019
- AICPA Trust Services Criteria (SOC 2)
- Regulation (EU) 2024/1689 (AI Act)
- Regulation (EU) 2017/745 (MDR)
- Regulation (EU) 2016/679 (GDPR)
- FDA 21 CFR 820 (QSR / QMSR)
- NIST Cybersecurity Framework 2.0
- Directive (EU) 2022/2555 (NIS2)
- HIPAA Security Rule + Privacy Rule + Breach Notification

For each evidence artefact, count of frameworks × controls satisfied = leverage score.

## The Top-Tier Artefacts (Build These First)

| Rank | Artefact | Reuse leverage | Acquisition cost | Why it's #1 |
|---|---|---|---|---|
| 1 | **Risk register with treatment plans** | 30+ mappings × 8+ frameworks | High | Every management-system standard + binding regulation demands risk management. Single artefact serves ISO 27001 Clause 6.1, ISO 42001 Clause 6.1.2, SOC 2 CC3, EU AI Act Article 9, GDPR Article 35 DPIA, NIST CSF GV.RM + ID.RA, NIS2 Article 21(2)(a), HIPAA §164.308(a)(1)(ii)(A) |
| 2 | **Asset inventory with classification** | 25+ mappings × 7+ frameworks | Medium | Required for ISO 27001 A.5.9-12, SOC 2 CC6.1, ISO 42001 A.4, GDPR Article 30, NIST CSF ID.AM, HIPAA §164.308 + §164.310(d). Foundation for almost every other artefact. |
| 3 | **Incident log + post-incident reviews + notifications** | 30+ mappings × 8+ frameworks | Medium | ISO 27001 A.5.24-27 + A.6.8, SOC 2 CC7.3-5, GDPR Articles 33-34, EU AI Act Article 73, NIS2 Article 23, HIPAA §164.308(a)(6) + Breach Notification, NIST CSF RS + RC |
| 4 | **Supplier inventory + reviews + DPAs/BAAs** | 25+ mappings × 8+ frameworks | Medium | ISO 27001 A.5.19-22, SOC 2 CC9.2, ISO 42001 A.10, GDPR Article 28, EU AI Act Article 25, NIST CSF GV.SC, NIS2 Article 21(2)(d), HIPAA §164.314(a) BAA |
| 5 | **Policy set (AI + info-sec + privacy + code-of-conduct)** | 20+ mappings × 7+ frameworks | Medium | ISO 27001 A.5.1, ISO 42001 Clause 5.2 + A.2.2-3, SOC 2 CC1.1-2, GDPR Article 24, NIST CSF GV.PO, EU AI Act Article 17(1)(a) |

## High-Leverage Artefacts (Build Next)

| Rank | Artefact | Reuse leverage | Acquisition cost | Notes |
|---|---|---|---|---|
| 6 | **Centralized tamper-evident logs** | 20+ mappings × 6+ frameworks | High | ISO 27001 A.8.15-16, SOC 2 CC7.1-2, ISO 42001 A.9.3-4, EU AI Act Article 12 + 72, NIST CSF DE.CM, HIPAA §164.312(b) audit controls |
| 7 | **Training records (per role, with effectiveness verification)** | 18+ mappings × 7+ frameworks | Medium | ISO 27001 A.6.3, SOC 2 CC1.4 + CC2.2, ISO 42001 Clause 7.2-3 + A.4.4, EU AI Act Article 4, NIST CSF PR.AT, NIS2 Article 21(2)(g), HIPAA §164.308(a)(5) |
| 8 | **Data inventory + provenance + consent register** | 20+ mappings × 6+ frameworks | High | ISO 27001 A.5.34, ISO 42001 A.7, EU AI Act Article 10, GDPR Articles 5+6+30, NIST CSF PR.DS + ID.AM-07, HIPAA §164.502 + §164.514 |
| 9 | **Internal audit programme records** | 15+ mappings × 6+ frameworks | Medium | ISO 27001 Clause 9.2, ISO 42001 Clause 9.2, ISO 13485 Clause 8.2.4, SOC 2 CC4.1, NIST CSF ID.IM, HIPAA §164.308(a)(8) |
| 10 | **Management review minutes + action tracking** | 12+ mappings × 5+ frameworks | Low | ISO 27001 Clause 9.3, ISO 42001 Clause 9.3, ISO 13485 Clause 5.6, NIST CSF GV.OV, NIS2 Article 20 |

## Mid-Leverage Artefacts

| Rank | Artefact | Reuse leverage | Acquisition cost | Notes |
|---|---|---|---|---|
| 11 | **Change records + rollback procedures + post-implementation reviews** | 14+ mappings × 5+ frameworks | Low | ISO 27001 A.8.32, SOC 2 CC8.1, ISO 42001 A.6.2.5, ISO 13485 Clause 7.3.9, NIST CSF PR.PS, HIPAA §164.308(a)(5)(ii)(B) |
| 12 | **Crypto records (algorithms, key lifecycle, KMS architecture)** | 14+ mappings × 6+ frameworks | Medium | ISO 27001 A.8.24, SOC 2 CC6.1 + CC6.7, GDPR Article 32(1)(a), NIST CSF PR.DS-01-02 + PR.PS-05, NIS2 Article 21(2)(h), HIPAA §164.312(a)(2)(iv) + §164.312(e)(2)(ii) |
| 13 | **BCP/DRP + RPO/RTO + exercise records** | 12+ mappings × 5+ frameworks | High | ISO 27001 A.5.29-30 + A.8.13-14, SOC 2 A1.2-3, NIST CSF RC.RP + RC.IM + RC.CO, NIS2 Article 21(2)(c), HIPAA §164.308(a)(7) |
| 14 | **DPIA records + LIAs + privacy notice version history** | 12+ mappings × 4+ frameworks | High | GDPR Articles 5+6+24+25+30+35+38, EU AI Act Article 27 FRIA (overlap), ISO 27001 A.5.34, ISO 42001 A.7.6 |
| 15 | **Quarterly access review records + RBAC matrix + JML evidence** | 18+ mappings × 7+ frameworks | Low | ISO 27001 A.5.15 + A.8.2-3, SOC 2 CC6.1-3, ISO 42001 A.4.4, GDPR Article 32(1)(b), NIST CSF PR.AA, NIS2 Article 21(2)(i), HIPAA §164.308(a)(3-4) + §164.312(a)(1) |
| 16 | **Vulnerability scan + patch SLA + remediation evidence** | 12+ mappings × 5+ frameworks | Medium | ISO 27001 A.8.7-9, SOC 2 CC7.1-2 + CC7.4, NIST CSF ID.RA + PR.PS-02, NIS2 Article 21(2)(f), HIPAA §164.308(a)(5)(ii)(B) |

## Low-Leverage (Framework-Specific) Artefacts

Build these only when the specific framework applies; lower reuse value across the programme.

| Artefact | Primary framework(s) | Why low-leverage |
|---|---|---|
| Annex IV technical documentation (EU AI Act) | EU AI Act | Specific to AI Act high-risk systems |
| Design History File (DHF) | ISO 13485, FDA QSR | Specific to medical-device QMS |
| Process validation (IQ/OQ/PQ) | ISO 13485, FDA QSR | Specific to medical-device manufacturing |
| Clinical evaluation (Annex XIV) | EU MDR | Specific to medical-device EU placement |
| Model card + datasheet | ISO 42001, EU AI Act | AI-specific |
| FRIA (Fundamental Rights Impact Assessment) | EU AI Act | Specific to high-risk AI public-sector deployers |
| Notice of Privacy Practices | HIPAA | Specific to US healthcare |
| Form 483 response records | FDA QSR | Specific to FDA-inspected entities |
| NIS2 incident notifications (24h/72h/1m) | NIS2 | Specific to NIS2-in-scope entities |
| EUDAMED registration | EU MDR | Specific to EU MDR |

## Reuse-Leverage Operational Pattern

For a multi-framework programme, the recommended build order is:

```
Phase 1 (Weeks 1-4):
  - Risk register with treatment plans (top reuse)
  - Asset inventory with classification
  - Policy set
  - Quarterly access review records + RBAC matrix

Phase 2 (Weeks 5-12):
  - Centralized tamper-evident logs
  - Supplier inventory + DPAs/BAAs
  - Training records
  - Crypto records
  - Internal audit programme records
  - Management review records

Phase 3 (Weeks 13-24):
  - Data inventory + provenance + consent (build alongside Phase 1 if GDPR/HIPAA early)
  - BCP/DRP + exercise records
  - DPIA records
  - Vulnerability scan + remediation
  - Change records + rollback procedures
  - Incident log + post-incident reviews
  - Physical security records (if applicable)

Phase 4 (Weeks 25+):
  - Framework-specific artefacts:
    * Annex IV docs (if EU AI Act)
    * DHF + process validation (if ISO 13485 / FDA QSR)
    * Clinical evaluation (if EU MDR)
    * Model cards + datasheets (if ISO 42001)
    * FRIA (if EU AI Act public-sector deployer)
    * Notice of Privacy Practices (if HIPAA)
```

## Common Mistakes (Anti-Patterns)

1. **Building framework-specific artefacts before top-tier reuse artefacts.** Common when team is led by a single-framework specialist; results in 5x more total effort across the programme.
2. **Separate evidence stores per framework.** Each framework wants the same access-review log; storing it 3 times in 3 systems = stale + inconsistent.
3. **Not citing the same artefact in multiple audit reports.** Different auditors may ask for the same evidence renamed; cite the shared artefact ID in both reports.
4. **Skipping centralized inventory in Phase 1.** Asset inventory is the foundation for risk register, supplier list, data inventory, etc. Without it, everything downstream is incomplete.
5. **Treating evidence as one-time collection rather than continuous artefact.** Quarterly access review records must be produced quarterly, not "fixed for the audit and then ignored".

## Evidence Freshness Discipline

Reuse leverage breaks down if evidence is stale. Per-artefact target freshness:

| Artefact | Refresh cadence | Stale = ineffective |
|---|---|---|
| Risk register | Quarterly minimum | Within 90 days |
| Asset inventory | Quarterly minimum | Within 90 days |
| Access review records | Quarterly | Within 1 quarter |
| Incident log + PIRs | Continuous + 30-day PIR | PIR within 30 days |
| Supplier reviews | Annually | Within 12 months |
| Training records | Annually + new-hire 30 days | Annual completion 100% |
| Policy set | Annually reviewed | Within 12 months |
| Crypto inventory | Quarterly review | Within 90 days |
| DPIA records | At new processing + on material change | Always current |
| BCP/DRP exercise records | Annually | Within 12 months |

## Anti-Reuse Patterns to Avoid

- **Per-framework reformatting** — collecting an artefact, then reformatting for each framework's report. Cite the shared artefact + map to framework controls instead.
- **Per-team ownership without integration** — security owns SOC 2 evidence, DPO owns GDPR evidence, RA/QM owns ISO 13485 evidence, no shared discovery layer. Use compliance-os meta-orchestrator to enforce shared inventory.
- **Custodial-only ownership** — artefact lives in one team's drive without index. New audit cycle re-discovers from scratch.

## When This Reference Doesn't Help

- **Specific GRC platform configuration.** Tooling decision; see vendor documentation.
- **Per-control evidence requirements.** See per-framework skill references.
- **Sector-specific evidence (financial NYDFS, energy NERC CIP).** Sectoral; not in 12-framework scope.

---

**Source authorities (non-exhaustive):**

- **ISO/IEC 27001:2022** + Annex A
- **ISO/IEC 42001:2023** + Annex A
- **ISO/IEC 19011:2018** — Guidelines for auditing management systems (audit evidence)
- **AICPA Trust Services Criteria** (2017 + 2022 update) + SOC 2 Reporting Guide
- **Regulation (EU) 2024/1689** — AI Act
- **Regulation (EU) 2017/745** — EU MDR
- **Regulation (EU) 2016/679** — GDPR
- **Regulation (EU) 2022/2555** — NIS2 Directive
- **NIST Cybersecurity Framework 2.0** + NIST SP 800-53A Rev 5 assessment procedures
- **HIPAA 45 CFR Parts 160 + 164** — Security + Privacy + Breach Notification Rules
- **FDA 21 CFR 820** — Quality System Regulation
- **ISO 13485:2016** + ISO 14971:2019
- **IIA International Professional Practices Framework** — Performance Standards on engagement records (2330)
- **DAMA-DMBOK 2** — Data Management Body of Knowledge (provenance + quality dimensions)
- **NIST SP 800-92** — Guide to Computer Security Log Management (retention + integrity)
- **Industry retrospectives** — Big 4 + Schellman + Coalfire + A-LIGN published findings on common audit exceptions
