# GDPR / DSGVO Compliance Audit Playbook

This reference answers exactly one decision: **how do we audit GDPR compliance (the binding Regulation (EU) 2016/679) — including DPIA quality, lawful-basis discipline, data subject rights workflow, and supervisory authority readiness?**

Pair with the per-area Python tools in this skill (`gdpr_compliance_checker.py`, `dpia_generator.py`, `data_subject_rights_tracker.py`) and `compliance-os/scripts/audit_simulator.py` for mock-audit preparation.

## Key Difference from ISO Audits

GDPR is not a management system — it's binding regulation with direct enforcement by national supervisory authorities (DPAs). There's no "GDPR certification audit" in the ISO sense. Instead:

- **Internal audit** verifies compliance with the Regulation's articles (this playbook)
- **DPA investigation** is a binding enforcement action (typically triggered by complaint or breach)
- **GDPR seal / certification** (Article 42) exists but is rarely operationalized; most companies do not pursue formal certification

**Penalties** are real: up to EUR 20M or 4% of worldwide annual turnover (Article 83) for the highest-tier violations.

## When to Use This Playbook

- Annual internal GDPR audit (organizational discipline)
- Quarterly Article 30 records-of-processing refresh
- Pre-launch DPIA review (for new high-risk processing)
- Post-breach internal audit (after Article 33 notification)
- Pre-DPA investigation readiness check
- Acquisition due diligence (target's GDPR posture)

## The Audit Workflow

Same 7-phase structure (Plan / Prepare / Open / Field / Close / Report / Track), with GDPR-specific content:

### Phase 4 Field — Article-Level Audit Procedures

The audit covers 7 substantive areas. Each maps to specific Articles.

#### 1. Article 5 — Lawfulness, Fairness, Transparency (the principles)

For each significant processing activity, verify:

- **Lawful basis identified and documented** (Article 6(1)(a)-(f) — consent, contract, legal obligation, vital interests, public task, legitimate interests)
- **Purpose specified at collection** (Article 5(1)(b)); incompatible secondary use prohibited
- **Data minimisation** (Article 5(1)(c)); evidence: data inventory + retention schedule
- **Accuracy** (Article 5(1)(d)); evidence: data quality + correction workflow
- **Storage limitation** (Article 5(1)(e)); evidence: deletion schedule executed
- **Integrity + confidentiality** (Article 5(1)(f)); evidence: ISO 27001 controls
- **Accountability** (Article 5(2)); evidence: documented decisions + records

#### 2. Article 6 — Lawful Basis Discipline

Common findings:

- "Consent" claimed but consent records not maintained (Article 7)
- "Legitimate interests" claimed without LIA (Legitimate Interests Assessment) documentation
- Multiple lawful bases listed for same processing (Article 6 is exclusive — pick ONE per purpose)
- Children's data processed under Article 6(1)(a) without parental consent verification per Article 8

#### 3. Article 9 — Special Categories

Audit any processing of special categories (race, religion, political opinion, health, biometric, sex life, etc.):

- Article 9(2) exception identified and documented
- Heightened safeguards in place (encryption, access restriction)
- For health data: alignment with sectoral law (Member State derogation per Article 9(4))

#### 4. Article 30 — Records of Processing Activities (RoPA)

Most common finding area. Verify:

- RoPA exists for both Article 30(1) (controller) and Article 30(2) (processor) where applicable
- All required information present per Article 30(1)(a)-(g) and Article 30(2)(a)-(d)
- RoPA updated within reasonable time of changes
- Joint controller arrangements documented per Article 26

#### 5. Article 35 — DPIA (Data Protection Impact Assessment)

Required for high-risk processing (Article 35(3) plus DPA-published lists). Verify:

- DPIA conducted before processing begins
- DPIA covers Article 35(7)(a)-(d) required elements:
  - Systematic description of the processing
  - Assessment of necessity + proportionality
  - Risks to rights and freedoms
  - Measures to address risks
- DPO consulted per Article 35(2) (if DPO appointed)
- Article 36 prior consultation triggered for residual high risk

Use `dpia_generator.py` (this skill) to assess DPIA completeness.

#### 6. Articles 12-22 — Data Subject Rights

Verify operational workflow for each right:

| Article | Right | Audit focus |
|---|---|---|
| 13/14 | Right to information | Privacy notice fresh + complete |
| 15 | Right of access | Response within 1 month (Article 12(3)); identity verification process |
| 16 | Right to rectification | Correction workflow documented |
| 17 | Right to erasure ("right to be forgotten") | Deletion procedure including backups + processors |
| 18 | Right to restriction | Restriction workflow |
| 19 | Notification obligation | Downstream notification to recipients |
| 20 | Right to data portability | Machine-readable format + transmission capability |
| 21 | Right to object | Including profiling-based processing |
| 22 | Automated decision-making + profiling | AI overlap; significant decisions require human review |

Use `data_subject_rights_tracker.py` (this skill) to validate workflow + timing.

#### 7. Article 28 — Processor Obligations + Sub-Processors

For each processor:

- Article 28(3) contract in place with all required clauses (a)-(j)
- Sub-processor list maintained + change notification mechanism
- Audit / inspection rights documented + actually exercised
- Standard Contractual Clauses (SCCs) per Commission Implementing Decision (EU) 2021/914 for non-EU transfers

#### 8. Article 32 — Security of Processing

Heavy overlap with ISO 27001 Annex A. Verify:

- Encryption (Article 32(1)(a))
- Confidentiality + integrity + availability + resilience (Article 32(1)(b))
- Backup + recovery (Article 32(1)(c))
- Regular testing + evaluation (Article 32(1)(d))
- Risk-appropriate measures per Article 32(2)

#### 9. Articles 33-34 — Breach Notification

Audit procedure + recent events:

- Detection mechanism in place
- Internal escalation path documented
- Article 33 notification to DPA within 72 hours (where required)
- Article 34 notification to data subjects (where high risk)
- Breach log per Article 33(5) maintained

#### 10. Article 37 — DPO Appointment

If DPO required (Article 37(1)(a)-(c)), verify:

- DPO appointment formal + published
- DPO independence (Article 38) — no conflicts; reports to highest management
- DPO contact published per Article 37(7)
- DPO tasks per Article 39 performed

## Common Findings (Practitioner Patterns)

Most-cited GDPR audit findings:

1. **RoPA exists but is stale** (>6 months without refresh)
2. **Cookie consent banner not GDPR-compliant** (pre-ticked, ambiguous, no granular control)
3. **Privacy notice missing Article 13/14 required elements** (especially retention periods + data subject rights)
4. **DPIA missing or incomplete** for high-risk processing (especially AI / profiling / large-scale surveillance)
5. **Data subject access request (DSAR) response > 1 month**
6. **Processor contracts missing one or more Article 28(3) clauses**
7. **International transfers without SCCs or adequacy decision**
8. **Breach log empty or only contains DPA-notifiable events** (Article 33(5) requires ALL breaches logged)
9. **Lawful basis = "legitimate interests" without documented LIA**
10. **Special-category processing without Article 9(2) exception cited**
11. **Vendor onboarding without DPIA / TIA (Transfer Impact Assessment)**

## Schrems II + International Transfers

Critical post-2020 area. Verify for every non-EU transfer:

- Adequacy decision exists (Article 45) OR SCCs signed (Article 46) OR derogation applies (Article 49)
- Transfer Impact Assessment (TIA) performed per EDPB Recommendations 01/2020 + 02/2020
- Supplementary measures where TIA flags risk (encryption, pseudonymisation, contractual)
- US transfers post-2023 covered by EU-US Data Privacy Framework adequacy decision

## DPA / Supervisory Authority Readiness

Internal audit should produce a "DPA readiness pack" annually:

- Current Article 30 RoPA (most-asked artifact in DPA investigation)
- DPIA log (covering high-risk processing past 24 months)
- Breach log (Article 33(5))
- Data Subject Rights response log + average response time
- DPO appointment record + activity log
- Processor list with Article 28(3) contracts + sub-processor flow-down
- International transfer mechanisms documented per recipient

## Cross-Framework Reuse

GDPR audit work supports:

- **ISO 27001** — Article 32 organizational measures = ISO 27001 Annex A (heavy reuse)
- **ISO 42001** — AI privacy controls (A.7.6 data privacy considerations) reuse GDPR DPIA
- **EU AI Act** — Article 27 FRIA can integrate with DPIA artefact for public-sector / essential-services deployers
- **SOC 2** — Privacy criteria (PI series) overlap with GDPR
- **Schrems II** — Transfer Impact Assessments cross-walk with cybersecurity / surveillance assessments

Pair with `compliance-os/references/multi_framework_audit_playbook.md`.

## When This Reference Doesn't Help

- **ePrivacy Directive / ePrivacy Regulation (cookies, electronic communications).** Sectoral; separate from GDPR.
- **Sectoral law overlay (PCI DSS, HIPAA, FERPA, GLBA).** Sector-specific.
- **National derogations under Article 23.** Member State-specific; consult national law.
- **Specific DPA enforcement record review.** Required for novel cases; consult outside counsel.

---

**Source authorities (non-exhaustive):**

- **Regulation (EU) 2016/679** — GDPR (the binding text)
- **EDPB Guidelines** — including DPIA list (Article 35(4)), data subject rights, breach notification
- **EDPB Recommendations 01/2020 and 02/2020** — supplementary measures for international transfers (Schrems II)
- **EDPB Opinion 28/2024** — AI models and personal data (December 2024)
- **Commission Implementing Decision (EU) 2021/914** — Standard Contractual Clauses for international transfers
- **EU-US Data Privacy Framework adequacy decision (10 July 2023)**
- **Article 29 Working Party Opinions** (legacy; still influential under EDPB)
- **National DPA guidelines** — CNIL (France), BfDI / state DPAs (Germany), AEPD (Spain), Garante (Italy), ICO (UK pre-Brexit equivalent under UK GDPR)
- **ISO/IEC 27701:2019** — Privacy information management extension to ISO 27001 (operationalizes GDPR controls)
- **IAPP CIPP/E + CIPM materials** — practitioner audit methodology
- **Court of Justice of the European Union (CJEU) case law** — Schrems II (C-311/18), Planet49 (C-673/17), and others
