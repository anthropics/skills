# Compliance Roadmap Reference

## Decision Framework: Which Framework First?

**Start here — who are your customers?**

```
Enterprise SaaS (B2B, US market)  →  SOC 2 Type II first
Healthcare / health data           →  HIPAA + SOC 2 together
EU customers or EU-resident data   →  GDPR (non-optional if applicable)
EU enterprise sales                →  ISO 27001 + GDPR
Government / defense               →  FedRAMP / CMMC (separate scope)
All of the above (Series B+)       →  Multi-framework efficiency approach
```

**The sequencing principle:** SOC 2 Type I is the fastest proof of intent (3–6 months). Type II is the credibility signal (12 months). Everything else builds on your control library.

---

## 1. SOC 2

### What It Is
SOC 2 is an attestation (not a certification) that your controls meet the AICPA Trust Service Criteria. An independent CPA firm audits your controls and issues a report.

- **Type I:** Controls are suitably designed at a point in time (snapshot). Lower credibility but faster.
- **Type II:** Controls operated effectively over a period of time (minimum 6 months). This is what enterprise buyers want.

### Trust Service Criteria (TSC)
You must include **Security** (CC). Others are optional:
| Criteria | When to add |
|---|---|
| Security (CC) | Always required |
| Availability | If uptime SLAs are contractual |
| Confidentiality | If you process confidential third-party data |
| Processing Integrity | If accuracy of processing is critical (fintech, data processing) |
| Privacy | If you make privacy commitments beyond GDPR/CCPA scope |

Most startups: **Security + Availability** is sufficient.

### Timeline: SOC 2 Type I

| Phase | Duration | Activities |
|---|---|---|
| Readiness assessment | 2–4 weeks | Gap analysis against CC criteria, identify control owners |
| Policy documentation | 4–6 weeks | Write ~15–20 policies (acceptable use, access control, change management, etc.) |
| Control implementation | 4–8 weeks | Deploy technical controls, fix gaps identified in readiness |
| Evidence collection | 2–4 weeks | Screenshots, logs, configs — auditor will sample these |
| Audit fieldwork | 2–4 weeks | CPA firm reviews evidence, interviews control owners |
| Report issuance | 2–4 weeks | Report issued, reviewed, shared with customers |
| **Total** | **3–6 months** | — |

### Timeline: SOC 2 Type II (after Type I)

| Phase | Duration | Notes |
|---|---|---|
| Observation period | 6–12 months | Controls must operate consistently — no exceptions |
| Audit fieldwork | 4–6 weeks | Auditor samples evidence across full period |
| Report issuance | 2–4 weeks | — |
| **Total from Type I** | **9–18 months** | Faster if Type I was clean |

### Cost Estimates

| Item | SOC 2 Type I | SOC 2 Type II |
|---|---|---|
| Audit firm fees | $15,000–$35,000 | $25,000–$60,000 |
| Compliance platform (Vanta, Drata, Secureframe) | $12,000–$30,000/yr | Same platform |
| External counsel / vCISO | $10,000–$30,000 | $5,000–$15,000 maintenance |
| Internal time (eng + ops) | 200–400 hours | 100–200 hours/yr |
| **Total first year** | **$40,000–$100,000** | **+$30,000–$75,000** |

**Cost optimization tips:**
- Use a compliance platform (Vanta, Drata, Secureframe) — automated evidence collection halves audit cost
- Choose a mid-tier audit firm; Big 4 is overkill for startups
- Type I and Type II with same auditor = continuity discount

### Common Failure Modes
1. Controls documented but not operating (access reviews on paper only)
2. Exceptions during observation period (one admin account without MFA = finding)
3. No formal security awareness training (required for CC criteria)
4. Change management not followed (no ticket for that production change)
5. Vendor risk management missing (you must assess your critical vendors)

---

## 2. ISO 27001

### What It Is
ISO 27001 is an internationally recognized certification for an Information Security Management System (ISMS). Unlike SOC 2, it's a certification (pass/fail), not an attestation report. Issued by accredited certification bodies (BSI, Bureau Veritas, DNV, TÜV).

**Why ISO 27001 over SOC 2:** EU enterprise buyers, government contracts, and global markets often prefer or require ISO 27001. It's geographically neutral.

### Scope Decision
ISO 27001 scope is flexible — you can certify a subset of the organization.
- **Narrow scope:** The production environment only — fastest, cheapest
- **Full scope:** Entire organization — most credibility, highest effort
- **Recommended for startups:** Production environment + key business processes

### Certification Timeline

| Phase | Duration | Activities |
|---|---|---|
| Gap analysis | 2–4 weeks | Assess current state vs. 93 controls in Annex A |
| ISMS design | 4–8 weeks | Scope, risk methodology, SoA (Statement of Applicability) |
| Policy and procedure development | 6–10 weeks | Mandatory documents: risk treatment plan, asset register, ISMS policy |
| Risk assessment | 4–6 weeks | Identify, analyze, evaluate risks; produce risk register |
| Control implementation | 8–16 weeks | Implement gaps from risk assessment |
| Internal audit | 2–4 weeks | First internal audit of ISMS |
| Management review | 1–2 weeks | Leadership sign-off on ISMS |
| Stage 1 audit (documentation) | 1–2 weeks | Certification body reviews docs and scope |
| Stage 2 audit (implementation) | 1–2 weeks | Certification body verifies controls are operating |
| Certification issued | 1–2 weeks | Certificate valid for 3 years with annual surveillance audits |
| **Total** | **9–18 months** | — |

### Cost Estimates

| Item | Cost |
|---|---|
| Certification body fees (Stage 1 + Stage 2) | $15,000–$40,000 |
| Annual surveillance audits | $8,000–$20,000/yr |
| vCISO / consultant (if not in-house) | $30,000–$80,000 |
| GRC platform | $10,000–$25,000/yr |
| Internal time | 400–800 hours |
| **Total first year** | **$55,000–$150,000** |

### Mandatory ISO 27001:2022 Documents
- ISMS scope document
- Information security policy
- Risk assessment methodology
- Risk register with risk treatment plan
- Statement of Applicability (SoA)
- Asset inventory
- Competence and awareness records
- Internal audit reports
- Management review minutes
- Nonconformity and corrective action records

---

## 3. HIPAA for Health Tech Startups

### When HIPAA Applies
HIPAA applies if you are a **Covered Entity** (healthcare provider, health plan, clearinghouse) or a **Business Associate** (you process, store, or transmit Protected Health Information on behalf of a Covered Entity).

**Key trigger:** If your product touches patient data in any way and a US healthcare provider uses your product, you are likely a Business Associate. You must sign a **BAA (Business Associate Agreement)** with each Covered Entity customer.

### HIPAA Rule Structure
| Rule | Focus | Key Requirements |
|---|---|---|
| Privacy Rule | How PHI can be used and disclosed | Minimum necessary, patient rights, notice of privacy practices |
| Security Rule | Technical and physical safeguards for ePHI | Required and addressable safeguards |
| Breach Notification Rule | What to do if PHI is breached | Timing and content of breach notifications |

### Security Rule: Required vs. Addressable
**Required safeguards** must be implemented exactly as specified. **Addressable safeguards** must be implemented or documented why an equivalent measure was used.

**Key Required Safeguards:**
- Unique user IDs (no shared logins)
- Emergency access procedure
- Audit controls (logging access to ePHI)
- Transmission security (encryption in transit)
- Person or entity authentication

**Key Addressable Safeguards (implement or document why not):**
- Automatic logoff
- Encryption and decryption (encryption at rest — despite being "addressable," regulators expect it)
- Audit review procedures
- Security reminders and training

### HIPAA Compliance Timeline

| Phase | Duration | Activities |
|---|---|---|
| Risk analysis | 4–6 weeks | Document all PHI flows, assess risks to PHI — **required by law** |
| Policy development | 4–8 weeks | Privacy policies, breach notification, workforce training |
| Technical safeguard implementation | 4–12 weeks | Encryption, audit logging, access controls, BAA templates |
| Workforce training | 2–4 weeks | Annual HIPAA training for all staff with PHI access |
| BAA execution | Ongoing | Execute with all vendors who process PHI |
| **Total** | **4–8 months** | — |

### Cost Estimates
| Item | Cost |
|---|---|
| Initial risk analysis (consultant) | $15,000–$40,000 |
| Policy development | $8,000–$20,000 |
| Technical implementation | $20,000–$60,000 |
| Annual training and maintenance | $5,000–$15,000/yr |
| HIPAA compliance platform | $10,000–$20,000/yr |
| **Total first year** | **$45,000–$130,000** |

### HIPAA Penalties (Why This Matters)
| Violation Category | Penalty per Violation | Annual Cap |
|---|---|---|
| Unaware | $100–$50,000 | $25,000 |
| Reasonable cause | $1,000–$50,000 | $100,000 |
| Willful neglect (corrected) | $10,000–$50,000 | $250,000 |
| Willful neglect (not corrected) | $50,000 | $1,500,000 |

---

## 4. GDPR Compliance Program

### When GDPR Applies
GDPR applies if you:
- Are established in the EU/EEA
- Process personal data of EU/EEA residents (regardless of your location)
- Offer goods or services to EU residents
- Monitor the behavior of EU residents

**Key point for US startups:** If you have EU users or EU employees, GDPR applies to you.

### Core GDPR Principles (Build These In)
1. **Lawfulness, fairness, transparency** — have a legal basis for every processing activity
2. **Purpose limitation** — collect data for specified, explicit purposes only
3. **Data minimization** — collect only what you need
4. **Accuracy** — keep data accurate
5. **Storage limitation** — delete data when no longer needed
6. **Integrity and confidentiality** — appropriate security measures
7. **Accountability** — demonstrate compliance

### Legal Bases for Processing
| Basis | When to use |
|---|---|
| Consent | Marketing, non-essential cookies, optional features |
| Contract | Processing necessary to deliver your service |
| Legitimate interests | Analytics, fraud prevention, security (requires LIA) |
| Legal obligation | Compliance with legal requirements |
| Vital interests | Emergency situations only |

**Avoid over-relying on consent** — it must be freely given, specific, informed, and unambiguous. Contractual basis is more robust for core product data.

### GDPR Compliance Checklist

**Governance:**
- [ ] Data Protection Officer (DPO) appointed (required for large-scale processing or sensitive data)
- [ ] Record of Processing Activities (RoPA) maintained
- [ ] Data Protection Impact Assessments (DPIA) for high-risk processing

**Rights Management (respond within 1 month):**
- [ ] Right of access (data subject access requests — DSARs)
- [ ] Right to rectification
- [ ] Right to erasure ("right to be forgotten")
- [ ] Right to data portability
- [ ] Right to object to processing

**Technical Measures:**
- [ ] Privacy by design in product development
- [ ] Data minimization enforced
- [ ] Encryption at rest and in transit
- [ ] Pseudonymization where possible
- [ ] Retention policies and automated deletion

**Vendor Management:**
- [ ] Data Processing Agreements (DPAs) with all processors
- [ ] Standard Contractual Clauses (SCCs) for non-EU transfers

**Breach Notification:**
- [ ] Notify supervisory authority within 72 hours of awareness
- [ ] Notify affected individuals if high risk to their rights and freedoms

### GDPR Compliance Timeline

| Phase | Duration | Activities |
|---|---|---|
| Data mapping | 3–6 weeks | Map all personal data flows: collect, store, process, share, delete |
| Legal basis review | 2–4 weeks | Assign legal basis to each processing activity |
| Policy updates | 4–6 weeks | Privacy policy, cookie policy, employee data notices |
| DPA execution | 2–4 weeks | Execute DPAs with all processors (SaaS vendors, cloud providers) |
| Technical controls | 4–12 weeks | Consent management, data subject rights automation, retention |
| Staff training | 2–4 weeks | GDPR awareness for all staff |
| **Total** | **3–6 months** | — |

### GDPR Fines
- **Standard violations:** Up to €10M or 2% of global annual revenue
- **Major violations** (basic principles, consent, data subject rights): Up to €20M or 4% of global annual revenue
- **Highest ever fine:** Meta, €1.2B (2023, data transfers to US)

---

## 5. Multi-Framework Efficiency

### Control Overlap Analysis

The same underlying controls satisfy multiple frameworks. Build once, certify multiple times.

**Core Control Domain Overlap:**

| Control Domain | SOC 2 | ISO 27001 | HIPAA | GDPR |
|---|---|---|---|---|
| Access control / IAM | CC6 | A.5.15–A.5.18 | §164.312(a) | Art. 32 |
| Encryption at rest/transit | CC6.7 | A.8.24 | §164.312(a)(2)(iv) | Art. 32 |
| Audit logging | CC7.2 | A.8.15, A.8.17 | §164.312(b) | Art. 32 |
| Incident response | CC7.3–CC7.5 | A.5.24–A.5.28 | §164.308(a)(6) | Art. 33–34 |
| Vendor/third-party mgmt | CC9 | A.5.19–A.5.22 | §164.308(b) | Art. 28 |
| Risk assessment | CC3 | Clause 6.1 | §164.308(a)(1) | Art. 32 |
| Security training | CC1.4 | A.6.3, A.6.8 | §164.308(a)(5) | Art. 39 |
| Business continuity | A1 | A.5.29–A.5.30 | §164.308(a)(7) | Art. 32 |
| Data classification | CC6.1 | A.5.9–A.5.13 | §164.514 | Art. 5(1)(c) |
| Change management | CC8 | A.8.32 | §164.312(c) | Art. 25 |

**Efficiency Rule:** If you build SOC 2 controls correctly, you're ~65–75% of the way to ISO 27001 and ~70% of the way to HIPAA. Don't rebuild — extend.

### Recommended Sequencing by Company Profile

**B2B SaaS (US-focused):**
```
Month 0–6:   SOC 2 Type I → unblocks early enterprise deals
Month 6–18:  SOC 2 Type II → enterprise table stakes
Month 18–30: ISO 27001 → EU market expansion
             (GDPR should be woven in from month 0 if any EU data)
```

**HealthTech (US):**
```
Month 0–8:   HIPAA compliance + BAA readiness → enables healthcare customers
Month 6–18:  SOC 2 Type II → enterprise IT requirements on top of HIPAA
Month 18+:   ISO 27001 if entering European market
```

**EU-founded SaaS:**
```
Month 0–3:   GDPR compliance → legal requirement, not optional
Month 3–12:  ISO 27001 → EU enterprise default expectation
Month 12–24: SOC 2 → US market expansion
```

**HealthTech (EU):**
```
Concurrent:  GDPR + ISO 27001 (strong overlap with MDR/IVDR security requirements)
Month 12+:   HIPAA if entering US market
```

### Shared Evidence Model
Build your evidence library once. Tag each piece of evidence by framework:

```
evidence/
├── access_control/
│   ├── iam_policy.pdf          [SOC2:CC6, ISO:A5.15, HIPAA:164.312a]
│   ├── mfa_screenshot_Q1.png   [SOC2:CC6, ISO:A8.5, HIPAA:164.312d]
│   └── access_review_log.xlsx  [SOC2:CC6, ISO:A5.18, HIPAA:164.308a]
├── encryption/
│   ├── kms_config.png          [SOC2:CC6.7, ISO:A8.24, HIPAA:164.312e]
│   └── tls_policy.md           [SOC2:CC6.7, ISO:A8.24, HIPAA:164.312e]
└── incident_response/
    ├── ir_plan.pdf             [SOC2:CC7, ISO:A5.24, HIPAA:164.308a6]
    └── tabletop_log.pdf        [SOC2:CC7, ISO:A5.26, HIPAA:164.308a6]
```

### GRC Platform Comparison

| Platform | Best For | Price/yr | SOC 2 | ISO 27001 | HIPAA | GDPR |
|---|---|---|---|---|---|---|
| Vanta | Fast SOC 2, US startups | $15–30K | ✅ | ✅ | ✅ | ✅ |
| Drata | Automation depth | $18–35K | ✅ | ✅ | ✅ | ✅ |
| Secureframe | Cost-effective | $10–20K | ✅ | ✅ | ✅ | ✅ |
| Sprinto | SMB, global | $12–25K | ✅ | ✅ | ✅ | ✅ |
| Tugboat Logic | Mid-market | $20–40K | ✅ | ✅ | ✅ | ✅ |
| Manual | Budget-constrained | $0 + time | ✅ | ✅ | ✅ | ✅ |

**Recommendation:** For Series A startups, Vanta or Drata pays for itself in reduced auditor fees and internal time savings. Budget $15–25K/year.

### Compliance Maintenance Annual Budget

| Item | SOC 2 | ISO 27001 | HIPAA | GDPR |
|---|---|---|---|---|
| Annual audit / surveillance | $25–60K | $8–20K | n/a (self-assessed) | n/a (self-assessed) |
| GRC platform | $15–30K | Shared | Shared | Shared |
| Annual training | $3–8K | Shared | Shared | Shared |
| Policy review | $2–5K | $2–5K | $2–5K | $2–5K |
| **Total ongoing** | **$45–103K/yr** | **+$10–25K/yr** | **+$5–15K/yr** | **+$5–15K/yr** |
