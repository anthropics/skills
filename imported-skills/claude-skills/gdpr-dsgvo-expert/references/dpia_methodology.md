# DPIA Methodology

Data Protection Impact Assessment process, criteria, and checklists following GDPR Article 35 and WP29 guidelines.

---

## Table of Contents

- [When DPIA is Required](#when-dpia-is-required)
- [DPIA Process](#dpia-process)
- [Risk Assessment](#risk-assessment)
- [Consultation Requirements](#consultation-requirements)
- [Templates and Checklists](#templates-and-checklists)

---

## When DPIA is Required

### Mandatory DPIA Triggers (Art. 35(3))

A DPIA is always required for:

1. **Systematic and extensive evaluation** of personal aspects (profiling) with legal/significant effects

2. **Large-scale processing** of special category data (Art. 9) or criminal conviction data (Art. 10)

3. **Systematic monitoring** of publicly accessible areas on a large scale

### WP29 High-Risk Criteria

DPIA likely required if processing involves **two or more** criteria:

| # | Criterion | Examples |
|---|-----------|----------|
| 1 | Evaluation or scoring | Credit scoring, behavioral profiling |
| 2 | Automated decision-making with legal effects | Auto-reject job applications |
| 3 | Systematic monitoring | Employee monitoring, CCTV |
| 4 | Sensitive data | Health, biometric, religion |
| 5 | Large scale | City-wide surveillance, national database |
| 6 | Data matching/combining | Cross-referencing datasets |
| 7 | Vulnerable subjects | Children, patients, employees |
| 8 | Innovative technology | AI, IoT, biometrics |
| 9 | Data transfer outside EU | Cloud services in third countries |
| 10 | Blocking access to service | Credit blacklisting |

### DPIA Not Required When

- Processing unlikely to result in high risk
- Similar processing already assessed
- Legal basis in EU/Member State law with DPIA done during legislative process
- Processing on supervisory authority's exemption list

### Threshold Assessment Workflow

```
1. Is processing on supervisory authority's mandatory list?
   → YES: DPIA required
   → NO: Continue

2. Is processing covered by Art. 35(3) mandatory categories?
   → YES: DPIA required
   → NO: Continue

3. Does processing meet 2+ WP29 criteria?
   → YES: DPIA required
   → NO: Continue

4. Could processing result in high risk to individuals?
   → YES: DPIA recommended
   → NO: Document reasoning, no DPIA needed
```

---

## DPIA Process

### Phase 1: Preparation

**Step 1.1: Identify Need**
- Complete threshold assessment
- Document decision rationale
- If DPIA needed, proceed

**Step 1.2: Assemble Team**
- Project/product owner
- IT/security representative
- Legal/compliance
- DPO consultation
- Subject matter experts as needed

**Step 1.3: Gather Information**
- Data flow diagrams
- Technical specifications
- Processing purposes
- Legal basis documentation

### Phase 2: Description of Processing

**Step 2.1: Document Scope**

| Element | Description |
|---------|-------------|
| Nature | How data is collected, used, stored, deleted |
| Scope | Categories of data, volume, frequency |
| Context | Relationship with subjects, expectations |
| Purposes | What processing achieves, why necessary |

**Step 2.2: Map Data Flows**

Document:
- Data sources (from subject, third parties, public)
- Collection methods (forms, APIs, automatic)
- Storage locations (databases, cloud, backups)
- Processing operations (analysis, sharing, profiling)
- Recipients (internal teams, processors, third parties)
- Retention and deletion

**Step 2.3: Identify Legal Basis**

For each processing purpose:
- Primary legal basis (Art. 6)
- Special category basis if applicable (Art. 9)
- Documentation of legitimate interests balance (if Art. 6(1)(f))

### Phase 3: Necessity and Proportionality

**Step 3.1: Necessity Assessment**

Questions to answer:
- Is this processing necessary for the stated purpose?
- Could the purpose be achieved with less data?
- Could the purpose be achieved without this processing?
- Are there less intrusive alternatives?

**Step 3.2: Proportionality Assessment**

Evaluate:
- Data minimization compliance
- Purpose limitation compliance
- Storage limitation compliance
- Balance between controller needs and subject rights

**Step 3.3: Data Protection Principles Compliance**

| Principle | Assessment Question |
|-----------|---------------------|
| Lawfulness | Is there a valid legal basis? |
| Fairness | Would subjects expect this processing? |
| Transparency | Are subjects properly informed? |
| Purpose limitation | Is processing limited to stated purposes? |
| Data minimization | Is only necessary data processed? |
| Accuracy | Are there mechanisms for keeping data accurate? |
| Storage limitation | Are retention periods defined and enforced? |
| Integrity/confidentiality | Are appropriate security measures in place? |
| Accountability | Can compliance be demonstrated? |

### Phase 4: Risk Assessment

**Step 4.1: Identify Risks**

Risk categories to consider:
- Unauthorized access or disclosure
- Unlawful destruction or loss
- Unlawful modification
- Denial of service to subjects
- Discrimination or unfair decisions
- Financial loss to subjects
- Reputational damage to subjects
- Physical harm
- Psychological harm

**Step 4.2: Assess Likelihood and Severity**

| Level | Likelihood | Severity |
|-------|------------|----------|
| Low | Unlikely to occur | Minimal impact, easily remedied |
| Medium | May occur occasionally | Significant inconvenience |
| High | Likely to occur | Serious impact on daily life |
| Very High | Expected to occur | Irreversible or very difficult to overcome |

**Step 4.3: Risk Matrix**

```
                    SEVERITY
                 Low   Med   High  V.High
L    Low        [L]   [L]   [M]   [M]
i    Medium     [L]   [M]   [H]   [H]
k    High       [M]   [H]   [H]   [VH]
e    V.High     [M]   [H]   [VH]  [VH]
```

### Phase 5: Risk Mitigation

**Step 5.1: Identify Measures**

For each identified risk:
- Technical measures (encryption, access controls)
- Organizational measures (policies, training)
- Contractual measures (DPAs, liability clauses)
- Physical measures (building security)

**Step 5.2: Evaluate Residual Risk**

After mitigations:
- Re-assess likelihood
- Re-assess severity
- Determine if residual risk is acceptable

**Step 5.3: Accept or Escalate**

| Residual Risk | Action |
|---------------|--------|
| Low/Medium | Document acceptance, proceed |
| High | Implement additional mitigations or consult DPO |
| Very High | Consult supervisory authority before proceeding |

### Phase 6: Documentation and Review

**Step 6.1: Document DPIA**

Required content:
- Processing description
- Necessity and proportionality assessment
- Risk assessment
- Measures to address risks
- DPO advice
- Data subject views (if obtained)

**Step 6.2: DPO Sign-Off**

DPO should:
- Review DPIA completeness
- Verify risk assessment adequacy
- Confirm mitigation appropriateness
- Document advice given

**Step 6.3: Schedule Review**

Review DPIA when:
- Processing changes significantly
- New risks emerge
- Annually (minimum)
- After incidents

---

## Risk Assessment

### Common Risks by Processing Type

**Profiling and Automated Decisions:**
- Discrimination
- Inaccurate inferences
- Lack of transparency
- Denial of services

**Large Scale Processing:**
- Data breach impact
- Difficulty ensuring accuracy
- Challenge managing subject rights
- Aggregation effects

**Sensitive Data:**
- Social stigma
- Employment discrimination
- Insurance denial
- Relationship damage

**New Technologies:**
- Unknown vulnerabilities
- Lack of proven safeguards
- Regulatory uncertainty
- Subject unfamiliarity

### Mitigation Measure Categories

**Technical Measures:**
- Encryption (at rest, in transit)
- Pseudonymization
- Anonymization where possible
- Access controls (RBAC)
- Audit logging
- Automated retention enforcement
- Data loss prevention

**Organizational Measures:**
- Privacy policies
- Staff training
- Access management procedures
- Incident response procedures
- Vendor management
- Regular audits

**Transparency Measures:**
- Clear privacy notices
- Layered information
- Just-in-time notices
- Easy rights exercise

---

## Consultation Requirements

### DPO Consultation (Art. 35(2))

**When:** During DPIA process

**DPO role:**
- Advise on whether DPIA is needed
- Advise on methodology
- Review assessment
- Monitor implementation

### Data Subject Views (Art. 35(9))

**When:** Where appropriate

**Methods:**
- Surveys
- Focus groups
- Public consultation
- User testing

**Not required if:**
- Disproportionate effort
- Confidential commercial activity
- Would prejudice security

### Supervisory Authority Consultation (Art. 36)

**Required when:**
- Residual risk remains high after mitigations
- Controller cannot sufficiently reduce risk

**Process:**
1. Submit DPIA to authority
2. Include information on controller/processor responsibilities
3. Authority responds within 8 weeks (extendable to 14)
4. Authority may prohibit processing or require changes

---

## Templates and Checklists

### DPIA Screening Checklist

**Project Information:**
- [ ] Project name documented
- [ ] Processing purposes defined
- [ ] Data categories identified
- [ ] Data subjects identified

**Threshold Assessment:**
- [ ] Checked against mandatory list
- [ ] Checked against Art. 35(3) criteria
- [ ] Counted WP29 criteria (need 2+)
- [ ] Decision documented with rationale

### DPIA Content Checklist

**Section 1: Processing Description**
- [ ] Nature of processing described
- [ ] Scope defined (data, volume, geography)
- [ ] Context documented
- [ ] All purposes listed
- [ ] Data flows mapped
- [ ] Recipients identified
- [ ] Retention periods specified

**Section 2: Legal Basis**
- [ ] Legal basis identified for each purpose
- [ ] Special category basis documented (if applicable)
- [ ] Legitimate interests balance documented (if applicable)
- [ ] Consent mechanism described (if applicable)

**Section 3: Necessity and Proportionality**
- [ ] Necessity justified for each processing operation
- [ ] Alternatives considered and documented
- [ ] Data minimization demonstrated
- [ ] Proportionality assessment completed

**Section 4: Risks**
- [ ] All risk categories considered
- [ ] Likelihood assessed for each risk
- [ ] Severity assessed for each risk
- [ ] Overall risk level determined

**Section 5: Mitigations**
- [ ] Technical measures identified
- [ ] Organizational measures identified
- [ ] Residual risk assessed
- [ ] Acceptance or escalation determined

**Section 6: Consultation**
- [ ] DPO consulted
- [ ] DPO advice documented
- [ ] Data subject views considered (where appropriate)
- [ ] Supervisory authority consulted (if required)

**Section 7: Sign-Off**
- [ ] Project owner approval
- [ ] DPO sign-off
- [ ] Review date scheduled

### Post-DPIA Actions

- [ ] Implement identified mitigations
- [ ] Update privacy notices if needed
- [ ] Update records of processing
- [ ] Schedule review date
- [ ] Monitor effectiveness of measures
- [ ] Document any changes to processing
