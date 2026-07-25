# GDPR Compliance Guide

Practical implementation guidance for EU General Data Protection Regulation compliance.

---

## Table of Contents

- [Legal Bases for Processing](#legal-bases-for-processing)
- [Data Subject Rights](#data-subject-rights)
- [Accountability Requirements](#accountability-requirements)
- [International Transfers](#international-transfers)
- [Breach Notification](#breach-notification)

---

## Legal Bases for Processing

### Article 6 - Lawfulness of Processing

Processing is lawful only if at least one basis applies:

| Legal Basis | Article | When to Use |
|-------------|---------|-------------|
| Consent | 6(1)(a) | Marketing, newsletters, cookies (non-essential) |
| Contract | 6(1)(b) | Fulfilling customer orders, employment contracts |
| Legal Obligation | 6(1)(c) | Tax records, employment law requirements |
| Vital Interests | 6(1)(d) | Medical emergencies (rarely used) |
| Public Interest | 6(1)(e) | Government functions, public health |
| Legitimate Interests | 6(1)(f) | Fraud prevention, network security, direct marketing (B2B) |

### Consent Requirements (Art. 7)

Valid consent must be:
- **Freely given**: No imbalance of power, no bundling
- **Specific**: Separate consent for different purposes
- **Informed**: Clear information about processing
- **Unambiguous**: Clear affirmative action
- **Withdrawable**: Easy to withdraw as to give

**Consent Checklist:**
- [ ] Consent request is clear and plain language
- [ ] Separate from other terms and conditions
- [ ] Granular options for different processing purposes
- [ ] No pre-ticked boxes
- [ ] Record of when and how consent was given
- [ ] Easy withdrawal mechanism documented
- [ ] Consent refreshed periodically

### Special Category Data (Art. 9)

Additional safeguards required for:
- Racial or ethnic origin
- Political opinions
- Religious or philosophical beliefs
- Trade union membership
- Genetic data
- Biometric data (for identification)
- Health data
- Sex life or sexual orientation

**Processing Exceptions (Art. 9(2)):**
1. Explicit consent
2. Employment/social security obligations
3. Vital interests (subject incapable of consent)
4. Legitimate activities of associations
5. Data made public by subject
6. Legal claims
7. Substantial public interest
8. Healthcare purposes
9. Public health
10. Archiving/research/statistics

---

## Data Subject Rights

### Right of Access (Art. 15)

**What to provide:**
1. Confirmation of processing (yes/no)
2. Copy of personal data
3. Supplementary information:
   - Purposes of processing
   - Categories of data
   - Recipients or categories
   - Retention period or criteria
   - Rights information
   - Source of data
   - Automated decision-making details

**Process:**
1. Receive request (any form acceptable)
2. Verify identity (proportionate measures)
3. Gather data from all systems
4. Provide response within one month (Art. 12(3); extendable by two further months for complex requests)
5. First copy free; reasonable fee for additional

### Right to Rectification (Art. 16)

**When applicable:**
- Data is inaccurate
- Data is incomplete

**Process:**
1. Verify claimed inaccuracy
2. Correct data in all systems
3. Notify third parties of correction
4. Respond within one month (Art. 12(3))

### Right to Erasure (Art. 17)

**Grounds for erasure:**
- Data no longer necessary for original purpose
- Consent withdrawn
- Objection to processing (no overriding grounds)
- Unlawful processing
- Legal obligation to erase
- Data collected from child for online services

**Exceptions (erasure NOT required):**
- Freedom of expression
- Legal obligation to retain
- Public health reasons
- Archiving in public interest
- Establishment/exercise/defense of legal claims

### Right to Restriction (Art. 18)

**Applicable when:**
- Accuracy contested (during verification)
- Processing unlawful but erasure opposed
- Controller no longer needs data but subject needs for legal claims
- Objection pending verification of legitimate grounds

**Effect:** Data can only be stored; other processing requires consent

### Right to Data Portability (Art. 20)

**Requirements:**
- Processing based on consent or contract
- Processing by automated means

**Format:** Structured, commonly used, machine-readable (JSON, CSV, XML)

**Scope:** Data provided by subject (not inferred or derived data)

### Right to Object (Art. 21)

**Processing based on legitimate interests/public interest:**
- Subject can object at any time
- Controller must demonstrate compelling legitimate grounds

**Direct marketing:**
- Absolute right to object
- Processing must stop immediately
- Must inform subject of right at first communication

### Automated Decision-Making (Art. 22)

**Right not to be subject to decisions:**
- Based solely on automated processing
- Producing legal or similarly significant effects

**Exceptions:**
- Necessary for contract
- Authorized by law
- Based on explicit consent

**Safeguards required:**
- Right to human intervention
- Right to express point of view
- Right to contest decision

---

## Accountability Requirements

### Records of Processing Activities (Art. 30)

**Controller must record:**
- Controller name and contact
- Purposes of processing
- Categories of data subjects
- Categories of personal data
- Categories of recipients
- Third country transfers and safeguards
- Retention periods
- Technical and organizational measures

**Processor must record:**
- Processor name and contact
- Categories of processing
- Third country transfers
- Technical and organizational measures

### Data Protection by Design and Default (Art. 25)

**By Design principles:**
- Data minimization
- Pseudonymization
- Purpose limitation built into systems
- Security measures from inception

**By Default requirements:**
- Only necessary data processed
- Limited collection scope
- Limited storage period
- Limited accessibility

### Data Protection Impact Assessment (Art. 35)

**Required when:**
- Systematic and extensive profiling with significant effects
- Large-scale processing of special categories
- Systematic monitoring of public areas
- Two or more high-risk criteria from WP29 guidelines

**DPIA must contain:**
1. Systematic description of processing
2. Assessment of necessity and proportionality
3. Assessment of risks to rights and freedoms
4. Measures to address risks

### Data Processing Agreements (Art. 28)

**Required clauses:**
- Process only on documented instructions
- Confidentiality obligations
- Security measures
- Sub-processor requirements
- Assistance with subject rights
- Assistance with security obligations
- Return or delete data at end
- Audit rights

---

## International Transfers

### Adequacy Decisions (Art. 45)

Current adequate countries/territories:
- Andorra, Argentina, Canada (commercial), Faroe Islands
- Guernsey, Israel, Isle of Man, Japan, Jersey
- New Zealand, Republic of Korea, Switzerland
- UK, Uruguay
- EU-US Data Privacy Framework (participating companies)

### Standard Contractual Clauses (Art. 46)

**New SCCs (2021) modules:**
- Module 1: Controller to Controller
- Module 2: Controller to Processor
- Module 3: Processor to Processor
- Module 4: Processor to Controller

**Implementation requirements:**
1. Complete relevant modules
2. Conduct Transfer Impact Assessment
3. Implement supplementary measures if needed
4. Document assessment

### Transfer Impact Assessment

**Assess:**
1. Circumstances of transfer
2. Third country legal framework
3. Contractual and technical safeguards
4. Whether safeguards are effective
5. Supplementary measures needed

---

## Breach Notification

### Supervisory Authority Notification (Art. 33)

**Timeline:** Within 72 hours of becoming aware

**Required unless:** Unlikely to result in risk to rights and freedoms

**Notification must include:**
- Nature of breach
- Categories and approximate numbers affected
- DPO contact details
- Likely consequences
- Measures taken or proposed

### Data Subject Notification (Art. 34)

**Required when:** High risk to rights and freedoms

**Not required if:**
- Appropriate technical measures in place (encryption)
- Subsequent measures eliminate high risk
- Disproportionate effort (public communication instead)

### Breach Documentation

**Document ALL breaches:**
- Facts of breach
- Effects
- Remedial action
- Justification for any non-notification

---

## Compliance Checklist

### Governance
- [ ] DPO appointed (if required)
- [ ] Data protection policies in place
- [ ] Staff training conducted
- [ ] Privacy by design implemented

### Documentation
- [ ] Records of processing activities
- [ ] Privacy notices updated
- [ ] Consent records maintained
- [ ] DPIAs conducted where required
- [ ] Processor agreements in place

### Technical Measures
- [ ] Encryption at rest and in transit
- [ ] Access controls implemented
- [ ] Audit logging enabled
- [ ] Data minimization applied
- [ ] Retention schedules automated

### Subject Rights
- [ ] Access request process
- [ ] Erasure capability
- [ ] Portability capability
- [ ] Objection handling process
- [ ] Response within deadlines
