# SOC 2 Trust Service Criteria Reference

Comprehensive reference for all five AICPA Trust Service Criteria (TSC) categories. Each criterion includes its objective, sub-criteria, typical controls, and evidence examples.

---

## 1. Security (Common Criteria) — Required

The Security category is mandatory for every SOC 2 engagement. It maps to the 17 COSO 2013 internal control principles organized into nine groups (CC1-CC9).

### CC1 — Control Environment

Establishes the foundation for all other components of internal control.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC1.1 | Demonstrate commitment to integrity and ethical values | Code of conduct, ethics hotline, background checks | Signed code of conduct, hotline reports, screening records |
| CC1.2 | Board exercises oversight of internal control | Independent board/committee, regular reporting | Board meeting minutes, committee charters, oversight reports |
| CC1.3 | Management establishes structure and reporting lines | Organizational charts, role definitions, RACI matrices | Org charts, job descriptions, authority matrices |
| CC1.4 | Commitment to attract, develop, and retain competent individuals | Training programs, competency assessments, career development | Training completion records, skills assessments, HR policies |
| CC1.5 | Hold individuals accountable for internal control responsibilities | Performance evaluations, disciplinary procedures | Performance review records, accountability documentation |

### CC2 — Communication and Information

Ensures relevant, quality information flows internally and externally.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC2.1 | Obtain and generate relevant quality information | Data classification, information quality standards | Classification policy, data quality reports |
| CC2.2 | Internally communicate information and responsibilities | Internal newsletters, policy distribution, security awareness | Communication logs, training materials, acknowledgment records |
| CC2.3 | Communicate with external parties | Customer notifications, vendor communications, incident notices | External communication policy, notification records, status pages |

### CC3 — Risk Assessment

Identifies and assesses risks that may prevent achievement of objectives.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC3.1 | Specify objectives to identify and assess risks | Risk management framework, risk appetite statement | Risk methodology document, risk appetite approval |
| CC3.2 | Identify and analyze risks | Risk assessments, threat modeling, vulnerability analysis | Risk register, threat models, assessment reports |
| CC3.3 | Consider potential for fraud | Fraud risk assessment, segregation of duties | Fraud risk report, SoD matrix, anti-fraud controls |
| CC3.4 | Identify and assess changes impacting internal control | Change impact analysis, environmental scanning | Change assessments, business impact analyses |

### CC4 — Monitoring Activities

Ongoing evaluations to verify internal controls are present and functioning.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC4.1 | Select and perform ongoing and separate evaluations | Continuous monitoring, internal audits, control testing | Monitoring dashboards, audit reports, testing results |
| CC4.2 | Evaluate and communicate deficiencies | Deficiency tracking, remediation management, management reporting | Deficiency logs, remediation plans, management reports |

### CC5 — Control Activities

Policies and procedures that ensure management directives are carried out.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC5.1 | Select and develop control activities that mitigate risks | Risk-based control selection, control design documentation | Control matrix, risk treatment plans |
| CC5.2 | Select and develop technology controls | IT general controls, automated controls, technology governance | ITGC documentation, technology policies, automated control configs |
| CC5.3 | Deploy control activities through policies and procedures | Policy library, procedure documentation, acknowledgment tracking | Policy repository, version history, signed acknowledgments |

### CC6 — Logical and Physical Access Controls

Restrict logical and physical access to information assets.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC6.1 | Logical access security over protected assets | IAM platform, SSO, MFA enforcement | IAM configuration, SSO settings, MFA enrollment reports |
| CC6.2 | Access provisioning based on role and need | Role-based access, provisioning workflows, approval chains | Provisioning tickets, role matrix, approval records |
| CC6.3 | Access removal on termination or role change | Offboarding checklists, automated deprovisioning | Deprovisioning tickets, termination checklists, access removal logs |
| CC6.4 | Periodic access reviews | Quarterly user access reviews, entitlement validation | Access review reports, entitlement listings, sign-off records |
| CC6.5 | Physical access restrictions | Badge systems, visitor management, secure areas | Badge access logs, visitor logs, physical access policies |
| CC6.6 | Encryption of data in transit and at rest | TLS enforcement, disk encryption, key management | TLS configuration, encryption settings, key rotation records |
| CC6.7 | Data transmission and movement restrictions | DLP tools, network segmentation, firewall rules | DLP configuration, network diagrams, firewall rule sets |
| CC6.8 | Prevention/detection of unauthorized software | Endpoint protection, application whitelisting, malware scanning | EDR configuration, whitelist policies, scan reports |

### CC7 — System Operations

Detect and mitigate security events and anomalies.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC7.1 | Vulnerability identification and management | Vulnerability scanning, patch management, remediation SLAs | Scan reports, patch records, SLA compliance metrics |
| CC7.2 | Monitor for anomalies and security events | SIEM, IDS/IPS, behavioral analytics | SIEM dashboards, alert rules, detection logs |
| CC7.3 | Security event evaluation and classification | Incident classification criteria, triage procedures | Classification matrix, triage logs, escalation records |
| CC7.4 | Incident response execution | Incident response plan, response team, communication procedures | IR plan, incident tickets, communication records |
| CC7.5 | Incident recovery and lessons learned | Recovery procedures, post-incident reviews, plan updates | Recovery records, postmortem reports, plan revision history |

### CC8 — Change Management

Authorize, design, develop, test, and implement changes to infrastructure and software.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC8.1 | Change authorization, testing, and approval | Change management process, approval workflows, testing requirements | Change tickets, approval records, test results, deployment logs |

### CC9 — Risk Mitigation

Manage risks associated with business disruption, vendors, and partners.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| CC9.1 | Vendor and business partner risk management | Vendor assessment program, third-party risk management | Vendor risk assessments, vendor register, vendor SOC reports |
| CC9.2 | Risk mitigation through transfer mechanisms | Cyber insurance, contractual protections | Insurance certificates, contract provisions |

---

## 2. Availability (A1) — Optional

Addresses system uptime, performance, and recoverability commitments.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| A1.1 | Capacity and performance management | Auto-scaling, resource monitoring, capacity planning | Capacity dashboards, scaling policies, resource utilization trends |
| A1.2 | Recovery operations | Backup procedures, DR planning, BCP documentation | Backup logs, DR plan, BCP documentation, recovery procedures |
| A1.3 | Recovery testing | DR drills, failover tests, RTO/RPO validation | DR test reports, failover results, RTO/RPO measurements |

### When to Include Availability

- Your customers depend on your service uptime
- You have SLAs with financial penalties for downtime
- Your service is in the critical path of customer operations
- You provide infrastructure or platform services

### Key Metrics

| Metric | Description | Typical Target |
|--------|-------------|----------------|
| RTO | Recovery Time Objective — max acceptable downtime | 1-4 hours |
| RPO | Recovery Point Objective — max acceptable data loss | 1-24 hours |
| SLA | Service Level Agreement — uptime commitment | 99.9%-99.99% |
| MTTR | Mean Time to Recovery — average recovery duration | < 1 hour |

---

## 3. Confidentiality (C1) — Optional

Protects information designated as confidential throughout its lifecycle.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| C1.1 | Identification of confidential information | Data classification scheme, confidential data inventory | Classification policy, data inventory, labeling standards |
| C1.2 | Protection of confidential information | Encryption, access restrictions, DLP, secure transmission | Encryption configs, ACLs, DLP rules, secure transfer logs |
| C1.3 | Disposal of confidential information | Secure deletion, media sanitization, retention enforcement | Disposal procedures, sanitization certificates, deletion logs |

### When to Include Confidentiality

- You handle trade secrets or proprietary business information
- Contracts require confidentiality assurance
- You process data classified above "public" in your classification scheme
- Customers share confidential data for processing

### Data Classification Levels

| Level | Description | Handling Requirements |
|-------|-------------|----------------------|
| Public | No restrictions | No special controls |
| Internal | Business use only | Access controls, basic encryption |
| Confidential | Restricted access | Strong encryption, DLP, access reviews |
| Highly Confidential | Strictly controlled | Strongest encryption, MFA, audit logging, need-to-know |

---

## 4. Processing Integrity (PI1) — Optional

Ensures system processing is complete, valid, accurate, timely, and authorized.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| PI1.1 | Processing accuracy | Input validation, data integrity checks, output verification | Validation rules, integrity check logs, reconciliation reports |
| PI1.2 | Processing completeness | Transaction monitoring, completeness checks, reconciliation | Transaction logs, batch processing reports, reconciliation records |
| PI1.3 | Processing timeliness | SLA monitoring, batch job scheduling, processing alerts | SLA reports, job schedules, processing time metrics |
| PI1.4 | Processing authorization | Authorization controls, segregation of duties, approval workflows | Authorization matrix, SoD analysis, approval records |

### When to Include Processing Integrity

- You perform financial calculations or transactions
- Data accuracy is critical to customer operations
- You provide analytics or reporting that drives business decisions
- Regulatory requirements demand processing accuracy (e.g., healthcare, finance)

### Validation Checkpoints

| Stage | Validation | Method |
|-------|-----------|--------|
| Input | Data format, range, completeness | Automated validation rules |
| Processing | Calculation accuracy, transformation correctness | Unit tests, reconciliation |
| Output | Report accuracy, data completeness | Cross-checks, manual review, checksums |
| Transfer | Transmission integrity, completeness | Hash verification, acknowledgment protocols |

---

## 5. Privacy (P1-P8) — Optional

Governs the collection, use, retention, disclosure, and disposal of personal information. Closely aligns with GDPR, CCPA, and other privacy regulations.

| Criterion | Objective | Typical Controls | Evidence |
|-----------|-----------|-----------------|----------|
| P1.1 | Notice — inform data subjects about data practices | Privacy policy, collection notices, purpose statements | Published privacy policy, collection banners, purpose documentation |
| P2.1 | Choice and consent — provide opt-in/opt-out mechanisms | Consent management, preference centers, granular consent | Consent records, preference logs, opt-out mechanisms |
| P3.1 | Collection — collect only necessary personal information | Data minimization, lawful basis documentation, purpose specification | Collection audits, lawful basis records, data flow diagrams |
| P4.1 | Use, retention, and disposal — limit use and enforce retention | Purpose limitation, retention schedules, automated deletion | Use restriction controls, retention policies, deletion logs |
| P4.2 | Disposal — secure disposal when no longer needed | Secure deletion, media sanitization | Disposal certificates, sanitization records |
| P5.1 | Access — provide data subjects access to their data | DSAR processing, data portability, access portals | DSAR logs, response timelines, export capabilities |
| P5.2 | Correction — allow data subjects to correct their data | Correction request processing, data update mechanisms | Correction logs, update records |
| P6.1 | Disclosure — control third-party data sharing | Data sharing agreements, third-party inventory, DPAs | DPAs, sharing agreements, third-party register |
| P6.2 | Notification — notify of breaches affecting personal data | Breach notification procedures, regulatory reporting | Breach response plan, notification records, reporting logs |
| P7.1 | Quality — maintain accurate personal information | Data quality checks, accuracy verification, correction mechanisms | Quality reports, accuracy audits, correction records |
| P8.1 | Monitoring — monitor privacy program effectiveness | Privacy audits, compliance reviews, complaint tracking | Audit reports, compliance dashboards, complaint logs |

### When to Include Privacy

- You process personal information (PII) of end users or customers
- You operate in jurisdictions with privacy regulations (GDPR, CCPA, LGPD)
- Customers request privacy assurance as part of vendor assessment
- Your service involves health, financial, or other sensitive personal data

### Privacy Criteria Overlap with GDPR

| SOC 2 Privacy | GDPR Article | Alignment |
|---------------|-------------|-----------|
| P1 (Notice) | Art. 13-14 | Direct — transparency requirements |
| P2 (Consent) | Art. 6-7 | Direct — lawful basis and consent |
| P3 (Collection) | Art. 5(1)(b-c) | Direct — purpose limitation, minimization |
| P4 (Retention) | Art. 5(1)(e) | Direct — storage limitation |
| P5 (Access) | Art. 15-16 | Direct — data subject rights |
| P6 (Disclosure) | Art. 33-34 | Direct — breach notification |
| P7 (Quality) | Art. 5(1)(d) | Direct — accuracy principle |
| P8 (Monitoring) | Art. 5(2) | Direct — accountability principle |

---

## TSC Selection Guide

| Question | If Yes, Include |
|----------|----------------|
| Do you store/process customer data? | Security (required) |
| Do customers depend on your uptime? | Availability |
| Do you handle confidential business data? | Confidentiality |
| Is data accuracy critical to your service? | Processing Integrity |
| Do you process personal information? | Privacy |

### Common Combinations

| Company Type | Typical TSC Selection |
|-------------|----------------------|
| SaaS platform | Security + Availability |
| Data analytics | Security + Processing Integrity + Confidentiality |
| Healthcare SaaS | Security + Availability + Privacy + Confidentiality |
| Financial services | Security + Availability + Processing Integrity + Confidentiality |
| Infrastructure/PaaS | Security + Availability |
| HR/Payroll SaaS | Security + Availability + Privacy |

---

## Mapping to Other Frameworks

| SOC 2 Criteria | ISO 27001 | NIST CSF | HIPAA | PCI DSS |
|---------------|-----------|----------|-------|---------|
| CC1 (Control Environment) | A.5 (Policies) | ID.GV | Administrative Safeguards | Req 12 |
| CC2 (Communication) | A.5.1 (Policies) | ID.GV | Administrative Safeguards | Req 12 |
| CC3 (Risk Assessment) | A.8.2 (Risk) | ID.RA | Risk Analysis | Req 12.2 |
| CC4 (Monitoring) | A.8.34 (Monitoring) | DE.CM | Audit Controls | Req 10 |
| CC5 (Control Activities) | A.5-A.8 | PR | All Safeguards | Multiple |
| CC6 (Logical/Physical Access) | A.5.15, A.7 | PR.AC | Access Controls | Req 7-9 |
| CC7 (System Operations) | A.8.8, A.8.15 | DE, RS | Technical Safeguards | Req 5-6, 11 |
| CC8 (Change Management) | A.8.32 | PR.IP | Change Management | Req 6.4 |
| CC9 (Risk Mitigation) | A.5.19-5.22 | ID.SC | Business Associate Agreements | Req 12.8 |
| A1 (Availability) | A.8.13-14 | PR.IP | Contingency Plan | Req 12.10 |
| C1 (Confidentiality) | A.5.13-14, A.8.10-12 | PR.DS | Access Controls | Req 3-4 |
| PI1 (Processing Integrity) | A.8.24-25 | PR.DS | Integrity Controls | Req 6.5 |
| P1-P8 (Privacy) | A.5.34 (Privacy) | PR.PT | Privacy Rule | N/A |
