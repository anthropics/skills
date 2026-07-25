# Regulatory Notification Deadlines

Reference table for incident notification deadlines under major regulatory frameworks. The notification clock starts at the moment an incident is declared, not at investigation completion.

**Operational rule:** If the scope of a breach is unclear at declaration time, assume the most restrictive applicable deadline and confirm scope within the first response window. Document the assumption and its resolution in the incident record.

---

## Deadline Summary Table

| Framework | Jurisdiction | Incident Type | Notification Deadline | Recipient | Penalty for Non-Compliance |
|-----------|-------------|--------------|----------------------|-----------|---------------------------|
| GDPR (EU 2016/679) | EU/EEA | Personal data breach | 72 hours after discovery | Supervisory Authority (DPA) | Up to 4% of global annual turnover or €20M |
| GDPR (EU 2016/679) | EU/EEA | Personal data breach affecting individual rights/freedoms | Without undue delay | Affected data subjects | Up to 4% of global annual turnover |
| PCI-DSS v4.0 | Global (card brands) | Cardholder data breach | 24 hours after confirmation | Acquiring bank and card brands | Fines per card brand schedule; potential card processing suspension |
| HIPAA (45 CFR §164.408) | United States | PHI breach (>500 individuals) | 60 calendar days after discovery | HHS Office for Civil Rights | $100–$50,000 per violation; up to $1.9M per violation category per year |
| HIPAA (45 CFR §164.406) | United States | PHI breach (>500 individuals in a state) | 60 days after discovery | Prominent media outlets in affected state | Same as above |
| HIPAA Small Breach | United States | PHI breach (<500 individuals) | Within 60 days of end of calendar year in which breach occurred | HHS (annual report) | Same as above |
| NY DFS 23 NYCRR 500.17 | New York State | Cybersecurity event affecting NY-regulated entity | 72 hours | NY DFS Superintendent | Regulatory sanctions, fines, license revocation |
| SEC Cybersecurity Rule (17 CFR §229.106) | United States (public companies) | Material cybersecurity incident | 4 business days after materiality determination | SEC Form 8-K filing (public disclosure) | SEC enforcement action; restatement risk |
| CCPA / CPRA | California, United States | Breach of sensitive personal information | Without unreasonable delay | CA Attorney General (if >500 CA residents affected) | Civil penalties up to $7,500 per intentional violation |
| NIS2 (EU 2022/2555) | EU/EEA (essential/important entities) | Significant incident | 24-hour early warning; 72-hour full notification | National CSIRT or competent authority | Up to €10M or 2% of global turnover |
| DORA (EU 2022/2554) | EU/EEA (financial sector) | Major ICT-related incident | Initial notification: 4 hours; intermediate: 72 hours; final: 1 month | Financial supervisory authority | National authority sanctions |
| SOX (for material incidents) | United States (public companies) | Financial system compromise creating material weakness | Immediate disclosure required | SEC, audit committee, auditors | Enforcement action; officer certification liability |
| Australia Privacy Act | Australia | Eligible data breach (serious harm likely) | 30 days after awareness | OAIC (Office of the Australian Information Commissioner) | Up to AUD 50M per serious contravention |
| PIPL (China) | China | Personal information breach | Immediately; notify individuals without delay | National Internet Information Office (CAC) | Up to ¥50M or 5% of prior year revenue |

---

## GDPR — Detailed Requirements

### Article 33 — Notification to Supervisory Authority

**When:** Any personal data breach where there is a risk to the rights and freedoms of individuals.

**Exception:** No notification required if the breach is unlikely to result in risk (e.g., the data was encrypted with a key that was not compromised, and the key cannot be recovered).

**What to include:**
1. Nature of the breach, including categories and approximate number of data subjects and records
2. Name and contact details of the Data Protection Officer
3. Likely consequences of the breach
4. Measures taken or proposed to address the breach, including mitigation

**Staggered notification:** If full information is not available within 72 hours, submit what is known and provide additional information in phases. Document why the information is being provided in phases.

### Article 34 — Notification to Data Subjects

**When:** When a breach is likely to result in high risk to the rights and freedoms of individuals.

**How:** In clear, plain language. Direct communication to the affected individuals.

**Exception:** Notification to individuals not required if:
- The personal data was protected by appropriate technical measures (e.g., encryption)
- The controller has taken subsequent measures that ensure high risk no longer materializes
- It would involve disproportionate effort (use public communication instead)

---

## PCI-DSS v4.0 — Detailed Requirements

### Requirement 12.10.5

Report compromises of cardholder data to the applicable payment brands and acquiring bank immediately upon detection of a suspected compromise. Do not wait for internal investigation to complete.

**Immediate actions required upon suspicion:**
1. Contact acquiring bank within 24 hours of suspicion (even if not yet confirmed)
2. Preserve all logs and evidence — do not modify or delete
3. Implement containment without destroying forensic evidence
4. Engage a PCI Forensic Investigator (PFI) from the approved list

**Card brand notification channels:**
- Visa: Visa Fraud Control
- Mastercard: Mastercard Fraud Control
- American Express: AmEx Security
- Discover: Discover Security

---

## HIPAA — Detailed Requirements

### 45 CFR §164.408 — Breach Notification to HHS

**Notification form:** HHS breach notification portal (https://www.hhs.gov/hipaa/for-professionals/breach-notification/)

**Content required:**
- Name of covered entity or business associate
- Nature of PHI involved (type of PHI, not specific records)
- Unauthorized persons who accessed or used the PHI
- Whether PHI was actually acquired or viewed
- Extent to which risk has been mitigated

### Breach Risk Assessment (45 CFR §164.402)

HIPAA provides a risk assessment safe harbor. A breach is presumed unless the covered entity can demonstrate (low probability PHI was compromised) based on:
1. Nature and extent of PHI involved
2. Who accessed the information
3. Whether PHI was actually acquired or viewed
4. Extent to which risk has been mitigated

Document this risk assessment in writing and retain for 6 years.

---

## Notification Clock Management

### Starting the Clock

Document the exact timestamp when the incident was declared in the incident record. This is the official start of all regulatory clocks.

### Parallel Tracking

Incidents often cross multiple frameworks simultaneously. Track all applicable clocks in parallel:

```
Incident declared: 2024-01-15T14:30:00Z

GDPR notification due:     2024-01-18T14:30:00Z  (72 hours)
PCI notification due:      2024-01-16T14:30:00Z  (24 hours)
HIPAA HHS notification:    2024-03-15T14:30:00Z  (60 days)
NY DFS notification:       2024-01-18T14:30:00Z  (72 hours)
```

### Notification Drafting

Prepare draft notifications in parallel with investigation. Do not wait until investigation is complete to begin drafting. All external regulatory communications must be reviewed by Legal and approved by CISO before transmission.
