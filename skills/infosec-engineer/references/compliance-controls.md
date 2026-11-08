# Compliance Framework Control Mapping

Maps common security controls across major compliance frameworks. Use to identify which controls satisfy multiple framework requirements simultaneously.

## Control Mapping Matrix

### Access Control

| Control | SOC 2 | ISO 27001 | HIPAA | PCI DSS | GDPR |
|---|---|---|---|---|---|
| Role-based access control | CC6.1 | A.9.2.3 | 164.312(a)(1) | 7.1 | Art. 32 |
| Least privilege | CC6.3 | A.9.4.1 | 164.312(a)(1) | 7.1.2 | Art. 25 |
| MFA for admin access | CC6.1 | A.9.4.2 | 164.312(d) | 8.3 | Art. 32 |
| Access reviews (quarterly) | CC6.2 | A.9.2.5 | 164.312(a)(1) | 7.1.4 | Art. 32 |
| Unique user IDs | CC6.1 | A.9.2.1 | 164.312(a)(2)(i) | 8.1.1 | Art. 32 |

### Data Protection

| Control | SOC 2 | ISO 27001 | HIPAA | PCI DSS | GDPR |
|---|---|---|---|---|---|
| Encryption at rest | CC6.1 | A.10.1.1 | 164.312(a)(2)(iv) | 3.4 | Art. 32 |
| Encryption in transit (TLS) | CC6.1 | A.10.1.1 | 164.312(e)(1) | 4.1 | Art. 32 |
| Data classification | CC6.5 | A.8.2.1 | 164.312(a)(1) | 9.6.1 | Art. 30 |
| Data retention policy | CC6.5 | A.8.2.3 | 164.530(j) | 3.1 | Art. 5(1)(e) |
| Backup and recovery | A1.2 | A.12.3.1 | 164.308(a)(7)(ii)(A) | 9.5.1 | Art. 32 |

### Logging and Monitoring

| Control | SOC 2 | ISO 27001 | HIPAA | PCI DSS | GDPR |
|---|---|---|---|---|---|
| Audit logging | CC7.2 | A.12.4.1 | 164.312(b) | 10.1 | Art. 30 |
| Log retention (90+ days) | CC7.2 | A.12.4.1 | 164.312(b) | 10.7 | Art. 30 |
| Security monitoring | CC7.2 | A.12.4.1 | 164.312(b) | 10.6 | Art. 32 |
| Alerting on anomalies | CC7.3 | A.16.1.4 | 164.308(a)(6)(ii) | 10.6.1 | Art. 33 |

### Vulnerability Management

| Control | SOC 2 | ISO 27001 | HIPAA | PCI DSS | GDPR |
|---|---|---|---|---|---|
| Vulnerability scanning | CC7.1 | A.12.6.1 | 164.308(a)(1)(ii)(A) | 11.2 | Art. 32 |
| Patch management | CC7.1 | A.12.6.1 | 164.308(a)(1)(ii)(A) | 6.2 | Art. 32 |
| Penetration testing | CC7.1 | A.18.2.3 | 164.308(a)(8) | 11.3 | Art. 32 |
| Code review | CC8.1 | A.14.2.1 | 164.308(a)(1)(ii)(A) | 6.3.2 | Art. 25 |

### Incident Response

| Control | SOC 2 | ISO 27001 | HIPAA | PCI DSS | GDPR |
|---|---|---|---|---|---|
| IR plan documented | CC7.3 | A.16.1.1 | 164.308(a)(6)(i) | 12.10.1 | Art. 33 |
| IR team defined | CC7.4 | A.16.1.1 | 164.308(a)(6)(i) | 12.10.1 | Art. 33 |
| Breach notification | CC7.3 | A.16.1.2 | 164.408 | 12.10.1 | Art. 33/34 |
| Post-incident review | CC7.5 | A.16.1.6 | 164.308(a)(6)(ii) | 12.10.6 | Art. 33 |

### Change Management

| Control | SOC 2 | ISO 27001 | HIPAA | PCI DSS | GDPR |
|---|---|---|---|---|---|
| Change approval process | CC8.1 | A.12.1.2 | 164.308(a)(1)(ii)(A) | 6.4.5 | Art. 25 |
| Testing before deployment | CC8.1 | A.14.2.8 | 164.308(a)(1)(ii)(A) | 6.4.4 | Art. 25 |
| Separation of environments | CC8.1 | A.12.1.4 | 164.308(a)(4)(ii)(A) | 6.4.1 | Art. 32 |

## Framework-Specific Notes

### SOC 2
- Trust Service Criteria (TSC) organized under 5 categories: Security, Availability, Processing Integrity, Confidentiality, Privacy
- Security (Common Criteria, CC) is required; others are optional
- Type I = point-in-time; Type II = over a period (typically 6-12 months)
- Evidence must demonstrate controls are operating effectively over time

### ISO 27001
- Annex A contains 114 controls across 14 domains
- Requires a formal Information Security Management System (ISMS)
- Risk assessment drives control selection (not all controls required)
- Statement of Applicability (SoA) documents which controls apply and why

### HIPAA
- Applies to Covered Entities and Business Associates handling PHI
- Technical, Administrative, and Physical safeguards required
- Business Associate Agreement (BAA) required with all vendors handling PHI
- Breach notification within 60 days of discovery

### PCI DSS
- 12 requirements organized into 6 goals
- Applies to any entity handling cardholder data
- Annual assessment by QSA for Level 1 merchants
- Self-Assessment Questionnaire (SAQ) for smaller merchants
- Quarterly network vulnerability scans by ASV

### GDPR
- Applies to organizations processing EU residents' personal data
- Data Protection Impact Assessment (DPIA) required for high-risk processing
- Breach notification to authority within 72 hours
- Right to erasure, data portability, access, rectification
- Data Protection Officer (DPO) required for certain organizations
