# SFC: SEAL Framework Checklist

SFC DNS Registrar certification: domain management, registrar access controls, DNSSEC configurations, email authentication (SPF/DKIM/DMARC), monitoring, and incident response.

**Controls and baselines for self-assessment and certification.**

## dns-1: Governance & Domain Management

### dns-1.1.1 — Domain Security Owner
**Q:** Is there a clearly designated person or team accountable for domain security?

**Baselines:**
- Accountability scope covers policy maintenance, security reviews, renewal management, access control oversight, and incident escalation

### dns-1.1.2 — Domain Inventory and Documentation
**Q:** Do you maintain a complete, current record of all your domains and their configurations?

**Baselines:**
- Registry includes domain name, ownership, purpose, expiration date, registrar, DNS record configurations, security settings (DNSSEC, CAA), and registrar account configurations
- Accessible to relevant team members

## dns-2: Risk Assessment & Classification

### dns-2.1.1 — Domain Classification and Compliance
**Q:** Do you classify your domains by risk level and verify they meet the security requirements for their classification?

**Baselines:**
- Classification considers criticality, financial exposure, and operational impact
- Domains where users may transact funds or that are external-facing classified at the highest tier
- Each classification maps to specific security requirements (DNSSEC, locks, monitoring frequency, access controls)
- Compliance verified at least annually through configuration review against documented standards

### dns-2.1.2 — Enterprise Registrar Security Requirements
**Q:** Do you use a registrar with enterprise-grade security for your critical domains?

**Baselines:**
- Registrar supports registry locks (server-level EPP locks)
- Registrar supports hardware security key MFA (FIDO2/WebAuthn)
- Registrar has no history of social engineering vulnerabilities
- Due diligence includes checking ICANN compliance notices for the registrar

## dns-3: Access Control & Authentication

### dns-3.1.1 — Registrar Access Control
**Q:** Do you control and secure access to domain registrar and DNS management accounts?

**Baselines:**
- Documented who is authorized, how access is granted/revoked, and role-based permissions where available
- Hardware security key MFA (FIDO2/WebAuthn) required for all registrar and DNS management accounts
- Access reviews conducted at least annually
- Access revoked promptly when no longer needed

### dns-3.1.2 — Dedicated Domain Security Contact Email
**Q:** Is your domain security contact email independent of the domains it protects?

**Baselines:**
- Hosted on a different domain than any domain it's responsible for
- Not a personal email address
- Used exclusively for domain security purposes
- Alias that notifies multiple people

### dns-3.1.3 — Change Management for Domain Operations
**Q:** Do you have change management procedures for critical domain operations?

**Baselines:**
- Covers transfers, deletions, nameserver changes, and DNS record modifications
- Relevant team members notified before critical changes
- All changes logged
- Critical changes verified through out-of-band confirmation with the registrar

## dns-4: Technical Security Controls

### dns-4.1.1 — DNS Security Standards
**Q:** Do you enforce DNS security standards across all your domains?

**Baselines:**
- DNSSEC enabled and validated on all critical domains
- CAA records configured to restrict certificate issuance to authorized CAs only
- TTL policies documented with rationale
- Standards applied consistently based on domain classification

### dns-4.1.2 — Email Authentication Standards
**Q:** Do you enforce email authentication standards and monitor for violations?

**Baselines:**
- SPF, DKIM, and DMARC configured for all domains that send email
- DMARC policy set to reject for domains actively sending email
- DMARC aggregate reports (rua) monitored and reviewed
- MTA-STS configured where supported to enforce encrypted email transport
- Domains that don't send email have SPF/DMARC records that reject all email

### dns-4.1.3 — Domain Lock Implementation
**Q:** Do you use domain locks to prevent unauthorized transfers and changes?

**Baselines:**
- Registry locks (server-level EPP locks) enabled for all critical domains where supported
- Transfer locks enabled on all domains
- Lock status verified periodically

### dns-4.1.4 — TLS Certificate Lifecycle Management
**Q:** Do you manage the full lifecycle of your TLS certificates?

**Baselines:**
- Covers issuance, renewal, and revocation procedures
- Certificates tracked with expiration alerts
- Automated renewal where possible
- Revocation procedures documented for compromised certificates

## dns-5: Monitoring & Detection

### dns-5.1.1 — Domain and DNS Monitoring
**Q:** Do you monitor your domains for unauthorized changes to DNS records, registration status, and security settings?

**Baselines:**
- DNS record monitoring covers nameserver (NS) changes, A/AAAA changes, MX changes, TXT/SPF/DMARC changes, CAA record removal, DNSSEC status changes, and unexpected TTL drops
- Registration monitoring covers lock status, registrar account settings, and nameserver delegation
- Alerting and escalation paths documented
- Critical alerts (nameserver changes, DNSSEC failure, registrar changes) trigger immediate investigation
- Monitoring infrastructure not dependent on the domains being monitored

### dns-5.1.2 — Certificate Transparency Monitoring
**Q:** Do you monitor Certificate Transparency logs for unauthorized certificates issued for your domains?

**Baselines:**
- Subscribed to a CT monitoring service that alerts on new certificate issuance
- Alerts reviewed and unauthorized certificates investigated promptly
- Wildcard certificates flagged if not expected

### dns-5.1.3 — Domain Expiration Prevention
**Q:** Do you actively prevent domain expiration?

**Baselines:**
- Auto-renewal enabled on all domains
- Calendar reminders at 90, 60, 30, and 7 days before expiration
- Payment methods verified current
- Backup person designated for renewal responsibility

## dns-6: Incident Response

### dns-6.1.1 — Alerting and Emergency Contacts
**Q:** Do you have alerting and emergency contacts in place for domain security incidents?

**Baselines:**
- Alerting system in place to notify relevant stakeholders when a potential compromise is detected
- Emergency contacts pre-documented including registrar security team, SEAL 911, and legal counsel
- Communication plan for warning users (status page, social media, in-app warnings)

### dns-6.1.2 — Domain Incident Response Plan
**Q:** Do you have an incident response plan for domain hijacking and DNS compromise?

**Baselines:**
- Covers key scenarios including registrar account compromise, DNS hijacking, and unauthorized transfers
- Emergency registry lock activation procedures
- Procedures for regaining control of compromised domains
- Post-recovery validation including DNS records verified against known-good baseline, all credentials reset, and access logs reviewed
- Plan tested at least annually (can be combined with broader IR drills)
