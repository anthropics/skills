# Cloud Security Audit Guide

Assessment framework for cloud service security verification.

---

## Table of Contents

- [Shared Responsibility Model](#shared-responsibility-model)
- [Cloud Provider Assessment](#cloud-provider-assessment)
- [Configuration Security](#configuration-security)
- [Data Protection](#data-protection)
- [Identity and Access Management](#identity-and-access-management)

---

## Shared Responsibility Model

### Responsibility Matrix

| Layer | IaaS | PaaS | SaaS |
|-------|------|------|------|
| Data classification | Customer | Customer | Customer |
| Identity management | Customer | Customer | Shared |
| Application security | Customer | Shared | Provider |
| Network controls | Shared | Provider | Provider |
| Host infrastructure | Provider | Provider | Provider |
| Physical security | Provider | Provider | Provider |

### Audit Focus by Model

**IaaS (AWS EC2, Azure VMs):**
- Virtual network configuration
- OS hardening and patching
- Application deployment security
- Data encryption implementation

**PaaS (Azure App Service, AWS Lambda):**
- Application code security
- Data handling and encryption
- Identity integration
- Logging configuration

**SaaS (Microsoft 365, Salesforce):**
- User access management
- Data classification and handling
- Security configuration settings
- Integration security

---

## Cloud Provider Assessment

### Certification Verification

Check for current certifications:
- [ ] ISO 27001 (Information Security)
- [ ] ISO 27017 (Cloud Security)
- [ ] ISO 27018 (Cloud Privacy)
- [ ] SOC 2 Type II
- [ ] CSA STAR certification

**Verification Steps:**
1. Request current certificates from provider
2. Verify certificate scope includes services used
3. Check certification expiration dates
4. Review SOC 2 report for relevant controls
5. Document any scope exclusions

### Data Residency Compliance

| Requirement | Verification |
|-------------|--------------|
| GDPR (EU data) | Confirm EU region availability |
| Data sovereignty | Verify no cross-border transfer |
| Backup location | Confirm backup region |
| Disaster recovery | Document DR site location |

### Provider Security Documentation

Request and review:
- Shared responsibility documentation
- Security whitepapers
- Incident notification procedures
- SLA for security incidents
- Vulnerability disclosure policy

---

## Configuration Security

### AWS Security Assessment

**Identity and Access (IAM):**
- [ ] Root account has MFA enabled
- [ ] No access keys for root account
- [ ] IAM policies follow least privilege
- [ ] No wildcard (*) permissions on sensitive resources
- [ ] Password policy meets requirements

**Network Configuration (VPC):**
- [ ] Default VPCs removed or secured
- [ ] Security groups follow least privilege
- [ ] No 0.0.0.0/0 ingress on management ports
- [ ] VPC flow logs enabled
- [ ] Network ACLs configured appropriately

**Storage (S3):**
- [ ] No public buckets (unless intended)
- [ ] Bucket policies restrict access
- [ ] Encryption at rest enabled
- [ ] Versioning enabled for critical data
- [ ] Access logging enabled

**Logging (CloudTrail):**
- [ ] CloudTrail enabled in all regions
- [ ] Log file validation enabled
- [ ] Logs encrypted with KMS
- [ ] S3 bucket for logs is secured
- [ ] CloudWatch alarms configured

### Azure Security Assessment

**Identity (Azure AD):**
- [ ] MFA enabled for all users
- [ ] Privileged Identity Management (PIM) configured
- [ ] Conditional Access policies defined
- [ ] Guest access restricted
- [ ] Password protection enabled

**Network (Virtual Networks):**
- [ ] NSG rules follow least privilege
- [ ] No open management ports to internet
- [ ] Network Watcher enabled
- [ ] DDoS protection configured
- [ ] Private endpoints for PaaS services

**Storage:**
- [ ] No anonymous access to blob storage
- [ ] Encryption at rest enabled
- [ ] Shared access signatures time-limited
- [ ] Storage analytics logging enabled
- [ ] Soft delete enabled

**Monitoring:**
- [ ] Azure Monitor enabled
- [ ] Activity log exported to SIEM
- [ ] Alerts configured for security events
- [ ] Azure Security Center enabled
- [ ] Diagnostic settings configured

---

## Data Protection

### Encryption Verification

**At Rest:**
| Service | Encryption Check |
|---------|------------------|
| Block storage | Verify CMK or provider-managed key |
| Object storage | Check default encryption settings |
| Databases | Confirm TDE or column encryption |
| Backups | Verify backup encryption |

**In Transit:**
| Connection | Requirement |
|------------|-------------|
| User to application | TLS 1.2+ required |
| Service to service | Internal TLS or VPN |
| API communications | HTTPS only, no HTTP |
| Database connections | TLS required |

### Key Management Assessment

- [ ] Customer-managed keys used for sensitive data
- [ ] Key rotation policy defined and implemented
- [ ] Key access restricted to authorized services
- [ ] Key usage logged and monitored
- [ ] Disaster recovery for keys documented

### Data Classification in Cloud

| Classification | Cloud Requirements |
|----------------|-------------------|
| Confidential | CMK encryption, access logging, no public access |
| Internal | Encryption enabled, network restrictions |
| Public | Integrity protection, CDN appropriate |

---

## Identity and Access Management

### Privileged Access Review

1. Identify all administrative roles
2. Verify role assignment justification
3. Check for standing vs. just-in-time access
4. Review privileged activity logs
5. Confirm MFA required for elevation

### Service Account Assessment

| Check | Verification |
|-------|--------------|
| Inventory | All service accounts documented |
| Permissions | Least privilege applied |
| Credentials | Keys rotated per policy |
| Monitoring | Activity logged and reviewed |
| Ownership | Clear owner assigned |

### Federation and SSO

- [ ] SSO configured for cloud console access
- [ ] Conditional Access/MFA policies applied
- [ ] Session timeout configured
- [ ] Failed login monitoring enabled
- [ ] Emergency access accounts documented

### API Security

- [ ] API keys not embedded in code
- [ ] Secrets management service used
- [ ] API access logged
- [ ] Rate limiting configured
- [ ] API permissions follow least privilege
