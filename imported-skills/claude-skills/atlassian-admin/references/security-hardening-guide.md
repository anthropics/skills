# Atlassian Cloud Security Hardening Guide

## Overview

This guide provides a comprehensive security hardening checklist for Atlassian Cloud products (Jira, Confluence, Bitbucket). It covers identity management, access controls, data protection, and monitoring practices aligned with enterprise security standards.

## Identity & Authentication

### SSO / SAML Setup

**Implementation Steps:**
1. Verify your domain in Atlassian Admin (admin.atlassian.com)
2. Claim all company email accounts
3. Configure SAML SSO with your identity provider (Okta, Azure AD, Google Workspace)
4. Set authentication policy to enforce SSO for all managed accounts
5. Test with a pilot group before full rollout
6. Disable password-based login for managed accounts

**Configuration Checklist:**
- [ ] Domain verified and accounts claimed
- [ ] SAML IdP configured with correct entity ID and SSO URL
- [ ] Attribute mapping: email, displayName, groups
- [ ] Single Logout (SLO) configured
- [ ] Authentication policy enforcing SSO
- [ ] Fallback access configured for emergency admin accounts
- [ ] SCIM provisioning enabled for automatic user sync

### Two-Factor Authentication (2FA)

**Enforcement Policy:**
- [ ] 2FA required for all managed accounts
- [ ] Enforce via authentication policy (not just recommended)
- [ ] Hardware security keys (FIDO2/WebAuthn) preferred for admin accounts
- [ ] TOTP (authenticator app) as minimum for all users
- [ ] SMS-based 2FA disabled (SIM swap vulnerability)
- [ ] Recovery codes generated and stored securely

### Session Management
- [ ] Session timeout set to 8 hours of inactivity (maximum)
- [ ] Absolute session timeout: 24 hours
- [ ] Require re-authentication for sensitive operations
- [ ] Monitor concurrent sessions per user
- [ ] Enforce session termination on password change

## Access Controls

### IP Allowlisting

**Configuration:**
- [ ] Enable IP allowlisting for organization
- [ ] Add corporate office IP ranges
- [ ] Add VPN exit node IP addresses
- [ ] Add CI/CD server IPs for API access
- [ ] Test access from all approved locations
- [ ] Document approved IP ranges with justification
- [ ] Review IP allowlist quarterly

**Exceptions:**
- Mobile access may require VPN or MDM solution
- Remote workers need VPN or conditional access policies
- API integrations need stable IP ranges

### API Token Management

**Policies:**
- [ ] Inventory all API tokens in use
- [ ] Set maximum token lifetime (90 days recommended)
- [ ] Require token rotation on schedule
- [ ] Use service accounts for integrations (not personal tokens)
- [ ] Monitor API token usage patterns
- [ ] Revoke tokens immediately on employee departure
- [ ] Document purpose and owner for each token

**Best Practices:**
- Use OAuth 2.0 (3LO) for user-context integrations
- Use API tokens only for service-to-service
- Store tokens in secrets management (never in code)
- Implement least-privilege scopes for OAuth apps

### Permission Model
- [ ] Review global permissions quarterly
- [ ] Use groups for permission assignment (not individual users)
- [ ] Implement role-based access for Jira projects
- [ ] Restrict Confluence space admin to designated owners
- [ ] Limit Jira system admin to 2-3 people
- [ ] Audit "anyone" or "logged in users" permissions
- [ ] Remove direct user permissions where groups exist

## Audit & Monitoring

### Audit Log Configuration

**What to Monitor:**
- User authentication events (login, logout, failed attempts)
- Permission changes (project, space, global)
- User account changes (creation, deactivation, group changes)
- API token creation and revocation
- App installations and updates
- Data export operations
- Admin configuration changes

**Setup Steps:**
- [ ] Enable organization audit log
- [ ] Configure audit log retention (minimum 1 year)
- [ ] Set up automated export to SIEM (Splunk, Datadog, etc.)
- [ ] Create alerts for suspicious patterns
- [ ] Schedule monthly audit log review
- [ ] Document incident response procedures for alerts

### Alerting Rules

**Critical Alerts (Immediate Response):**
- Multiple failed login attempts (>5 in 10 minutes)
- Admin permission grants to unexpected users
- API token created by non-service accounts
- Bulk data export or deletion
- New third-party app installed with broad permissions

**Warning Alerts (Same-Day Review):**
- New admin users added
- Permission scheme changes
- Authentication policy modifications
- IP allowlist changes
- User deactivation (verify it is expected)

## Data Protection

### Data Residency
- [ ] Configure data residency realm (US, EU, AU, etc.)
- [ ] Verify product data pinned to selected region
- [ ] Document data residency for compliance audits
- [ ] Review data residency coverage (some metadata may be global)
- [ ] Monitor for new residency options from Atlassian

### Encryption
- [ ] Verify encryption at rest (AES-256, managed by Atlassian)
- [ ] Verify encryption in transit (TLS 1.2+)
- [ ] Review Atlassian's encryption key management practices
- [ ] Consider BYOK (Bring Your Own Key) for Atlassian Guard Premium

### Data Loss Prevention
- [ ] Configure content restrictions for sensitive pages/issues
- [ ] Implement classification labels (public, internal, confidential)
- [ ] Restrict file attachment types if needed
- [ ] Monitor bulk exports and downloads
- [ ] Set up DLP rules for sensitive data patterns (PII, credentials)

## Mobile Device Management

### Mobile Access Controls
- [ ] Require MDM enrollment for mobile Atlassian apps
- [ ] Enforce device encryption
- [ ] Require screen lock with biometrics or PIN
- [ ] Enable remote wipe capability
- [ ] Block rooted/jailbroken devices
- [ ] Restrict copy/paste to managed apps
- [ ] Set app-level PIN for Atlassian apps

### Mobile Policies
- [ ] Define approved mobile devices/OS versions
- [ ] Enforce automatic app updates
- [ ] Configure offline data access limits
- [ ] Set maximum offline cache duration
- [ ] Review mobile access logs monthly

## Third-Party App Security

### App Review Process
- [ ] Maintain approved app list (whitelist)
- [ ] Review app permissions before installation
- [ ] Verify app is Atlassian Marketplace certified
- [ ] Check app vendor security certifications
- [ ] Assess data access scope (read-only vs read-write)
- [ ] Review app privacy policy
- [ ] Document app owner and business justification

### App Governance
- [ ] Audit installed apps quarterly
- [ ] Remove unused apps (no usage in 90 days)
- [ ] Monitor app permission changes
- [ ] Restrict app installation to admins only
- [ ] Review Atlassian Guard app access policies
- [ ] Set up alerts for new app installations

## Compliance Documentation

### Required Documentation
- [ ] Security policy for Atlassian Cloud usage
- [ ] Access control matrix (roles, permissions, justification)
- [ ] Incident response plan for Atlassian security events
- [ ] Data classification policy applied to Atlassian content
- [ ] Third-party app risk assessments
- [ ] Annual security review report

### Compliance Frameworks
- **SOC 2:** Map Atlassian controls to Trust Service Criteria
- **ISO 27001:** Align with Annex A controls for cloud services
- **GDPR:** Configure data residency, right to deletion, DPAs
- **HIPAA:** Review BAA availability, encryption, access controls

## Hardening Schedule

| Task | Frequency | Owner |
|------|-----------|-------|
| Permission audit | Quarterly | IT Admin |
| API token rotation | Every 90 days | Integration owners |
| App review | Quarterly | IT Admin |
| Audit log review | Monthly | Security team |
| IP allowlist review | Quarterly | IT Admin |
| Authentication policy review | Semi-annually | Security team |
| Full security assessment | Annually | Security team |
| User access review | Quarterly | Managers + IT Admin |
| Data residency verification | Annually | Compliance |
| Mobile device audit | Quarterly | IT Admin |
