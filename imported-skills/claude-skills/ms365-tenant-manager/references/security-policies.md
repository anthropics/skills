# Security Policies Reference

Comprehensive security configuration guide for Microsoft 365 tenants covering Conditional Access, MFA, DLP, and security baselines.

---

## Table of Contents

- [Conditional Access Policies](#conditional-access-policies)
- [Multi-Factor Authentication](#multi-factor-authentication)
- [Data Loss Prevention](#data-loss-prevention)
- [Security Baselines](#security-baselines)
- [Admin Role Security](#admin-role-security)
- [Guest Access Controls](#guest-access-controls)

---

## Conditional Access Policies

### Policy Architecture

| Policy Type | Target Users | Applications | Grant Control |
|-------------|-------------|--------------|---------------|
| Admin MFA | Admin roles | All apps | Require MFA |
| User MFA | All users | All apps | Require MFA |
| Device Compliance | All users | Office 365 | Compliant device |
| Location-Based | All users | All apps | Block non-trusted |
| Legacy Auth Block | All users | All apps | Block |

### Recommended Policies

#### 1. Require MFA for Administrators

**Scope:** Global Admin, Security Admin, Exchange Admin, SharePoint Admin, User Admin

**Settings:**
- Include: Directory roles (admin roles)
- Exclude: Emergency access accounts
- Grant: Require MFA
- Session: Sign-in frequency 4 hours

#### 2. Require MFA for All Users

**Scope:** All users

**Settings:**
- Include: All users
- Exclude: Emergency access accounts, service accounts
- Conditions: All cloud apps
- Grant: Require MFA
- Session: Persistent browser session disabled

#### 3. Block Legacy Authentication

**Scope:** All users

**Settings:**
- Include: All users
- Conditions: Exchange ActiveSync, Other clients
- Grant: Block access

**Why:** Legacy protocols (POP, IMAP, SMTP AUTH) cannot enforce MFA.

#### 4. Require Compliant Devices

**Scope:** All users accessing sensitive data

**Settings:**
- Include: All users
- Applications: Office 365, SharePoint, Exchange
- Grant: Require device compliance OR Hybrid Azure AD joined
- Platforms: Windows, macOS, iOS, Android

#### 5. Block Access from Untrusted Locations

**Scope:** High-risk operations

**Settings:**
- Include: All users
- Applications: Azure Management, Microsoft Graph
- Conditions: Exclude named locations (corporate IPs)
- Grant: Block access

### Named Locations Configuration

| Location Name | Type | IP Ranges |
|--------------|------|-----------|
| Corporate HQ | IP ranges | 203.0.113.0/24 |
| VPN Exit Points | IP ranges | 198.51.100.0/24 |
| Trusted Countries | Countries | US, CA, GB |
| Blocked Countries | Countries | (high-risk regions) |

### Policy Deployment Strategy

1. **Report-Only Mode (Week 1-2)**
   - Enable policies in report-only
   - Monitor sign-in logs for impact
   - Identify false positives

2. **Pilot Group (Week 3-4)**
   - Enable for IT staff first
   - Address issues before broad rollout
   - Document exceptions needed

3. **Gradual Rollout (Week 5-8)**
   - Enable by department
   - Provide user communication
   - Monitor help desk tickets

4. **Full Enforcement**
   - Enable for all users
   - Maintain exception process
   - Quarterly policy review

---

## Multi-Factor Authentication

### MFA Methods (Strength Ranking)

| Method | Security Level | User Experience |
|--------|---------------|-----------------|
| FIDO2 Security Keys | Highest | Excellent |
| Windows Hello | Highest | Excellent |
| Microsoft Authenticator (Passwordless) | High | Good |
| Microsoft Authenticator (Push) | High | Good |
| OATH Hardware Token | High | Fair |
| SMS/Voice | Medium | Good |
| Email OTP | Low | Fair |

### Recommended Configuration

**For Administrators:**
- Require phishing-resistant MFA (FIDO2, Windows Hello)
- Disable SMS/Voice as backup
- Enforce re-authentication every 4 hours

**For Standard Users:**
- Require Microsoft Authenticator
- Allow SMS as backup (temporary)
- Session lifetime: 90 days with risk-based re-auth

**For External/Guest Users:**
- Require MFA from home tenant
- Fall back to email OTP if needed

### MFA Registration Campaign

```
Phase 1: Communication (Week 1)
- Announce MFA requirement
- Provide registration instructions
- Set deadline for registration

Phase 2: Registration (Week 2-3)
- Open registration portal
- IT support available
- Track registration progress

Phase 3: Enforcement (Week 4)
- Enable MFA requirement
- Grace period for stragglers
- Block unregistered after deadline
```

---

## Data Loss Prevention

### Sensitive Information Types

| Category | Examples | Action |
|----------|----------|--------|
| Financial | Credit card, Bank account | Block external sharing |
| PII | SSN, Passport, Driver's license | Require justification |
| Health | Medical records, Insurance | Block and notify |
| Credentials | Passwords, API keys | Block all sharing |

### DLP Policy Templates

#### Financial Data Protection

**Scope:** Exchange, SharePoint, OneDrive, Teams

**Rules:**
1. Credit card numbers (Luhn validated)
2. Bank account numbers
3. SWIFT codes

**Actions:**
- Block external sharing
- Encrypt email to external recipients
- Notify compliance team

#### PII Protection

**Scope:** All Microsoft 365 locations

**Rules:**
1. Social Security Numbers
2. Passport numbers
3. Driver's license numbers

**Actions:**
- Warn user before sharing
- Require business justification
- Log all incidents

#### Healthcare (HIPAA)

**Scope:** Exchange, SharePoint, Teams

**Rules:**
1. Medical record numbers
2. Health insurance IDs
3. Drug names with patient info

**Actions:**
- Block external sharing
- Apply encryption
- Retain for 7 years

### DLP Deployment

1. **Audit Mode First**
   - Enable policies in test mode
   - Review matched content
   - Tune false positives

2. **User Tips**
   - Enable policy tips in apps
   - Educate before enforcing
   - Provide override option with justification

3. **Enforcement**
   - Block high-risk content
   - Warn for medium-risk
   - Log everything

---

## Security Baselines

### Microsoft Secure Score Targets

| Category | Target Score | Key Actions |
|----------|-------------|-------------|
| Identity | 80%+ | MFA, Conditional Access, PIM |
| Data | 70%+ | DLP, Sensitivity labels, Encryption |
| Device | 75%+ | Compliance policies, Defender |
| Apps | 70%+ | OAuth app review, Admin consent |

### Priority Security Settings

#### Identity (Do First)

- [ ] Enable Security Defaults OR Conditional Access
- [ ] Require MFA for all admins
- [ ] Block legacy authentication
- [ ] Enable self-service password reset
- [ ] Configure password protection (banned passwords)

#### Data Protection

- [ ] Enable sensitivity labels
- [ ] Configure DLP policies
- [ ] Enable audit logging
- [ ] Set retention policies
- [ ] Configure information barriers (if needed)

#### Device Security

- [ ] Require device compliance
- [ ] Enable Microsoft Defender for Endpoint
- [ ] Configure BitLocker requirements
- [ ] Set application protection policies
- [ ] Enable Windows Autopilot

#### Application Security

- [ ] Review OAuth app permissions
- [ ] Configure admin consent workflow
- [ ] Block risky OAuth apps
- [ ] Enable app governance
- [ ] Configure MCAS policies

---

## Admin Role Security

### Privileged Identity Management (PIM)

**Configuration:**
- Require approval for Global Admin activation
- Maximum activation: 8 hours
- Require MFA at activation
- Require justification
- Send notification to security team

### Role Assignment Best Practices

| Role | Assignment Type | Approval Required |
|------|-----------------|-------------------|
| Global Admin | Eligible only | Yes |
| Security Admin | Eligible only | Yes |
| User Admin | Eligible | No |
| Help Desk Admin | Permanent (limited) | No |

### Emergency Access Accounts

**Configuration:**
- 2 cloud-only accounts
- Excluded from ALL Conditional Access
- No MFA (break-glass scenario)
- Monitored via alerts
- Passwords in secure vault
- Test quarterly

**Naming:** `emergency-access-01@tenant.onmicrosoft.com`

---

## Guest Access Controls

### Guest Invitation Settings

| Setting | Recommended Value |
|---------|------------------|
| Guest invite restrictions | Admins and users in guest inviter role |
| Enable guest self-service sign-up | No |
| Enable email one-time passcode | Yes |
| Collaboration restrictions | Allow invitations only to specified domains |

### Guest Access Review

**Frequency:** Quarterly

**Scope:**
- All guest users
- Group memberships
- Application access

**Actions:**
- Remove inactive guests (90+ days)
- Revoke unnecessary permissions
- Require re-certification

### B2B Collaboration Settings

**Allowed Domains:**
- Partners: `partner1.com`, `partner2.com`
- Block all others for sensitive resources

**Guest Permissions:**
- Limited directory browsing
- Cannot enumerate users
- Cannot invite other guests
