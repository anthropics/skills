# SFC: SEAL Framework Checklist

SFC Workspace Security certification: device management, account security, credential handling, network security, employee training, and insider threat assessment.

**Controls and baselines for self-assessment and certification.**

## ws-1: Governance & Inventory

### ws-1.1.1 — Workspace Security Owner
**Q:** Is there a clearly designated person or team accountable for workspace security?

**Baselines:**
- Accountability scope covers policy maintenance, device and account standards, access control oversight, periodic reviews, and incident escalation

### ws-1.1.2 — Workspace Security Policy
**Q:** Do you maintain a workspace security policy that is accessible and understood by all personnel?

**Baselines:**
- Policy covers core expectations including device security, account hygiene, credential management, acceptable use, and incident reporting
- Written in plain language so all personnel can follow it
- Policy reviewed at least annually and after significant changes (security incidents, technology shifts, organizational restructuring)

### ws-1.1.3 — Asset Inventory
**Q:** Do you maintain an inventory of organizational devices and accounts with defined ownership?

**Baselines:**
- Scoped to devices and accounts with access to sensitive systems or data
- Device inventory tracks make/model, owner, OS version, encryption status, and EDR/MDM enrollment
- Account inventory covers organizational accounts (eg. email, cloud, social media) with defined ownership
- Updated as devices/accounts are provisioned or decommissioned

### ws-1.1.4 — System and Data Classification
**Q:** Do you classify systems and data by sensitivity to determine appropriate security controls?

**Baselines:**
- Classification levels defined (e.g., critical, high, standard)
- Classification determines which controls apply (access restrictions, monitoring, encryption, backup requirements)
- Classification reviewed when systems, data sensitivity, or organizational structure change

## ws-2: Device Security

### ws-2.1.1 — Device Security Standards
**Q:** Do you define and enforce security standards for organizational devices?

**Baselines:**
- Full disk encryption enabled on all devices
- Automatic OS and application patching enabled or enforced
- Strong authentication required (password/biometric, auto-lock timeouts, lock screens)
- Administrative privileges separated from daily-use accounts
- Devices procured through verified supply chains and verified for integrity upon receipt
- Device compliance verified upon provisioning and monitored on an ongoing basis
- BYOD policy defining what personal devices can access and the security controls required (e.g., MDM enrollment, separate work profiles)

### ws-2.1.2 — Device Lifecycle Management
**Q:** Do you have procedures for device loss, theft, and secure decommissioning?

**Baselines:**
- Remote lock and wipe capability for all organizational devices
- Documented procedures for responding to lost or stolen devices (notification, remote wipe, credential rotation, incident escalation)
- Secure decommissioning procedures including data sanitization and verified destruction for storage media

### ws-2.1.3 — Endpoint Protection
**Q:** Do you deploy and monitor endpoint protection on organizational devices?

**Baselines:**
- EDR or MDM deployed on all organizational devices with documented coverage
- Alert triage and response procedures defined with severity-based escalation
- Compliance enforcement actions documented (e.g., quarantine non-compliant devices, block access)
- Monitoring coverage includes detection of malware, unauthorized software, and policy violations

### ws-2.1.4 — Physical and Travel Security
**Q:** Do you maintain physical security requirements for workspaces and travel?

**Baselines:**
- Physical workspace requirements defined for both on-site and remote work environments
- Screen privacy and shoulder-surfing awareness enforced
- Travel security procedures documented covering device handling, network usage, and border crossings
- High-risk travel procedures defined (loaner devices, enhanced controls, check-in schedules)
- USB and charging security addressed (data blockers, no public USB ports)
- Devices physically secured when not in active use (cable locks, safes, carry-on luggage for travel)

## ws-3: Account, Access & Credential Management

### ws-3.1.1 — Account Lifecycle Management
**Q:** Do you have procedures for provisioning, modifying, and revoking user accounts?

**Baselines:**
- Account creation requires documented approval from the account owner's manager or designated authority
- Accounts provisioned with minimum necessary permissions (least privilege)
- Modification of account permissions requires documented approval
- Account revocation procedures tied to offboarding and role changes
- Service accounts and shared credentials inventoried with defined ownership

### ws-3.1.2 — Multi-Factor Authentication
**Q:** Do you enforce multi-factor authentication across organizational accounts?

**Baselines:**
- MFA required for all organizational accounts by default
- Hardware security keys required for high-privilege and critical accounts (admin, infrastructure, custody)
- Phishing-resistant MFA preferred (FIDO2/WebAuthn, hardware keys) over SMS or TOTP where available
- Exceptions documented with justification, compensating controls, and expiry date
- Backup MFA methods configured for account recovery

### ws-3.1.3 — Organizational Account Security
**Q:** Do you maintain security standards for all organizational accounts, including enterprise platforms and external services?

**Baselines:**
- Security configuration standards defined and applied for enterprise platforms (Google Workspace, Microsoft 365, collaboration tools)
- Social media and public-facing accounts secured with strong authentication and defined ownership
- Ownership verified and documented for all organizational accounts
- Recovery methods restricted to organizational channels (no personal recovery emails or phone numbers on organizational accounts)
- Account configurations reviewed periodically for drift or unauthorized changes

### ws-3.1.4 — Credential Management Standards
**Q:** Do you enforce credential management standards, including secure storage and individual accountability?

**Baselines:**
- Password manager required for all personnel; no passwords stored in plain text, documents, or browsers
- Unique, strong passwords for every account (minimum length/complexity standards defined)
- Individual accounts required for all personnel — no sharing of personal login credentials
- When credentials must be provisioned or shared (e.g., service accounts, API keys, onboarding), transmission only through encrypted channels (password manager sharing features, not email or chat)
- Credential rotation schedule defined based on risk; rotation triggered immediately after suspected compromise
- Enhanced controls for high-privilege credentials (admin accounts, service accounts, API keys) including stricter rotation, separate storage, and logged access
- Service account and API key inventory maintained with defined ownership

### ws-3.1.5 — Access Reviews
**Q:** Do you conduct periodic access reviews and promptly adjust permissions when roles change?

**Baselines:**
- Scheduled access reviews at least quarterly for critical systems, annually for others
- Access adjusted within defined timelines when employees change roles
- Reviews verify each user still requires their current level of access
- Unnecessary permissions revoked promptly with documented evidence
- Insider threat consideration included — for each role, assess what damage could be done with current access

## ws-4: Software & Application Security

### ws-4.1.1 — Software Evaluation and Approval
**Q:** Do you evaluate and approve software, extensions, and tools before organizational use?

**Baselines:**
- Evaluation criteria for all software before adoption (browsers, extensions, IDEs, libraries, AI assistants, SaaS tools)
- Data privacy and leakage risks assessed (does the tool send data to third parties for training or analytics?)
- Approved software list maintained; unapproved software restricted
- Browser extension approval process defined
- Dependency management includes version pinning, vulnerability scanning, and update policies

### ws-4.1.2 — Source Code and Repository Security
**Q:** Do you secure source code repositories against unauthorized access and credential exposure?

**Baselines:**
- Role-based access control with least-privilege permissions
- Branch protection rules enforced on critical branches (require reviews, signed commits)
- Automated secret scanning enabled to detect credentials, API keys, and private keys in code
- Pre-commit hooks or CI checks to prevent secrets from being committed
- Repository security audited periodically (access permissions, configuration, open PRs)

## ws-5: Network & Communication

### ws-5.1.1 — Network Security
**Q:** Do you enforce secure network access for organizational systems?

**Baselines:**
- VPN or zero-trust network access required for accessing internal resources remotely
- Wi-Fi security standards defined (no auto-connect, avoid public Wi-Fi for sensitive operations)
- Network segmentation applied where applicable (separate guest networks, development environments)
- Cellular or personal hotspot preferred over public Wi-Fi for sensitive work

### ws-5.1.2 — Secure Communications
**Q:** Do you secure organizational communications and verify identity for sensitive interactions?

**Baselines:**
- End-to-end encrypted channels used for sensitive communications
- Identity verification procedures established for sensitive requests (e.g., access changes, financial approvals, credential sharing)
- Anti-impersonation protocols documented (e.g., secondary channel verification, code words, video confirmation)
- Email security configured (SPF, DKIM, DMARC) to prevent spoofing
- Procedures for channel compromise including switching to backup channels

## ws-6: People & Training

### ws-6.1.1 — Security Onboarding
**Q:** Do you verify employee identity and provide security onboarding before granting system access?

**Baselines:**
- Identity and authorization verified before any access is provisioned
- Background checks or identity verification appropriate to role sensitivity
- Security onboarding includes device provisioning, account creation, MFA setup, and initial security training
- New personnel acknowledge security policies before access is granted
- Onboarding checklist documented and consistently applied

### ws-6.1.2 — Security Offboarding
**Q:** Do you have comprehensive offboarding procedures for departing personnel?

**Baselines:**
- All account access revoked within 24 hours of departure
- Devices returned and verified for data sanitization
- Credentials and secrets rotated for any shared systems the departing person accessed
- Offboarding checklist documented covering: account deprovisioning, device return, credential rotation, access to organizational repositories and tools, recovery of company property
- Involuntary departures trigger immediate access revocation before notification where feasible

### ws-6.1.3 — Security Awareness and Training
**Q:** Do you maintain a security awareness program with regular training and testing?

**Baselines:**
- Training covers workspace security topics: phishing, social engineering, device security, credential hygiene, and incident reporting
- Phishing simulations conducted at least quarterly
- Follow-up training required for personnel who fail simulations
- Training content updated annually and after significant threats or procedure changes
- Covers crypto-specific risks: fake job offers, malicious browser extensions, clipboard hijacking, social engineering via DMs

## ws-7: Monitoring & Risk Management

### ws-7.1.1 — Workspace Security Monitoring and Incident Response
**Q:** Do you detect and respond to workspace security incidents?

**Baselines:**
- Monitoring in place for common workspace threats: account takeovers, unauthorized access, credential leaks, device compromise, data exfiltration
- Response procedures documented for key scenarios: compromised account, compromised device, data leak, insider threat event
- Escalation paths defined with severity levels
- Credential leak monitoring (dark web, breach databases, paste sites, code repositories)
- Incidents documented with timeline, root cause, actions taken, and lessons learned

### ws-7.1.2 — Insider Threat Assessment
**Q:** Do you assess insider threat risks and enforce least-privilege access for each role?

**Baselines:**
- Damage scenarios documented for each role (what could this person do if compromised or malicious?)
- Least-privilege access enforced across all systems
- Separation of duties applied for critical operations (e.g., no single person can deploy to production, execute large transactions, and manage access controls)
- Assessed during periodic access reviews

### ws-7.1.3 — Third-Party Access Management
**Q:** Do you manage third-party access with time-limited, purpose-specific permissions?

**Baselines:**
- Third-party access requires documented approval with defined scope and expiry date
- Access limited to minimum necessary systems and data
- Access revoked automatically upon contract expiry or project completion
- Audit trails maintained for all third-party access
- Third-party vendor security evaluated before granting access (security certifications, incident history)
