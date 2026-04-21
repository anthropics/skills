# SFC: SEAL Framework Checklist

SFC Treasury Operations certification: governance, custody architecture, risk classification, access control, transaction security, protocol deployments, monitoring, incident response, vendor management, and accounting.

**Controls and baselines for self-assessment and certification.**

## tro-1: Governance & Treasury Architecture

### tro-1.1.1 — Treasury Operations Owner
**Q:** Is there a clearly designated person or team accountable for treasury operations?

**Baselines:**
- Accountability scope covers policy upkeep, security reviews, operational hygiene, access control oversight, and incident escalation

### tro-1.1.2 — Treasury Registry and Documentation
**Q:** Do you maintain a complete, current record of all treasury wallets, accounts, and their configurations?

**Baselines:**
- Registry includes wallet/account address, network/chain, custody provider, custody model, purpose/classification, authorized signers/approvers, controlled contracts or protocols, and last review date
- Updated within 24 hours for security-critical changes (signer changes, new wallets), 3 days for routine changes
- Accessible to authorized treasury personnel

### tro-1.1.3 — Custody Architecture Rationale
**Q:** Do you have documented rationale for your treasury custody architecture?

**Baselines:**
- Custody model documented for each wallet/account (custodial, self-custody, co-managed, MPC, multisig, HSM)
- Technology trade-offs understood by the team (not necessarily a formal document — could be a brief internal memo)
- Custody architecture reviewed when treasury size, operational needs, or risk profile changes significantly

### tro-1.1.4 — Treasury Infrastructure Change Management
**Q:** Do you have change management procedures for treasury infrastructure modifications?

**Baselines:**
- Covers wallet setups, custody configurations, signer/approver permission changes, and protocol integrations
- Changes require documented approval before implementation
- All changes logged with justification and approver
- Changes reflected in the treasury registry within defined SLAs
- Rollback procedures documented for critical changes

## tro-2: Risk Classification & Fund Allocation

### tro-2.1.1 — Treasury Wallet Risk Classification
**Q:** Do you classify your treasury wallets and accounts by risk level and assign security controls accordingly?

**Baselines:**
- Classification considers financial exposure, operational dependency, and regulatory impact
- Impact levels defined (e.g., Low <1%, Medium 1-10%, High 10-25%, Critical >25% of total assets)
- Operational types defined based on transaction frequency and urgency requirements
- Each classification maps to specific controls including approval thresholds, MFA requirements, whitelist delays, and monitoring levels
- Classification reviewed when asset values, operational patterns, or risk profile change significantly

### tro-2.1.2 — Fund Allocation Limits and Rebalancing
**Q:** Do you enforce fund allocation limits and rebalancing triggers across your treasury?

**Baselines:**
- Maximum allocation defined per wallet, per custody provider, and per chain
- Rebalancing triggers documented (e.g., when a wallet exceeds its allocation ceiling or falls below operational minimums)
- Allocation limits reviewed periodically and after significant treasury changes
- No single wallet or custody account holds more than the organization's defined maximum concentration

## tro-3: Access Control & Platform Security

### tro-3.1.1 — Custody Platform Security Configuration
**Q:** Do you configure and maintain security controls on your custody platforms?

**Baselines:**
- Transaction policy rules configured: multi-approval workflows, approval thresholds scaled to transaction value, address whitelisting with cooling-off periods, velocity/spending limits
- Hardware security key MFA required for all approvers on High and Critical accounts
- Session timeouts and re-authentication for sensitive operations
- Network restrictions: IP whitelisting, VPN requirements where supported, geographic access restrictions
- Separation of duties enforced: initiators cannot approve their own transactions, admins cannot unilaterally execute withdrawals
- Platform configurations documented and reviewed at least quarterly

### tro-3.1.2 — Credential and Secret Management
**Q:** Do you securely manage all credentials and secrets used in treasury operations?

**Baselines:**
- Covers API keys, service accounts, owner/admin credentials, and signing keys
- Credentials stored in dedicated secret management systems, not in code, documents, or shared drives
- Owner and admin credentials isolated from day-to-day operational access
- Credential rotation schedule defined and enforced
- Access to credentials logged and monitored

### tro-3.1.3 — Access Reviews for Treasury Systems
**Q:** Do you periodically review who has access to treasury systems?

**Baselines:**
- Access reviews conducted at least quarterly for High/Critical accounts, annually for others
- Reviews verify each user still requires their current access level
- Access promptly revoked when personnel change roles or leave

### tro-3.1.4 — Personnel Operational Security
**Q:** Do you enforce operational security requirements for treasury personnel?

**Baselines:**
- Device security requirements documented: dedicated devices for custody access, full disk encryption, automatic screen lock
- Signing devices (hardware wallets) securely stored when not in use
- Backup materials (seed phrases, recovery keys) stored securely with geographic distribution
- VPN mandatory for all remote treasury platform access
- Travel security procedures for personnel with signing or custody access capabilities
- Mobile devices used as second factors have endpoint security monitoring

## tro-4: Transaction Security

### tro-4.1.1 — Transaction Verification and Execution
**Q:** Do you have a defined process for verifying and executing treasury transactions?

**Baselines:**
- Pre-execution verification includes: recipient address validation, amount verification, network confirmation, and transaction simulation
- Test transactions required before sending to new addresses
- Address verified through multiple independent sources; never copied from email, chat, or transaction history
- Multi-party confirmation required: minimum 2 internal personnel for large transfers
- Specific procedures for receiving large incoming transfers (address generation, bidirectional test, sender coordination)
- Specific procedures for OTC transactions where applicable
- High-value transfers (organization-defined threshold) require video call verification with liveness checks
- All transaction parameters read aloud and confirmed before execution

### tro-4.1.2 — Signer and Approver Knowledge
**Q:** Are treasury signers and approvers knowledgeable in the security practices relevant to their role?

**Baselines:**
- Knowledge covers: transaction verification procedures, address validation techniques, social engineering awareness, emergency procedures
- Competence demonstrated before authorization (e.g., verifying a test transaction end-to-end)
- Knowledge refreshed annually; updated within 30 days of significant procedure changes
- Covers custody-platform-specific workflows and policy engine rules

### tro-4.1.3 — Secure Communication Procedures
**Q:** Do you have secure communication procedures for treasury operations, including standard identity verification?

**Baselines:**
- Dedicated primary and backup channels on different platforms
- End-to-end encryption, MFA required, invitation-based membership
- Identity verified as standard procedure during signing/approval operations (e.g., code phrases, video call, secondary authenticated channel)
- Anti-social-engineering protocols: established verification procedures for address changes or unusual requests
- Documented procedures for channel compromise including switching to backup channels and out-of-band verification
- All treasury personnel trained on these procedures; compromise response tested annually

## tro-5: Protocol Deployments

### tro-5.1.1 — Protocol Evaluation and Exposure Limits
**Q:** Do you evaluate external protocols and enforce exposure limits before deploying treasury funds?

**Baselines:**
- Due diligence process for all protocols before deployment: smart contract audit status, team reputation, TVL history, insurance coverage
- Exposure limits defined per protocol, per chain, and per deployment category (DeFi, staking, liquid staking, etc.)
- Limits reviewed periodically and after significant market or protocol changes
- Risk re-evaluation triggered by: security incidents, major governance proposals, significant TVL changes, new vulnerabilities disclosed

### tro-5.1.2 — Position Lifecycle Management
**Q:** Do you have procedures for managing the lifecycle of your positions in external protocols?

**Baselines:**
- Entry procedures: smart contract address verification against multiple independent sources, token approval management (minimal approvals, revocation after use)
- Emergency withdrawal/exit procedures documented for all active positions
- Alternative access methods documented in case primary UIs are unavailable (direct contract interaction, CLI tools, alternative frontends)
- Unbonding/unstaking timelines understood and factored into liquidity planning

## tro-6: Monitoring & Incident Response

### tro-6.1.1 — Monitoring and Threat Awareness
**Q:** Do you monitor your treasury for anomalous activity, external threats, and operational risks?

**Baselines:**
- Transaction monitoring: unusual amounts, unexpected destinations, failed transactions, policy violations
- Account state monitoring: balance changes, configuration modifications, new device enrollments, authentication anomalies
- External threat intelligence: protocol vulnerabilities, DeFi/staking risks, relevant security incidents in the ecosystem
- Vendor/platform monitoring: custody platform status, infrastructure alerts, service availability
- Compliance monitoring: transactions and wallet addresses screened for sanctions and compliance risk
- Protocol and position monitoring: deployed protocol health, governance changes, TVL shifts, collateral ratios, reward accrual, liquidation risks
- Alerting with defined severity levels and escalation paths
- Critical alerts (large unexpected transactions, unauthorized access attempts) trigger immediate investigation
- Monitoring system integrity protected — alerts triggered when monitoring configurations are changed, disabled, or degraded

### tro-6.1.2 — Incident Response Plan
**Q:** Do you have an incident response plan for treasury security events, and do you test it?

**Baselines:**
- Severity levels defined with escalation procedures specific to treasury operations
- Containment procedures: fund protection actions (emergency freeze, transfer to secure cold storage, policy lockdown)
- Covers key scenarios: custody platform compromise, unauthorized transaction, signer key compromise, vendor breach
- Emergency contacts pre-documented: custody provider security team, SEAL 911, legal counsel
- Communication plan for stakeholders
- Drills conducted at least annually; after major procedure changes
- Drill documentation includes: date, participants, response times, issues identified, improvements made

## tro-7: Vendor & Infrastructure

### tro-7.1.1 — Vendor Security Management
**Q:** Do you evaluate and monitor the security of third-party services used in treasury operations?

**Baselines:**
- Initial due diligence before adoption: security certifications (SOC 2, ISO 27001), audit history, insurance coverage, incident history
- Ongoing monitoring: SOC report currency, security incident notifications, service availability tracking
- Contractual security requirements verified periodically (at least annually)
- Critical vendor changes (ownership, infrastructure, security posture) trigger re-evaluation

### tro-7.1.2 — Backup Infrastructure and Alternate Access
**Q:** Do you have backup infrastructure and alternate access methods for treasury operations?

**Baselines:**
- Alternate access methods for custody platforms documented and tested (e.g., API access, mobile app, secondary UI)
- Backup RPC providers configured
- Procedures for operating treasury if primary custody platform is unavailable
- Backup infrastructure tested at least annually

## tro-8: Accounting & Reporting

### tro-8.1.1 — Financial Recordkeeping and Reconciliation
**Q:** Do you maintain accurate treasury records and conduct periodic reconciliation?

**Baselines:**
- All treasury transactions recorded with categorization, documentation, and authorization chain
- Periodic reconciliation between custody platform records, on-chain balances, and accounting records
- Reconciliation frequency scaled to account classification: daily for Active Operations, weekly for Warm Storage, monthly for Cold Vault
- Discrepancies investigated and resolved promptly
- Treasury reporting procedures documented with defined cadence and audience

### tro-8.1.2 — Insurance Coverage
**Q:** Do you maintain insurance coverage appropriate for your treasury operations?

**Baselines:**
- Coverage scope documented: what's covered (custody theft, hack, insider fraud) and what's excluded
- Coverage amounts appropriate relative to assets held
- Custody provider's insurance evaluated as part of vendor due diligence
- Insurance coverage reviewed at least annually or when treasury size changes significantly
