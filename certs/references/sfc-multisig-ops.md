# SFC: SEAL Framework Checklist

SFC Multisig Operations certification: governance, signer security, transaction verification, emergency playbooks, communication protocols, and 24/7 paging for critical multisigs.

**Controls and baselines for self-assessment and certification.**

## ms-1: Governance & Inventory

### ms-1.1.1 — Named Multisig Operations Owner
**Q:** Is there a clearly named person or team accountable for multisig operations?

**Baselines:**
- Accountability scope covers policy maintenance, signer onboarding/offboarding, documentation accuracy, periodic reviews, and incident escalation

### ms-1.1.2 — Multisig Registry and Documentation
**Q:** Do you maintain a complete, accurate, and accessible record of all your multisigs, their configurations, and their signers?

**Baselines:**
- Registry includes address, network, threshold, classification, purpose, signer addresses, controlled contracts, on-chain roles, and last review date
- Updated within 24 hours for security-critical changes, 3 days for routine changes
- Accessible to signers and key personnel

## ms-2: Risk Assessment & Management

### ms-2.1.1 — Multisig Classification and Risk-Based Controls
**Q:** Do you classify your multisigs by risk level and apply security controls proportional to each classification?

**Baselines:**
- Classification considers impact factors (financial exposure, protocol criticality, reputational risk) and operational needs (response time, coordination complexity)
- Each classification maps to specific required controls (thresholds, quorum composition, review cadence)
- All multisigs must have at least 3 distinct signers with a signing threshold of 50% or greater; N-of-N configurations should be avoided
- Higher-risk classifications require stronger controls (more signers, higher thresholds)
- Classifications reviewed every 6 months and after significant changes (TVL shifts, new products, protocol upgrades, security incidents)

### ms-2.1.2 — Contract-Level Security Controls
**Q:** Have you evaluated contract-level security controls that could limit the impact of a multisig compromise?

**Baselines:**
- Evaluation covers timelocks, modules, guards, address whitelisting, invariant enforcement, and parameter bounds
- Controls evaluated for each multisig based on classification
- Security review required before enabling any module or guard
- Decisions documented, including rationale for controls not implemented

### ms-2.1.3 — Exception Approval Process
**Q:** Do you have a process for approving and tracking exceptions to multisig policies?

**Baselines:**
- Exceptions require documented justification, expiry date, compensating controls, and remediation plan
- Critical-class exceptions require executive or security-lead approval

### ms-2.1.4 — Wallet Segregation
**Q:** Do you distribute assets across multiple wallets to limit the impact of a single compromise?

**Baselines:**
- Segregation considers value, operational needs, and risk tolerance
- Examples include hot/cold separation and treasury distribution across multiple wallets

## ms-3: Signer Security & Access Control

### ms-3.1.1 — Signer Address Verification
**Q:** Do you verify that each signer address on your multisigs belongs to the intended person?

**Baselines:**
- Verification process includes message signing with the signer address, verification via an independent tool, and documented proof of verification

### ms-3.1.2 — Signer Key Management Standards
**Q:** Do you enforce signer key management standards?

**Baselines:**
- Hardware wallets required for all multisig operations
- Each signer uses a fresh, dedicated address per multisig, used exclusively for that multisig's operations

### ms-3.1.3 — Seed Phrase Backup and Protection
**Q:** Do you securely back up and protect signer seed phrases and recovery materials?

**Baselines:**
- Seed phrases never stored digitally, in cloud storage, or photographed
- Backups are geographically distributed (disaster resistant)
- No single point of compromise (theft resistant)
- Recoverable if one operator is unavailable (operator-loss resistant)

### ms-3.1.4 — Signer Lifecycle Management
**Q:** Do you have a defined process for adding, removing, and periodically verifying signers?

**Baselines:**
- Offboarded signers removed within 48-72 hours (Emergency-class), 7 days (Critical-class), 14 days (others)
- Access reviews quarterly, confirming each signer still controls their key

### ms-3.1.5 — Signer Training and Assessment
**Q:** Are signers trained and assessed on security practices before they are authorized to sign?

**Baselines:**
- Training covers transaction verification, emergency procedures, phishing and social engineering awareness
- Practical skills assessment included
- Annual refreshers; updates within 30 days of significant procedure changes

### ms-3.1.6 — Hardware Wallet Standards
**Q:** Do you define and enforce hardware wallet standards for multisig operations?

**Baselines:**
- Wallet capability requirements include adequate display, clear signing support, PIN security, and firmware integrity verification
- Procurement through verified supply chains (direct from manufacturer or authorized resellers), with device authenticity verification

### ms-3.1.7 — Secure Signing Environment
**Q:** Do signers use a secure environment for signing operations?

**Baselines:**
- Device security requirements documented and enforced
- Dedicated signing devices or network isolation for high-value operations

### ms-3.1.8 — Signer Diversity
**Q:** Are your signers distributed across roles, entities, and geographies to prevent a single event from compromising quorum?

**Baselines:**
- Diversity requirements scale with multisig classification

## ms-4: Operational Procedures

### ms-4.1.1 — Transaction Handling Process
**Q:** Do you have a defined, documented process for how transactions are proposed, verified, and executed?

**Baselines:**
- Process covers initiation, approval, simulation, execution, and confirmation
- Defines who is authorized to initiate transactions
- Each signer independently verifies transaction details (chain ID, target address, calldata, value, nonce, operation type) before signing
- Transaction hashes compared across at least two independent interfaces (e.g., web UI and CLI, or web and mobile app)
- DELEGATECALL operations to untrusted addresses flagged as high risk
- High-risk transactions (large transfers, emergency actions, protocol changes) require waiting periods where feasible and elevated threshold approval
- High-risk thresholds defined based on classification and reviewed periodically
- Private transaction submission used when appropriate to prevent front-running or MEV extraction

### ms-4.1.2 — Transaction Audit Trails
**Q:** Do you keep records of all transaction reviews, approvals, and executions?

**Baselines:**
- Retained for 3 years
- Records include proposer, approvers, verification evidence, timestamps, and issues encountered

### ms-4.1.3 — Tool and Platform Evaluation
**Q:** Do you vet the tools and platforms used for multisig operations before adoption?

**Baselines:**
- Evaluation considers whether tools are open source or audited by 2+ reputable firms, have no known critical unpatched vulnerabilities, and have established ecosystem adoption
- Formal process for adopting new tools

### ms-4.1.4 — Backup Signing Infrastructure
**Q:** Do you have backup infrastructure in case your primary signing tools are unavailable?

**Baselines:**
- Alternate signing UI
- 2-3 backup RPC providers
- Alternate block explorer

## ms-5: Communication & Coordination

### ms-5.1.1 — Secure Communication Procedures
**Q:** Do you have secure communication procedures for multisig operations, including standard identity verification?

**Baselines:**
- Dedicated primary and backup channels on different platforms
- End-to-end encryption, MFA required, invitation-based membership
- Signer identity verified as standard procedure during signing operations (e.g., code words, video call, secondary authenticated channel)
- Documented procedures for channel compromise including switching to backup channels and out-of-band verification
- All signers trained on these procedures; compromise response tested annually

### ms-5.1.2 — Emergency Contact List
**Q:** Do you maintain a current emergency contact list for all multisig stakeholders?

**Baselines:**
- Includes protocol security team, external security resources, legal/compliance contacts, and backup contacts for signers
- Personal emergency contacts for each signer (e.g., trusted family member, close colleague) for situations where the signer is unreachable through normal channels
- Reviewed every 6 months

## ms-6: Emergency Operations

### ms-6.1.1 — Emergency Playbooks
**Q:** Do you have step-by-step emergency playbooks?

**Baselines:**
- Scenarios covered include key compromise, lost access, communication channel compromise, and urgent protocol actions
- Each scenario has procedures and escalation paths
- Playbooks accessible through at least one backup method independent of the primary documentation platform

### ms-6.1.2 — Signer Reachability and Escalation
**Q:** Can you reach enough signers to meet quorum at any time, including outside business hours?

**Baselines:**
- Response times by classification - Emergency less than 2 hours, Time-Sensitive 2-12 hours, Routine 24-48 hours
- Paging covers all signers including external parties
- Tested quarterly
- Escalation paths documented

### ms-6.1.3 — Multisig Monitoring and Alerts
**Q:** Do you monitor all multisigs for unauthorized or suspicious activity?

**Baselines:**
- Monitored events include signer/threshold changes, transfers exceeding thresholds, nonce gaps, interactions with unknown addresses, failed transactions, module/guard changes, and low submitter/proposer balances
- Alerting and escalation paths documented
- Monitoring infrastructure protected against tampering

### ms-6.1.4 — Emergency Drills and Improvement
**Q:** Do you regularly rehearse your emergency procedures and track improvements?

**Baselines:**
- Annual minimum
- After major procedure changes
- Documentation includes date, participants, response times, issues identified, and improvements made
