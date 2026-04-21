          } from "../../../components";

# Enhanced Controls for High-Risk Accounts

For Critical and High impact custodial accounts, implement the following controls in addition to baseline measures.

---

## Transaction Verification

- Test transactions: Send maximum $100 to new addresses before executing full transaction
- Multi-channel confirmation: Request via one channel, approve via separate channel
- Simulation requirement: All transactions must be simulated before execution
- Address verification: Verify new addresses against three independent sources

For DeFi interactions: refer to the [DeFi Risk Assessment Guide](https://entethalliance.org/specs/defi-risks/v1/) for recommended procedures.

## Access Security

- Hardware security keys (FIDO2/WebAuthn) mandatory for all approvers
  - Secure fallback: Each approver must register minimum 2 hardware keys stored in separate secure locations
  - Key loss procedure: Temporary access via backup key + additional approver verification via multiple channels + mandatory key replacement within 48 hours
- IP whitelisting with 24-hour change approval delay - if treasury software supports application-level IP whitelisting, restrict to VPN IP range only
- Device fingerprinting with new device approval process
- Session timeout and re-authentication for sensitive operations
- Dedicated credentials: Use separate email addresses and passwords exclusively for custody access, not shared with other corporate systems

## Device Security

- Dedicated secure workstations and mobile devices for custody access only (no general browsing, email, or other corporate activities)
- Network isolation on separate VLAN/segment
- VPN mandatory for all platform access; if treasury platform supports it, configure IP whitelisting to only allow access from VPN IP addresses
- Full disk encryption with automatic screen lock
- MDM-enforced security baseline with remote wipe capability
- Mobile endpoint security monitoring (e.g., iVerify) for devices used as second factors or keystores, without requiring full MDM admin control

## MPC for Large Holdings

For organizations managing >10% of total assets or >$10M equivalent in a single custodial account consider using MPC:

- Evaluate MPC (Multi-Party Computation) custody solutions that distribute key material across multiple parties
- Consider threshold signature schemes (e.g., 3-of-5 or 5-of-9) where no single party controls sufficient key shares
- Implement geographic distribution of key share holders across multiple jurisdictions
- Establish clear key refresh and rotation procedures
- Document recovery procedures and test annually

### Custody/MPC Policy Thresholds for Treasury Operations

- Minimum of 3 distinct approvers across roles (e.g., Treasury, Security, Finance)
- Target majority approval (≥50% of designated approver group; e.g., 3/5, 4/7)
- Scale quorum size with assets-at-risk and operational blast radius
- Enforce separation of duties: requester cannot be an approver; admins cannot unilaterally execute withdrawals

Policy scope definitions (examples):

- Emergency Freeze: Temporarily block withdrawals/policy changes across workspaces
- Protocol Parameters: Custody/policy engine settings, risk rules, policy changes
- Capital Allocation: Movements between accounts, exchanges, or strategies
- Treasury – Large: Routine treasury transfers above internal threshold or rate limit
- Treasury – Small: Routine operational transfers below internal threshold or rate limit
- Constrained DeFi: Time-sensitive interactions with pre-approved protocols/contracts

Suggested approver thresholds (treasury contexts):

| Operation            | Impact   | Urgency        | Approver Threshold            |
| -------------------- | -------- | -------------- | ----------------------------- |
| Emergency Freeze     | Critical | Emergency      | 2/4                           |
| Protocol Parameters  | High     | Routine        | 4/7 (7/9+ for upgrades)       |
| Capital Allocation   | High     | Time-Sensitive | 3/5                           |
| Treasury - Large     | High     | Routine        | 4/7                           |
| Treasury - Small     | Medium   | Routine        | 3/5                           |
| Constrained DeFi     | Medium   | Time-Sensitive | 2/3                           |

## Custody Policy Engine Rules

Most custody/MPC platforms provide a policy engine that evaluates transaction rules and takes one of three actions: allow, block, or require additional approvals.

Core rule elements:

- Action: allow | block | escalate (require more approvers)
- Asset selector: all assets or specific assets/tokens
- Amount limits: per-transaction limit and optional rolling window aggregation
- Source and destination selectors: account/wallet groups, internal vs external addresses, exchanges
- Transaction type: transfers, contract interactions, approvals/signing
- Initiators and approvers: who can initiate and who must authorize (with thresholds)
- Rule identity and ordering: each rule has an ID; engines typically evaluate rules in order (first-match wins)

## Zero Trust Architecture Alternative

A Zero Trust architecture involves continuous verification of user, device, and context, rather than reliance on a single perimeter or network location. Centralizing access through a secure environment (such as a bastion host or isolated cloud workspace) can support Zero Trust principles when combined with strong identity and device posture enforcement.

- Bastion Host Approach: Deploy a hardened jump server that acts as the sole gateway to custody platforms.
  - All custody sessions route through the bastion with full session recording
  - Bastion enforces MFA, device posture checks, and approved software versions
  - No direct custody access from employee devices
  - Centralized patch management and security configuration
  
- Cloud Workspace Isolation: Use browser-isolated or virtual workspace environments (e.g., Citrix, AWS WorkSpaces, Azure Virtual Desktop)
  - Custody access occurs only within a controlled virtual environment
  - Copy/paste and download restrictions prevent data exfiltration
  - Session timeout and automatic workspace destruction after use
  - Significantly reduces risk from compromised employee devices

## Security Monitoring & Logging

For Critical and High impact accounts, implement centralized security monitoring:

- SIEM Deployment: Deploy SIEM to centralize logs from custody platforms, authentication systems, and access devices. Create real-time correlation rules for suspicious patterns (failed authentication, geographic anomalies, policy changes).

- Internal Incident Response: Build dedicated incident response capability for custody-related security events. Define clear escalation procedures, maintain 24/7 on-call rotation for Critical accounts, and establish playbooks for custody compromise scenarios.

- Essential Log Sources: Authentication events, transaction attempts, policy modifications, access changes, whitelist updates, IP address changes, new device enrollments, and approval workflows.

For Medium and Low impact accounts, leverage custodian's native audit logs with weekly manual review and automated alerting for critical events (new device enrollment, policy changes, transactions above threshold).

---

### See also

- Classification: [Custodial Treasury Security: Classification Framework](./classification)
- Templates: [Registration Documents](./registration-documents)

