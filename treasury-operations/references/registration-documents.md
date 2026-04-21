          } from "../../../components";

# Registration Documents

Use these standardized templates to register custodial accounts, track access changes, document security configurations, and perform quarterly reviews.

> See also: [Classification Framework](./classification) and [Enhanced Controls for High-Risk Accounts](./enhanced-controls)

---

## Registration Template

Use this template when initially documenting a custodial account.

```
CUSTODIAL ACCOUNT REGISTRATION

Account Name: [Descriptive name]
Custodian: [Provider name and legal entity]
Account ID: [Custodian reference number]
Network(s): [Bitcoin, Ethereum, etc.]
Registration Date: YYYY-MM-DD
Registered By: [Name]

CLASSIFICATION
Impact Level: [Low / Medium / High / Critical]
Operational Type: [Cold Vault / Warm Storage / Active Operations / Time-Critical]

Justification:
- Financial exposure: $XXX,XXX,XXX
- Operational dependency: [Description]
- Recovery time objective: [X hours/days]

ASSETS CONTROLLED
Asset   | Network  | Value     | Purpose
--------|----------|-----------|------------------------------
BTC     | Bitcoin  | $XXX,XXX  | [Reserve/Trading/Operations]
ETH     | Ethereum | $XXX,XXX  | [Reserve/Trading/Operations]
USDC    | Ethereum | $XXX,XXX  | [Reserve/Trading/Operations]

CUSTODY MODEL
Type: [Qualified Custodian / Co-managed / MPC Platform]
Key Management: [MPC 3-of-5 / Multi-sig 2-of-3 / HSM]
Key Control: [Custodian only / Co-managed / Client-controlled]
Recovery Capability: [Yes - describe / No]

INITIAL ACCESS SETUP
Primary Administrator: [Name, added YYYY-MM-DD]
Initial Approvers: [Names, added YYYY-MM-DD]

Note: Complete access details documented in Access Change Template
Note: Security configuration documented in Security Configuration Template

ATTESTATION
This account [meets / deviates from] security standards for its classification.

[If deviation: Explain gap and compensating controls]

CONTACTS
Security Owner: [Name, email, phone]
Backup Contact: [Name, email, phone]
Custodian Support: [Name, email, phone]

Last Updated: YYYY-MM-DD
Updated By: [Name]
```

---

## Access Change Template

Use this template when modifying user access to a custodial account.

```
CUSTODIAL ACCOUNT ACCESS CHANGE

Account Name: [Name]
Custodian: [Provider]
Account ID: [Reference]
Change Date: YYYY-MM-DD
Changed By: [Name]

ACCESS MODIFICATIONS

Additions:
Name/Role | Access Level | MFA Method     | Justification
----------|--------------|----------------|------------------------------
[Name]    | [Approver]   | [Hardware key] | [Reason for addition]

Removals:
Name/Role | Access Level | Removal Reason
----------|--------------|-------------------------------
[Name]    | [Approver]   | [Personnel change / Security / Other]

Permission Changes:
Name/Role | Old Level | New Level | Justification
----------|-----------|-----------|---------------------------
[Name]    | [Initiator] | [Approver] | [Reason for elevation]

CURRENT ACCESS LIST (after changes)
Name/Role | Level     | MFA Method    | Device ID
----------|-----------|---------------|---------
[Name]    | Admin     | Hardware key  | [ID]
[Name]    | Approver  | Hardware key  | [ID]
[Name]    | Approver  | Hardware key  | [ID]
[Name]    | Initiator | TOTP          | [ID]

VERIFICATION
[ ] All removed users confirmed deactivated in custodian platform
[ ] All new users completed MFA setup
[ ] Access permissions tested and verified
[ ] Emergency contacts updated
[ ] Documentation updated in [location]

APPROVALS
Requested By: _________________ Date: _______
Approved By: _________________ Date: _______
Security Review: _________________ Date: _______

Change Ticket: [Reference number if applicable]
```

---

## Security Configuration Template

Use this template to document detailed security settings. Complete this after initial account registration.

```
CUSTODIAL ACCOUNT SECURITY CONFIGURATION

Account: [Name]
Custodian: [Provider]
Last Configuration Update: YYYY-MM-DD
Configured By: [Name]

AUTHENTICATION SETTINGS

Multi-Factor Authentication:
Role | Primary Method | Backup Method | Enrollment Status
Administrator | Hardware key + biometric | Hardware key + PIN | [Active]
Approver | Hardware key | TOTP + SMS | [Active]
Initiator | Hardware key or TOTP | SMS | [Active]
Viewer | TOTP | SMS | [Active]

Session Controls:
- Timeout: [X minutes]
- Re-auth required for: [High-value transactions, policy changes, user management]
- Concurrent sessions: [Allowed/Blocked]

ACCESS CONTROL

Current User List:
Name/Role | Level    | MFA Method   | Device ID | Added Date
----------|----------|--------------|----------|------------
[Name]    | Admin    | Hardware key | [ID]     | YYYY-MM-DD
[Name]    | Approver | Hardware key | [ID]     | YYYY-MM-DD
[Name]    | Approver | Hardware key | [ID]     | YYYY-MM-DD

Note: Track all access changes using Access Change Template

Approval Thresholds:
Transaction Value (% of Total Assets) | Required Approvers | Time Delay | Additional Requirements
<0.1%          | 1 | None       | MFA
0.1% - 1%   | 3 | 4 hours    | MFA
1% - 10%    | 4 | 24 hours   | Multi-channel confirmation, test transaction
10% - 25%    | 5 | 24 hours   | Multi-channel confirmation, test transaction
>25%           | 7 | 48 hours   | Multi-channel confirmation, test transaction

Separation of Duties:
[ ] Initiators cannot approve own transactions
[ ] Admins cannot unilaterally execute withdrawals
[ ] Minimum [X] unique approvers required

NETWORK RESTRICTIONS

IP Whitelist:
XXX.XXX.XXX.XXX - [Office Location]
XXX.XXX.XXX.XXX - [VPN Range]
XXX.XXX.XXX.XXX - [Backup Location]

Change Approval: [24 hour delay / XX approvers required]
Emergency Override: [Process description]

VPN Requirement: [Mandatory / Optional]
Geographic Restrictions: [Blocked countries/regions]
Device Fingerprinting: [Enabled / Disabled]

TRANSACTION POLICIES

Address Whitelisting:
Status: [Enabled / Disabled]
Current Addresses: [XX addresses]
Addition Process: [XX approvers, YY hour delay]
Review Schedule: [Monthly / Quarterly]

Transaction Limits:
Limit Type        | Amount   | Override Process
------------------|----------|-----------------
Single Transaction | $XXX,XXX | [Authorization required]
Hourly Aggregate   | $XXX,XXX | [Authorization required]
Daily Aggregate    | $XXX,XXX | [Authorization required]
Weekly Aggregate   | $XXX,XXX | [Authorization required]
Monthly Aggregate  | $XXX,XXX | [Authorization required]

Time-Lock Settings:
Change Type                          | Delay Period
-------------------------------------|-------------
New address addition                 | XX hours
Policy modification                  | XX hours
High-value transaction (>$XXX,XXX)   | XX hours

MONITORING & ALERTS

Real-Time Alerts:
Type                       | Enabled
---------------------------|--------
All outgoing transactions  | [ ]
New device login           | [ ]
Failed authentication attempts (>X) | [ ]
Policy violations          | [ ]
Large transactions (>$XXX,XXX) | [ ]
Unusual access times       | [ ]
New geographic location    | [ ]

Alert Routing:
Severity | Contact         | Method       | Response Time
---------|------------------|-------------|--------------
Critical | [Name, phone]   | SMS + Call   | <15 min
High     | [Name, phone]   | SMS + Email  | <1 hour
Medium   | [Name, email]   | Email        | <4 hours

VERIFICATION
[ ] All settings tested and operational
[ ] Alert routing verified
[ ] User access confirmed
[ ] Documentation stored in [location]

Configured By: _________________ Date: _______
Reviewed By: _________________ Date: _______
Approved By: _________________ Date: _______
```

---

## Quarterly Review Template

Use this template for regular security reviews of custodial accounts.

```
CUSTODIAL ACCOUNT QUARTERLY REVIEW

Account: [Name]
Custodian: [Provider]
Review Period: [Q1/Q2/Q3/Q4 YYYY]
Review Date: YYYY-MM-DD
Reviewed By: [Name]

ACCESS AUDIT

Current Users:
Name/Role | Level | Last Login | MFA Status | Action Required
[Name] | Admin | YYYY-MM-DD | Active | None
[Name] | Approver | YYYY-MM-DD | Active | None
[Name] | Approver | Never logged in | Inactive | Remove access

Access Changes This Quarter: [X additions, Y removals, Z modifications]

Findings:
[ ] All users still require current access level
[ ] No dormant accounts (>90 days inactive)
[ ] MFA functioning for all users
[ ] No unauthorized access detected

Actions Required:
- [List any access to be removed/modified]
- [List any policy updates needed]

TRANSACTION REVIEW

Transaction Volume:
- Total transactions: [X]
- Average per month: [Y]
- Largest transaction: $XXX,XXX
- Total outflow: $XXX,XXX

Pattern Analysis:
[ ] Transactions within expected parameters
[ ] No unusual transaction patterns detected
[ ] All large transactions properly authorized
[ ] Test transactions performed correctly

Anomalies Detected:
- [List any unusual activity or violations]

SECURITY CONFIGURATION

Whitelist Review:
- Current addresses: [X]
- Addresses added this quarter: [Y]
- Addresses to remove: [Z]
- Review complete: [Yes/No]

Spending Limits:
Current | Actual Usage | Status
Single: $XXX,XXX | Max: $XXX,XXX | [Appropriate / Adjust]
Daily: $XXX,XXX | Avg: $XXX,XXX | [Appropriate / Adjust]
Monthly: $XXX,XXX | Avg: $XXX,XXX | [Appropriate / Adjust]

Findings:
[ ] Limits appropriate for current usage
[ ] No limit breaches this quarter
[ ] IP whitelist current and accurate
[ ] Time-locks functioning properly

ALERT EFFECTIVENESS

Alerts This Quarter:
Type | Count | False Positive Rate
Critical | [X] | [Y%]
High | [X] | [Y%]
Medium | [X] | [Y%]

Response Times:
Severity | Target | Actual Average | Status
Critical | <15 min | [X min] | [Met/Missed]
High | <1 hour | [X min] | [Met/Missed]
Medium | <4 hours | [X hours] | [Met/Missed]

Findings:
[ ] Alert routing working correctly
[ ] Response times meeting SLAs
[ ] No missed critical alerts

Actions Required:
- [Adjust alert thresholds if needed]
- [Update contact information]

CUSTODIAN RELATIONSHIP

SOC Reports: [Current / Expired - date]
Security Incidents: [Any custodian-wide incidents this quarter]
Service Quality: [Any issues or concerns]
Communication: [Regular contact maintained]

RISK ASSESSMENT UPDATE

Classification Review:
Current: [Impact Level / Operational Type]
Still Appropriate: [Yes / No]

If No, Recommended Change:
New Classification: [Level / Type]
Justification: [Explain change in risk profile]

Asset Value Change: [% increase/decrease]
Operational Change: [Any significant changes in usage]

RECOMMENDATIONS

Security Improvements:
1. [Recommendation]
2. [Recommendation]
3. [Recommendation]

Operational Improvements:
1. [Recommendation]
2. [Recommendation]

ATTESTATION

This account [continues to meet / deviates from] security standards.

[If deviation: Describe and provide remediation plan]

APPROVALS

Reviewer: _________________ Date: _______
Security Officer: _________________ Date: _______
Treasury Lead: _________________ Date: _______

Next Review Due: YYYY-MM-DD
```

---

