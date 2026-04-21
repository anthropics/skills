          } from "../../../components";

# Custodial Treasury Security: Classification Framework

Proper documentation and classification of custodial accounts is essential for institutional treasury security. This guide focuses on the security assessment and classification framework for crypto assets held with third-party custodians.

> See also: [Registration Documents](./registration-documents) and [Enhanced Controls for High-Risk Accounts](./enhanced-controls)

## Classification Process

Use this dual classification to determine appropriate security controls for each custodial account.

### Step 1: Impact Assessment

Evaluate the consequences if this account is compromised or unavailable.

#### Financial Impact

Calculate the total value at risk in this account:

- Current market value of all assets held
- Include value of any active positions (e.g., staked assets, DeFi deposits)
- What is the financial impact if unavailable for 7 days?

#### Operational Impact

Assess the consequences if this account becomes unavailable:

- What specific operations require this account?
- Do you have a secondary custody account that can handle these operations?
- What is the reputational impact if this account is compromised or unavailable?

#### Regulatory Impact

Evaluate regulatory and compliance consequences:

- Are assets in this account subject to regulatory reporting requirements (SEC filings, audit requirements)?
- Does this account hold regulated assets (e.g., stablecoins subject to reserves reporting)?
- What are the regulatory deadlines that could be missed if this account is unavailable?

#### Impact Classification

| Level        | Financial Exposure (% of Total Assets) | Operational Dependency                       | Regulatory Impact                                    |
| ------------ | -------------------------------------- | -------------------------------------------- | ---------------------------------------------------- |
| **Low**      | \<1%                                   | No critical operations depend on it          | No regulatory reporting tied to this account         |
| **Medium**   | 1% - 10%                               | Important but alternative funding available  | Periodic reporting; delays manageable                |
| **High**     | 10% - 25%                              | Critical operations, limited alternatives    | Regular regulatory filings; delays cause violations  |
| **Critical** | \>25%                                  | Business-critical, no alternatives for weeks | Real-time reporting requirements; SEC filings; audit |

### Step 2: Operational Assessment

Evaluate how frequently and urgently this account must be accessed.

#### Transaction Frequency

Document typical transaction patterns:

- Transactions per month
- Typical transaction sizes
- Predictability of transaction timing

#### Access Urgency

Define response time requirements:

- What is the maximum acceptable delay for routine transactions?
- Are there scenarios requiring same-day execution?
- What are the consequences of 24-hour, 72-hour, or 7-day delays?

#### Coordination Requirements

Assess how transactions are executed:

- How many approvers are needed for typical transactions?
- Are transactions handled manually or through automated systems?
- Do approvers need to coordinate across timezones?

Note: Single-approver configurations should only be used for low-value operational accounts (\<0.1%) with additional compensating controls like strict spending limits and daily reconciliation.

#### Operational Classification

| Type                  | Frequency     | Response Window | Example Use Cases                                  |
| --------------------- | ------------- | --------------- | -------------------------------------------------- |
| **Cold Vault**        | \<5 tx/month  | 48-72 hours     | Long-term reserves, infrequent rebalancing         |
| **Warm Storage**      | 5-50 tx/month | 4-24 hours      | Scheduled payments, planned operations             |
| **Active Operations** | \>50 tx/month | \<4 hours       | Trading capital, frequent operational expenses     |
| **Time-Critical**     | Unpredictable | \<2 hours       | Collateral management, market-sensitive operations |

### Step 3: Security Control Matrix

Combine impact and operational assessments to determine required controls.

| Use Case                      | Impact      | Operational   | Approvers | MFA Requirement    | Whitelist Delay | Additional Controls                         |
| ----------------------------- | ----------- | ------------- | --------- | ------------------ | --------------- | ------------------------------------------- |
| Payments                      | Low         | Active Ops    | 2         | Standard TOTP      | 6 hours         | **Baseline (all accounts):** Dedicated devices for custody access, address whitelisting enabled, test small amount to new addresses before full transaction, transaction simulation. **Low-specific:** Per-transaction cap, monthly aggregate limit         |
| Operational Wallet            | Medium      | Active Ops    | 2         | Hardware required  | 12 hours        | All Low controls + daily transaction caps, weekly reconciliation, monthly audit                    |
| Liquidation Protection        | Medium-High | Time-Critical | 2         | Hardware required  | None            | All Low/Medium controls + automated alerts for position health, real-time monitoring |
| DeFi Positions                | Medium-High | Warm Storage  | 3         | Hardware mandatory | 24 hours        | All Low/Medium controls + smart contract whitelist, position monitoring, daily reconciliation     |
| Trading Capital (variable)    | High        | Active Ops    | 3         | Hardware mandatory | 6 hours         | All Low/Medium controls + smart contract whitelist, real-time monitoring, daily reconciliation   |
| Active Treasury (5-10%)       | High        | Warm Storage  | 3-4       | Hardware mandatory | 24 hours        | All Low/Medium controls + transaction velocity limits, SIEM monitoring， multi-channel confirmation       |
| Secondary Reserve (10-25%)    | Critical    | Cold Vault    | 4-5       | Hardware mandatory | 48 hours        | All Low/Medium/High controls + geographic distribution of approvers, MPC recommended    |
| Primary Reserve (>25% assets) | Critical    | Cold Vault    | 5-7       | Hardware mandatory | 72 hours        | All Low/Medium/High controls + geographic distribution of approvers, MPC recommended    |

### Step 4: Document Your Decision

- Record impact level and operational type with justification
- Capture approver thresholds and required controls
- Store links to relevant custody accounts and addresses

Proceed to: [Registration Documents](./registration-documents)

For Critical/High accounts, ensure you also review: [Enhanced Controls for High-Risk Accounts](./enhanced-controls)

