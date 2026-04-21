          } from "../../../components";

# Planning & Classification

Before setting up a new multisig, take time to properly assess its role and requirements. This planning phase will guide all subsequent configuration decisions and help ensure appropriate security measures.

## Before You Start

### Define Purpose and Scope

Document the multisig's intended use:

- **Primary function** - What will this multisig do?
- **Asset types and amounts** - What will it control?
- **Operational frequency** - How often will it be used?
- **Decision timeline** - How quickly must it respond?
- **Integration points** - What systems will it interact with?

### Assess Constraints and Recovery

Consider limiting factors that affect risk:

- **Smart contract constraints** - What technical limits reduce risk?
- **Governance recovery** - Can governance override or recover funds?
- **Operational limits** - Are there built-in spending or parameter limits?
- **Backup mechanisms** - What happens if this multisig fails?

### Identify Stakeholders

Determine who should be involved:

- **Required expertise** - What knowledge is needed for decisions?
- **Geographic distribution** - Do you need global coverage?
- **External signers** - Should independent parties be involved?
- **Backup signers** - Who can step in if primary signers are unavailable?

## Classification Process

Use this dual classification system to determine appropriate security measures. These classifications are guidance to help you think through risk levels - they inform threshold selection, signer requirements, and operational procedures in later sections.

### Step 1: Impact Assessment

What happens if this multisig is compromised or fails?

#### Financial Exposure:

- Direct funds controlled by the multisig
- Indirect exposure through protocol impacts
- Maximum potential loss in worst-case scenario

#### Protocol Impact:

- Can the protocol function without this multisig?
- How difficult would recovery be?
- Are there alternative execution paths?

#### Reputational Risk:

- How visible is this multisig to the community?
- What would compromise mean for the protocol's reputation?
- Are there regulatory or compliance considerations?

#### Impact Classification

| Level        | Financial Exposure     | Protocol Impact                                       | Reputational Risk             |
| ------------ | ---------------------- | ----------------------------------------------------- | ----------------------------- |
| **Low**      | \<$100k direct exposure | Minimal disruption, alternative paths exist           | Limited scope impact          |
| **Medium**   | $100k - $1M exposure   | Significant operational delays, workarounds available | Moderate reputational concern |
| **High**     | $1M - $10M exposure    | Major protocol disruption, difficult recovery         | Serious reputational damage   |
| **Critical** | \>$10M exposure         | Protocol-wide failure, catastrophic impact            | Severe reputational damage    |

### Step 2: Operational Assessment

How quickly and under what conditions must this multisig respond?

#### Response Time Requirements:

- How quickly must decisions be made?
- What are the consequences of delays?
- Are there market or competitive timing factors?

#### Decision Context:

- Are operations routine and predictable?
- Do market conditions affect timing?
- Is this primarily for emergency response?

#### Coordination Complexity:

- How many parties must coordinate?
- Are signers distributed globally?
- What communication is required?

#### Operational Classification

| Type               | Response Time | Decision Context                             | Verification Level               |
| ------------------ | ------------- | -------------------------------------------- | -------------------------------- |
| **Routine**        | 24-48 hours   | Standard procedures, predictable operations  | Full verification protocols      |
| **Time-Sensitive** | 2-12 hours    | Market conditions, protocol needs            | Streamlined but thorough         |
| **Emergency**      | \<2 hours      | Crisis response, preventing immediate damage | Minimal delays, risk-appropriate |

### Step 3: Classification Matrix

Combine your impact and operational assessments. Below are some example configurations.

| Use Case            | Impact   | Operational    | Standard Threshold |
| ------------------- | -------- | -------------- | ------------------ |
| Emergency Freeze    | Critical | Emergency      | 2/4                |
| Protocol Parameters | High     | Routine        | 4/7 (higher for upgrades, consider 7/9+) |
| Capital Allocation  | High     | Time-Sensitive | 3/5                |
| Treasury - Large    | High     | Routine        | 4/7                |
| Treasury - Small    | Medium   | Routine        | 3/5                |
| Constrained DeFi    | Medium   | Time-Sensitive | 2/3                |

### Step 4: Document Your Decision

Record your classification decision in the [Registration template](/multisig-for-protocols/registration-and-documentation#registration-template).

## Important Notes

⚠️ **When between classifications**: Always err toward higher security requirements. Classifications can be relaxed with proper justification, but security incidents cannot be undone.

This classification will guide your threshold selection ([Thresholds & Configuration](/wallet-security/secure-multisig-best-practices#thresholds--configuration)), signer requirements, and operational procedures throughout the rest of the documentation.

## Next Steps

After completing classification, proceed to:

1. [Setup & Configuration](/multisig-for-protocols/setup-and-configuration) - Deploy your multisig
2. [Registration & Documentation](/multisig-for-protocols/registration-and-documentation) - Document your setup

