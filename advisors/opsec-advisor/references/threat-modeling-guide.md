# Threat Modeling Guide

## Why Threat Model?

Without structured threat modeling, security becomes unfocused and inefficient. Notable failures:
- **ByBit $1.5B Hack (2025)**: Could have been prevented with proper threat modeling
- **Ronin Bridge $620M (2022)**: Lazarus Group targeted blockchain infrastructure
- **Nomad Bridge $190M (2022)**: Vulnerability allowed bypassing transaction validation
- **Twitter 2020**: High-profile accounts hijacked for crypto scams

## Common Pitfalls

| Pitfall | Example | Solution |
|---------|---------|----------|
| Tunnel vision | Colonial Pipeline focused on OT, ignored VPN | Comprehensive asset mapping |
| Unrealistic scenarios | Over-invest in zero-day, ignore phishing | Prioritize by likelihood |
| Static models | Equifax breach from outdated model | Quarterly reviews |
| Insider blindness | Twitter admin tools not modeled | Include all access paths |

## Step-by-Step Process

### Step 1: Asset Inventory

Document everything that would cause harm if compromised:

```
Asset Categories:
├── Digital Value Stores
│   ├── Cryptocurrencies and tokens
│   ├── NFTs and digital collectibles
│   └── Test tokens on testnets
├── Credentials & Access
│   ├── Multi-sig wallet configs
│   ├── Password manager accounts
│   ├── Recovery seed phrases
│   ├── SSH keys
│   └── API keys
├── Hardware & Devices
│   ├── Laptops (encrypted drives)
│   ├── Mobile devices
│   ├── Hardware wallets
│   ├── YubiKeys
│   └── Physical access controls
├── Infrastructure
│   ├── Cloud resources (AWS, GCP)
│   ├── Code repositories
│   ├── CI/CD pipelines
│   └── Communication tools
├── Sensitive Information
│   ├── Source code
│   ├── Client data
│   ├── Financial records
│   └── Business strategy
└── Legal & Compliance
    ├── Contracts and NDAs
    ├── Regulatory documentation
    └── Security audit reports
```

### Step 2: Adversary Analysis

Classify potential attackers:

**Tier 1 - Opportunistic**
- Who: Script kiddies, automated scanners
- Motivation: Quick financial gain, reputation
- Capabilities: Public exploits, basic phishing
- Targets: Public infrastructure, known vulnerabilities

**Tier 2 - Targeted**
- Who: Organized crime, competitors, ex-employees
- Motivation: Financial theft, competitive advantage, revenge
- Capabilities: Custom malware, spear phishing, persistent attacks
- Targets: Treasury wallets, intellectual property, credentials

**Tier 3 - Advanced**
- Who: Nation-states (Lazarus Group), APT groups
- Motivation: Strategic intelligence, large-scale theft
- Capabilities: Zero-days, supply chain attacks, long-term persistence
- Targets: All high-value assets, infrastructure access

### Step 3: Attack Vector Mapping

For each critical asset, document potential attack paths:

**Example: Treasury Wallet**

| Vector | Description | Adversary Tier | Likelihood |
|--------|-------------|----------------|------------|
| Phishing | Targeted emails for credentials | 1-2 | High |
| Social engineering | Manipulating employees | 2 | Medium |
| Supply chain | Compromised wallet software | 3 | Low |
| Insider threat | Employee with access | 2 | Medium |

**Example: Source Code**

| Vector | Description | Adversary Tier | Likelihood |
|--------|-------------|----------------|------------|
| GitHub compromise | Developer credential theft | 1-3 | Medium |
| CI/CD injection | Malicious code in pipeline | 3 | Low |
| Developer machine | Local environment compromise | 2-3 | Medium |

### Step 4: Risk Assessment

Combine likelihood and impact:

```
Risk = Likelihood × Impact

Risk Matrix:
              │ Low Impact │ Med Impact │ High Impact │
──────────────┼────────────┼────────────┼─────────────┤
High Likely   │   Medium   │    High    │  Critical   │
Med Likely    │    Low     │   Medium   │    High     │
Low Likely    │    Low     │    Low     │   Medium    │
```

### Step 5: Countermeasure Implementation

Prioritize controls based on risk:

**Critical Risk**: Implement immediately
- Hardware 2FA on all privileged accounts
- Multi-sig for treasury operations
- Security awareness training

**High Risk**: Implement within 30 days
- Regular permission audits
- Endpoint detection tools
- Encrypted communications

**Medium Risk**: Implement within 90 days
- Enhanced logging
- Third-party security reviews
- Incident response planning

## Attack Tree Visualization

```
Goal: Steal crypto assets
├── Compromise user wallet
│   ├── Phishing attack
│   │   └── Mitigate: Security awareness training
│   └── Malware infection
│       └── Mitigate: Endpoint protection
├── Attack exchange/protocol
│   ├── API key theft
│   │   └── Mitigate: IP restrictions, 2FA
│   └── Credential stuffing
│       └── Mitigate: Unique passwords, MFA
└── SIM swapping
    └── Mitigate: Hardware keys, non-SMS 2FA
```

## When to Update Threat Model

| Trigger | Description |
|---------|-------------|
| Initial development | Before launching any crypto project |
| Regular reviews | Quarterly or with significant changes |
| After incidents | Any security breach or near-miss |
| Team changes | Onboarding/offboarding key personnel |
| New integrations | Adding external protocols or services |
| Major releases | Before deploying significant updates |

## Role-Specific Responsibilities

- **Security specialists**: Lead threat modeling, provide threat intelligence
- **Operations**: Contribute infrastructure knowledge, implement controls
- **Developers**: Identify code-level vulnerabilities, secure development
- **HR/Management**: Address insider threats, security training
- **Community/Marketing**: Reputation risks, public-facing attack surfaces
