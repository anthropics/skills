---
name: opsec-advisor
description: Guide on operational security (opsec) for individuals and Web3 organizations. Use when users ask about personal security practices, threat modeling, travel security, protecting sensitive information, device hardening, or reducing digital footprint. Triggers on questions about "opsec practices," "travel security," "threat modeling," "protecting my identity," or "security while traveling."
---

# Operational Security Advisor

Help individuals and organizations protect sensitive information through systematic operational security practices.

## What is OpSec?

Operational Security is a systematic process to:
1. Identify critical information and assets
2. Analyze threats to those assets
3. Discover vulnerabilities
4. Evaluate risks in business context
5. Deploy targeted countermeasures

**Goal**: Prevent unauthorized access to information that could cause operational, financial, or reputational harm.

## Core Principles

| Principle | Description |
|-----------|-------------|
| Defense in Depth | Multiple overlapping security controls |
| Least Privilege | Only permissions needed for function |
| Need-to-Know | Information only to those requiring it |
| Compartmentalization | Isolate systems/info to contain breaches |
| Continuous Monitoring | Ongoing security posture awareness |

## Threat Modeling Framework

### 1. Asset Inventory
Categorize what you're protecting:
- **Digital value stores**: Crypto, tokens, NFTs
- **Credentials**: Passwords, API keys, private keys, seeds
- **Hardware**: Laptops, phones, hardware wallets, YubiKeys
- **Infrastructure**: Cloud resources, repos, networks
- **Sensitive info**: Code, customer data, business docs
- **Legal assets**: Certificates, contracts, compliance docs

### 2. Adversary Analysis

| Tier | Who | Capabilities |
|------|-----|--------------|
| Tier 1 | Script kiddies, opportunists | Public exploits, basic phishing |
| Tier 2 | Organized crime, competitors | Custom malware, spear phishing |
| Tier 3 | Nation-states, APT groups | Zero-days, supply chain attacks |

### 3. Attack Vector Mapping
- **Technical**: Vulnerability exploitation, network attacks
- **Social**: Phishing, social engineering, insider threats
- **Physical**: Device theft, office intrusion, tampering
- **Operational**: SIM swapping, supply chain, third-party breaches

## STRIDE Threat Categories

| Category | Security Property | Web3 Example |
|----------|------------------|--------------|
| **S**poofing | Authentication | Wallet credential phishing |
| **T**ampering | Integrity | Smart contract manipulation |
| **R**epudiation | Non-repudiation | Disputing tx authorization |
| **I**nfo disclosure | Confidentiality | Private key extraction |
| **D**enial of service | Availability | Network congestion attacks |
| **E**levation | Authorization | Exploiting admin functions |

## Travel Security Quick Reference

### Before Travel
- [ ] Full disk encryption enabled
- [ ] Devices updated to latest OS
- [ ] Backup all devices
- [ ] Export 2FA backup codes
- [ ] Enable password manager travel mode
- [ ] Disable biometrics (use PIN only)
- [ ] No seed phrases - leave at home
- [ ] Hardware wallet firmware updated

### During Travel
- [ ] Use cellular/hotspot over public WiFi
- [ ] VPN for any network use
- [ ] Devices never unattended
- [ ] Privacy screen on laptop
- [ ] No crypto branding visible
- [ ] Separate hardware wallet from laptop
- [ ] Avoid public USB charging (juice jacking)

### After Travel
- [ ] Run malware scans
- [ ] Change passwords used on trip
- [ ] Review account activity
- [ ] Consider device wipe if high-risk
- [ ] Update threat model based on experience

## Control Domains

### Organizational Controls
- Security policies and governance
- Compliance and regulatory alignment
- Supply chain security
- Third-party risk management

### People Controls
- Security awareness training
- Insider threat mitigation
- Social engineering defense
- Security culture building

### Physical Controls
- Secure workspace practices
- Travel security protocols
- Tamper evidence measures
- Device physical security

### Technical Controls
- Device hardening
- Network security
- Encrypted storage and backups
- Hardware authentication (2FA/MFA)
- Cryptocurrency-specific controls

## Personal OpSec Checklist

### Digital Identity
- [ ] Unique passwords per service
- [ ] Hardware 2FA on critical accounts
- [ ] Separate 2FA from password manager
- [ ] Email aliases for registrations
- [ ] Review and revoke old app permissions

### Communication
- [ ] E2E encrypted messaging (Signal)
- [ ] Verify recipient before sensitive info
- [ ] Assume unencrypted comms are public
- [ ] Separate work and personal accounts

### Social Media
- [ ] Minimize public personal info
- [ ] Don't announce travel in real-time
- [ ] No crypto holdings disclosure
- [ ] Private account settings by default

### Device Security
- [ ] Full disk encryption
- [ ] Auto-lock short timeout
- [ ] Remote wipe capability
- [ ] Regular OS and app updates
- [ ] No untrusted USB devices

## Web3-Specific Considerations

- **Transparency vs Privacy**: Balance blockchain transparency with operational secrecy
- **Decentralized Operations**: Secure operations across distributed teams
- **Crypto Security**: Private key and seed phrase protection
- **Smart Contract Risks**: Immutable code requires extra caution
- **Community Dynamics**: Security in open, community-driven projects

## Reference Files

- See `references/threat-modeling-guide.md` for detailed threat modeling process
- See `references/travel-security.md` for comprehensive travel security guide
