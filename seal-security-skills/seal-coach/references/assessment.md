# SEAL Readiness Assessment

Flexible assessment approach — conversational, not a quiz. Adapt to user context.

## Pre-Assessment (always do first)

Before diving into domains, ask:

1. **What does your organization do?** (protocol, exchange, wallet provider, DAO, etc.)
2. **What's your role?** (dev, ops, founder, security lead, etc.)
3. **What keeps you up at night?** (their biggest fear/concern)
4. **Have you had incidents before?** (context for urgency)
5. **What's your team size?** (solo dev vs 50-person org changes everything)

Skip domains that don't apply based on answers.

## Quick Scan (5 questions)

For users who want a fast triage. One question per cluster:

| # | Question | Maps To |
|---|----------|---------|
| 1 | "If your main wallet or signing key was compromised right now, what would happen?" | wallet-security, multisig, iam |
| 2 | "If someone on your team got phished tomorrow, what's the worst case?" | awareness, incident-management, user-team-security |
| 3 | "How do you handle dependencies and code deployments?" | devsecops, supply-chain, secure-software-development |
| 4 | "Do you have monitoring or alerting for suspicious activity?" | monitoring, infrastructure, security-automation |
| 5 | "Who decides what's acceptable risk, and how?" | governance, opsec, treasury-operations |

Map answers to readiness bands and recommend priority domains.

## Readiness Bands

Not pass/fail. Four bands that show trajectory:

| Band | Meaning | Typical Signs |
|------|---------|---------------|
| **Critical** | Major gaps, high risk exposure | No incident plan, shared keys, no monitoring |
| **Developing** | Some controls, inconsistent execution | Basic auth but no MFA, informal processes |
| **Established** | Solid foundation, room for optimization | Documented procedures, regular reviews |
| **Advanced** | Industry-leading, continuous improvement | Automation, red-teaming, proactive threat hunting |

## Domain Deep-Dive Questions

When user wants to go deeper on a specific domain, use these conversational starters.
Don't ask all of them — pick 3-4 most relevant.

### Wallet Security
- What type of wallets do you use? (EOA, multisig, smart contract)
- How are private keys stored? (HSM, cloud KMS, local, seed phrase)
- Who has access to signing, and how is it audited?
- Do you have key rotation procedures?

### Incident Management
- Do you have a written incident response plan?
- Who's on the incident team, and do they practice?
- How would you detect a breach right now?
- Do you have relationships with security firms (SEAL 911, etc.)?

### IAM (Identity & Access Management)
- How do people authenticate? (SSO, MFA, passwords)
- How are permissions granted and revoked?
- Do you audit access regularly?
- What happens when someone leaves the team?

### DevSecOps
- Do you run security tests in CI/CD?
- How do you manage secrets in code?
- Do you have code review requirements for security-sensitive changes?
- How do you handle dependency updates?

### Governance
- Who owns security decisions?
- Is there a documented risk management process?
- How do you decide what to spend on security?
- Do you have regular security reviews?

### Monitoring
- What are you monitoring right now?
- How do you detect anomalies?
- Who gets alerts, and how fast do they respond?
- Do you log security-relevant events?

### Supply Chain
- How do you vet dependencies?
- Do you pin versions or use lockfiles?
- Have you audited your build pipeline?
- Do you verify artifact provenance?

### Threat Modeling
- Have you done a formal threat model?
- Do you know your attack surface?
- How do you prioritize security work?
- When did you last review threats?

### OpSec
- Do team members use separate accounts for work vs personal?
- How do you handle sensitive information sharing?
- Are communications encrypted?
- Do you have operational security guidelines?

### Encryption
- What's encrypted at rest? In transit?
- How do you manage encryption keys?
- Do you use end-to-end encrypted comms?
- Is disk encryption enforced on team devices?

## Scoring Approach

After assessment, summarize as:

```
Domain Readiness:
  wallet-security:      Developing → needs multisig + key rotation
  incident-management:  Critical → no plan exists
  iam:                  Established → MFA in place, needs access reviews
  devsecops:            Developing → CI/CD exists, no security gates
  
Priority: incident-management (highest risk), then wallet-security
```

Frame gaps as opportunities: "Here's where small changes have big impact" not "you're failing at X."
