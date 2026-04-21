# SEAL Security Knowledge Graph

27 domains from [Security Alliance Frameworks](https://github.com/security-alliance/frameworks).

## Trigger Table

| Keywords | Skill |
|---|---|
| hack, compromised, stolen, breach, drainer | seal-incident-management |
| wallet, seed phrase, hardware wallet, signing | seal-wallet-security |
| phishing, scam, social engineering | seal-awareness |
| DPRK, fake employee, remote worker, hiring | seal-dprk-it-workers |
| encrypt, VPN, TLS, secure comms | seal-encryption |
| code review, CI/CD, supply chain | seal-devsecops |
| threat model, risk assessment | seal-threat-modeling |
| governance, compliance, KPI | seal-governance |
| multisig, transaction approval | seal-multisig-for-protocols |
| Discord/Telegram security, moderation | seal-community-management |
| bug bounty, vuln disclosure | seal-vulnerability-disclosure |
| audit, external review | seal-external-security-reviews |
| web app, frontend, XSS | seal-front-end-web-app |
| access control, RBAC, authentication | seal-iam |
| OS hardening, network, firewall, cloud | seal-infrastructure |
| monitoring, alerting, SIEM | seal-monitoring |
| privacy, digital footprint, VPN | seal-privacy |
| whitehat, safe harbor | seal-safe-harbor |
| secure coding, repositories | seal-secure-software-development |
| automation, IaC, policy-as-code | seal-security-automation |
| testing, fuzzing, static analysis | seal-security-testing |
| supply chain, dependencies, SLSA | seal-supply-chain |
| treasury, fund controls | seal-treasury-operations |
| team training, security culture | seal-user-team-security |
| ENS, .eth domains | seal-ens |
| certification, protocol cert | seal-certs |
| opsec, travel security, device hardening | seal-opsec |

## How It Works

1. Match user question to a row above
2. `skill_view("seal-<domain>")` to load it
3. Follow `related_skills` in that domain's frontmatter for cross-references
4. `skill_view("seal-<domain>", "references/file.md")` for deeper content

## Source

https://github.com/security-alliance/frameworks
