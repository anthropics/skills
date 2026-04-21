# seal-skills

Security knowledge graph for AI agents. 27 domains, 111 certification controls, from the [SEAL Frameworks](https://github.com/security-alliance/frameworks).

```bash
# Ask any security question — the agent finds the right domain automatically
> My multisig was compromised, what do I do?
> How do I set up incident response for our protocol?
> We're hiring remote devs — any DPRK concerns?
```

---

## What this does

Gives your AI agent (Hermes, Claude, Cursor, etc.) structured security knowledge across 27 domains — from incident response and multisig operations to DPRK worker detection and supply chain security.

**Not a PDF.** Not a static checklist. Interactive guidance with gotchas, cross-domain awareness, and context-specific answers.

## Quick Start

```bash
git clone https://github.com/clanktank/seal-skills.git ~/.hermes/skills/seal
```

For private inference (sensitive security data):

```bash
hermes config set provider.base_url "https://api.venice.ai/v1"
hermes config set provider.model "qwen3-5-35b-a3b"
hermes restart
```

Verify it works:

```bash
hermes chat --toolsets skills -q "What seal skills do you have?"
```

## Usage

**Discord:** `@mention` the bot and ask any security question naturally.

**Telegram / CLI:** Say things like:
- "check my security posture"
- "help me set up multisig"
- "we just got hacked, what do I do"
- "daily security tips" (sets up coach with daily lessons)

The agent matches your question to the right domain and answers using the SEAL frameworks.

## Domains (27)

| Domain | Focus |
|--------|-------|
| **incident-management** | Response playbooks, containment, recovery |
| **multisig-for-protocols** | Signer management, thresholds, backup signing |
| **treasury-operations** | Fund classification, diversification, controls |
| **wallet-security** | Seed phrases, hardware wallets, signing verification |
| **supply-chain** | Dependency auditing, lockfiles, vendoring |
| **infrastructure** | OS hardening, network security, cloud configuration |
| **iam** | Access control, least privilege, RBAC |
| **monitoring** | SIEM, alerting, anomaly detection |
| **threat-modeling** | Asset identification, attack surface analysis |
| **dprk-it-workers** | Worker infiltration detection, identity verification |
| **safe-harbor** | Whitehat protections, scope terms |
| **vulnerability-disclosure** | Bug bounties, responsible disclosure |
| **opsec** | Operational security, information classification |
| **privacy** | Encrypted comms, VPN, metadata protection |
| **encryption** | At-rest, in-transit, key management |
| **devsecops** | CI/CD security, code signing, branch protection |
| **governance** | Compliance, risk assessment, security KPIs |
| **external-security-reviews** | Audit lifecycle, vendor selection |
| **front-end-web-app** | CSP, supply chain, XSS prevention |
| **community-management** | Discord/Telegram security, bot moderation |
| **secure-software-development** | Code review, secure coding practices |
| **security-testing** | Penetration testing, fuzzing, red teaming |
| **security-automation** | As-code, automated scanning, SOAR |
| **ens** | ENS domain security, record verification |
| **certs** | SEAL certification frameworks (6 SFCs, 111 controls) |
| **awareness** | Phishing, social engineering, training |
| **user-team-security** | Security culture, onboarding, phishing defense |

## Coach Mode

The seal-coach skill provides Duolingo-style security training:

- **Daily tips** — one security lesson per day, relevant to your domain
- **Readiness assessment** — 8-10 questions to measure your security posture
- **Hardening plans** — prioritized action items based on assessment
- **Progress tracking** — streaks, domain scores, completed lessons
- **Urgency path** — immediate triage for active threats

Start coaching by saying "daily security tips" or "check my readiness."

## How it works

Each domain is a skill with cross-domain triggers and gotchas:

```
~/.hermes/skills/seal/
├── INDEX.md                         # Trigger table — routes questions to domains
├── SEAL-COACH/                      # Coach skill (daily tips, assessments)
│   ├── SKILL.md
│   ├── references/
│   └── templates/
├── CERTS/                           # 6 SFC certifications (111 controls)
│   ├── SKILL.md
│   └── references/
├── incident-management/             # Response playbooks
├── multisig-for-protocols/          # Signer ops
├── wallet-security/                 # Seed phrases, HW wallets
└── ... (24 more domains)
```

## Security & Privacy

SEAL skills handle information about an organization's security posture — which controls they fail, weak configurations, incident gaps. **Using these with a cloud LLM sends sensitive security data to a third party.**

### Provider trust

| Provider | What they see | Risk | When to use |
|----------|--------------|------|-------------|
| **Local LLM** (Ollama, vLLM) | Nothing leaves the machine | None | Highest security |
| **Venice.ai** | Queries during inference, no retention | Low | Privacy + quality balance |
| **Self-hosted** (Modal, Lambda) | You control infra | Low-Medium | Scale + full control |
| **Anthropic/Claude** | All queries retained | High | Non-sensitive only |
| **OpenRouter** | Aggregator, varies by provider | Varies | Never for sensitive data |

Venice.ai guarantees no data retention and no training on user data. "No retention" is a policy, not a technical guarantee — treat Venice as lower-risk than Anthropic/OpenAI, but not equivalent to local inference.

### What flows to the LLM

- Your security questions (reveals what you're worried about)
- Answers to cert controls ("no" = specific gap identified)
- Incident scenarios (details of breaches)
- Gotchas discussed (known weaknesses)

**Rule:** Before deploying for any organization, ask: *"Are we comfortable with our inference provider seeing this data?"* If no, use local inference or Venice.ai.

## Source

- Frameworks: https://github.com/security-alliance/frameworks
- Skill standard: https://agentskills.io
- Agent: https://github.com/NousResearch/hermes-agent
