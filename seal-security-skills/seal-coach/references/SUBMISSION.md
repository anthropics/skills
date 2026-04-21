# SEAL Security Coach

**An AI-powered security coach that turns the SEAL Security Alliance Frameworks into personalized, actionable hardening plans for open source projects and DAOs.**

*Synthesis Hackathon Submission*

---

## Why This Matters

Open source security is a sustainability problem. Projects that power billions in on-chain value — protocols, DAOs, tooling — can't afford the security infrastructure they need:

- **Professional assessments cost $10K-$50K+.** Open source teams run on grants and donations.
- **Frameworks are static docs.** SEAL publishes 27 domains with 213+ controls. Nobody reads a 200-page framework and knows where to start.
- **Security is reactive.** Teams fix things after they get drained. The damage is already done.

This is the open source security gap: **the projects that need security the most can least afford it.**

The SEAL Security Coach closes that gap — not by replacing security experts, but by turning domain knowledge into an interactive, always-available coach that meets teams where they are.

## What It Does

### Three Entry Points

**1. "I'm worried we're going to get hacked"** (Urgency)
- Triage in 2 exchanges: wallet vs infrastructure concern
- 3-5 targeted questions focused on "can an attacker exploit this TODAY?"
- Immediate actions before a full assessment
- Then broadens to full readiness check

**2. "Check our security posture"** (Assessment)
- Pre-assessment: org type, role, team size, past incidents
- Quick scan: 5 questions mapping to priority domains
- Domain deep-dive: 3-4 targeted questions per area
- Readiness bands: Critical -> Developing -> Established -> Advanced

**3. "Give me a security tip"** (Daily)
- Rotates across all 27 SEAL domains
- Tracks delivered tips to avoid repeats
- Links each tip to specific framework controls

### Example: Before a Drain

```
User: "I think we might get hacked. We have a multisig treasury but I'm not sure
       we're doing enough."

Coach: "Let's figure out where the risk is. You mentioned multisig — that's good.
        Quick question: if one signer's device was compromised right now, could
        the attacker drain funds?"

User: "We use 2-of-3 multisig. But two of us have our keys on the same laptop..."

Coach: "That's the gap. If that laptop is compromised, an attacker has 2 of 3 keys.
        Three things you can do RIGHT NOW:
        1. Split keys — one signer should use a hardware wallet
        2. Set a timelock — large transactions need a waiting period
        3. Verify signers — no one has shared or insecurely stored their key"
```

No quiz. No generic "enable MFA" advice. Context-specific, actionable, immediate.

### From Assessment to Action

After assessment, the coach generates a phased hardening plan:

```
Phase 1: Quick Wins (Week 1-2)
  - Split multisig keys across hardware wallets
  - Enable MFA on all admin accounts
  - Save SEAL 911 emergency contact

Phase 2: Foundation (Week 3-6)
  - Write incident response playbook
  - Add semgrep to CI/CD pipeline
  - Set up transaction monitoring alerts

Phase 3: Strengthen (Week 7-12)
  - Formal threat model
  - Automated compliance checks
  - Tabletop incident exercises
```

Every action maps to specific SEAL framework controls — no vague advice.

### Proactive Onboarding

After the first assessment, the coach offers to set up ongoing support:

- **Daily security tips** — builds a security habit, one tip per day rotated across 27 domains
- **Weekly progress check-ins** — "How's the hardening plan going? Any blockers?"
- **Team accountability pings** — reminds specific team members about their assigned actions

The coach asks, user explicitly confirms, then creates scheduled check-ins. No silent automations.

### Memory Across Sessions

The coach remembers your readiness bands, completed actions, tips already delivered, and current focus. When you come back: "Last time we identified incident-management as Critical. Want to pick up there?"

## What Makes It Different

| Generic AI Security Advice | SEAL Coach |
|---|---|
| "Enable MFA" (no context) | "Your multisig uses 2-of-3, but two signers share a laptop — if it's compromised, attacker has 2 of 3 keys. Move one signer to a hardware wallet." |
| One-size-fits-all list | Adapts to team size, role, tech stack, urgency |
| No memory between sessions | Tracks readiness bands, completed actions, avoids repeating tips |
| No domain expertise | Maps every recommendation to specific SEAL framework controls |
| Cloud-dependent, data retention | Zero data retention via Venice.ai, local-first state |
| One-shot interaction | Offers proactive check-ins (daily tips, weekly reviews, team accountability) |

## Validated Against Test Suite

The coach skill is scored against a synthetic test suite with 30 prompts across 13 categories:

| Version | Prompts | Avg Score | What Changed |
|---|---|---|---|
| v1.0 baseline | 20 | 4.75 | Initial skill structure |
| v2.0 | 20 | 4.85 | Cross-domain triggers + gotchas |
| v3.0 | 30 | pending | Expanded coverage, 13 categories |

## Architecture

```
seal-coach/
├── SKILL.md                        # Core: triggers, urgency flow, scenario walkthroughs
├── references/
│   ├── assessment.md               # Flexible assessment + readiness bands
│   ├── gotchas.md                  # Common coaching failures & fixes
│   ├── plans/hardening-template.md # Actionable plans by readiness band
│   └── tips/security-tips.md       # Rotating tips across 27 domains
├── scripts/score_assessment.py     # Maps answers to readiness bands
└── templates/state-log.json        # Per-user progress tracking
```

**Built on:**
- [SEAL Security Alliance Frameworks](https://github.com/security-alliance/frameworks) — 27 domains, 213+ controls
- [Hermes Agent](https://github.com/m3-org/hermes-agent) — agent platform with memory, tool use, multi-platform delivery
- Skill-based architecture — portable, works with any agent supporting the skills spec

## Privacy

- **Zero data retention** via Venice.ai inference — no conversation logs stored server-side
- **Local-first** — assessment state in local JSON, not cloud
- **No PII** — the coach asks about your security setup, not your identity

## Demo

*[Recording: urgency flow — worried about drainage -> rapid triage -> immediate actions -> full assessment -> hardening plan]*

## Try It

```bash
# Install with Hermes Agent
hermes skills install seal-coach
hermes

# Or clone and copy into your agent's skills directory
```

## Built For

The [Synthesis Hackathon](https://synthesis.devfolio.co/) — Open source sustainability and agent-DAO.

**The connection:** Open source projects sustain the ecosystem but can't afford security infrastructure. An AI coach built on open frameworks (SEAL) delivered through an open agent platform (Hermes) closes that gap — making expert-level security guidance accessible to every project, not just those with funding.

**Team:** jin, cyberWarlock, emotionull, peepo
