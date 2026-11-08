# TOS Guardian — Anthropic Compliance Skill for AI Agents

**Prevent account suspension. Keep your agents legal.**

An [Agent Skill](https://claude.com/blog/skills) that enforces Anthropic's Consumer TOS for autonomous AI agents.

🌐 [cryptopedia.ai](https://cryptopedia.ai) · 𝕏 [@cryptopedia_AI](https://x.com/cryptopedia_AI)

---

## What This Is

TOS Guardian is a compliance skill that teaches AI agents the rules before they break them.

If you run autonomous Claude-powered agents — on Hetzner, Railway, AWS, your basement server, wherever — those agents need to know what they can and can't do under Anthropic's Consumer Terms of Service. Most don't. They'll happily auto-refresh OAuth tokens, hammer the API at machine speed, or publish content without checking policy. Then your account gets suspended and you lose everything.

This skill prevents that. It gives your agents a clear, machine-readable ruleset covering authentication, access methods, rate limits, content policy, data handling, and account integrity. It includes a self-check protocol agents run at startup and periodically, an audit logging system, and graceful degradation — so when something goes wrong, the agent pauses and calls you instead of digging itself deeper.

## Who This Helps

**Agent operators:** You get peace of mind. Your agents know the boundaries. You don't wake up to a suspended account.

**Anthropic:** Compliant agents mean less abuse, fewer false positives in enforcement, and a healthier ecosystem. When agents self-police, everybody wins.

**The community:** This is the first TOS compliance skill for AI agents. It's open source, cross-platform (works with Claude Code, Codex CLI, and any framework that reads Agent Skills), and sets a precedent that autonomous agents should ship with governance built in — not bolted on after something goes wrong.

## Rules Covered

| Rule | Summary |
|------|---------|
| 1. Human Auth | Tokens must come from human login — no auto-refresh |
| 2. Sanctioned Access | Only Claude Code, API keys, or approved tools |
| 3. Rate Respect | Human-reasonable pace, backoff on limits |
| 4. Content Policy | All publications pass AUP checklist |
| 5. Data Privacy | Redact secrets and PII from prompts |
| 6. Account Integrity | One user per token, no reselling |
| 7. Graceful Degradation | When uncertain, stop and ask |
| 8. Audit Trail | Log every TOS-relevant decision |

## How It Works

1. Drop the skill into your agent's skills directory
2. The agent loads it automatically when relevant (that's how Agent Skills work)
3. At boot and every 4 hours, the self-check script validates token status, access methods, and environment
4. If something's wrong — expired token, unsanctioned tool detected — the agent pauses and notifies you
5. Every TOS-relevant decision gets logged to an audit trail you can review anytime

No magic. No black boxes. Just a Markdown file with clear rules and a bash script that checks them.

## Install

```bash
# Claude Code (personal)
cp -r tos-guardian ~/.claude/skills/

# Claude Code (project)
cp -r tos-guardian .claude/skills/

# OpenClaw
cp -r tos-guardian /root/.openclaw/workspace/skills/

# Any other framework
# Load SKILL.md into your agent's system prompt at initialization
```

---

## Independent Project — Not Affiliated with Anthropic

This skill is an independent, community-built project. The developer is **not associated with, employed by, endorsed by, or affiliated with Anthropic in any way**.

This is a good-faith effort by someone who uses Anthropic's products, appreciates them, and wants to help both sides: agent operators who want to stay compliant, and Anthropic who benefits from a community that respects the rules instead of gaming them.

The rules in this skill are based on publicly available information — Anthropic's published Consumer Terms of Service, their Acceptable Use Policy, public enforcement actions, and official documentation. Nothing here is sourced from insider knowledge, private communications, or privileged access.

If Anthropic has corrections, suggestions, or objections, contributions are welcome.

---

## Disclaimer & Terms

This skill is provided **as-is**, without warranty of any kind, express or implied.

By using TOS Guardian, you acknowledge and agree that:

1. **No guarantees.** This skill is a best-effort guide based on publicly available information about Anthropic's Consumer Terms of Service as of February 2026. It does not guarantee compliance. Terms change. Enforcement evolves. This skill may be outdated, incomplete, or wrong.

2. **Not legal advice.** Nothing in this skill constitutes legal advice. We are not lawyers. If you need a legal opinion on your specific use case, consult an actual lawyer.

3. **AI-generated content.** This skill was built with the assistance of AI. AI makes mistakes. Review everything yourself before relying on it.

4. **You are responsible.** The human operator is solely responsible for their agents' behavior, their account, and their compliance with any applicable terms of service. If your agent violates Anthropic's TOS (or anyone else's), that's on you — not on this skill, its authors, or its contributors.

5. **No liability.** The authors and contributors of TOS Guardian shall not be held liable for any damages, account suspensions, financial losses, or consequences of any kind arising from the use or misuse of this skill.

6. **You already know this.** If you're running autonomous AI agents on remote infrastructure, you presumably understand the risks. This skill helps — it doesn't babysit.

This disclaimer may be updated at any time. Check the repo for the latest version.

---

## License

Apache 2.0 — Use it, fork it, improve it. Keep agents compliant.