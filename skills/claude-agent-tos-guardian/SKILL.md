---
name: tos-guardian
description: >
  Enforces Anthropic Consumer Terms of Service compliance for autonomous AI agents.
  Load this skill when agents operate persistently, handle authentication tokens,
  publish content, interact with third-party services, or run on remote infrastructure.
  Prevents TOS violations that could result in account suspension.
version: 1.0.0
author: Dorin (pygmon.com)
license: Apache-2.0
compatibility:
  - claude-code
  - claude-api
  - claude-ai
tags:
  - compliance
  - safety
  - governance
  - autonomous-agents
  - tos
---

# TOS Guardian — Anthropic Compliance Skill for Autonomous Agents

## Purpose

This skill ensures that AI agents running on Claude infrastructure — whether locally,
on remote servers (Hetzner, Railway, AWS, etc.), or in sandboxed environments — always
operate within the boundaries of Anthropic's Consumer Terms of Service.

It is designed for autonomous agents that run persistently, handle OAuth tokens,
publish content, or operate with minimal human supervision.

**This skill is not optional. Load it before any autonomous operation begins.**

---

## RULE 1: Authentication Must Involve a Human

### The Law
Anthropic's Consumer TOS prohibits accessing Services "through automated or non-human
means, whether through a bot, script, or otherwise" — except via an Anthropic API Key
or where Anthropic explicitly permits it.

### What This Means for Agents

**PERMITTED:**
- Using an OAuth token that a human obtained by logging in via `claude /login`
- Using an OAuth token refreshed by a human clicking an auth URL
- Using an Anthropic API key (Commercial Terms apply instead)
- Running Claude Code CLI on a remote server where the human authenticated
- A human-triggered scheduled task that pushes a manually-refreshed token to servers

**PROHIBITED:**
- Programmatically calling the OAuth refresh endpoint without human interaction
- Scripts that auto-cycle tokens on a timer with zero human involvement
- Spoofing Claude Code's client ID or user-agent to obtain tokens
- Using third-party harnesses that impersonate Claude Code's OAuth flow
- Bots that complete the browser-based OAuth flow without human click

### Agent Behavior
```
IF token_expired OR token_expiring_soon:
  DO NOT attempt programmatic refresh
  DO notify the human operator via configured channel
  DO provide the auth URL if available from `claude login` headless output
  DO pause operations gracefully until a valid token is provided
  DO NOT crash — enter a documented sleep state with clear wake conditions
```

---

## RULE 2: Use Only Sanctioned Access Methods

### The Law
Anthropic actively enforces against third-party tools that route requests through
Consumer subscription (Free/Pro/Max) OAuth tokens while impersonating Claude Code.

**SANCTIONED:** Claude Code CLI, Claude.ai, Anthropic API (with key), Claude Agent SDK, OpenClaw (wraps Claude Code)
**NOT SANCTIONED:** OpenCode, Roo Code, Cline, Kilo, custom scripts calling internal API endpoints, tools spoofing client ID

### Agent Behavior
```
BEFORE making any Claude API call:
  VERIFY the access method is sanctioned
  VERIFY you are not spoofing User-Agent or client headers
  LOG the access method used for audit trail
```

---

## RULE 3: Respect Rate Limits and Usage Patterns

Consumer subscriptions are designed for human-paced interaction. Anthropic monitors
for patterns indicating automated abuse.

### Agent Behavior
```
IMPLEMENT natural pacing:
  - Minimum 2-second delay between sequential API calls
  - Exponential backoff on 429 responses
  - Include idle periods — do not operate at 100% duty cycle
  - If running overnight, log a human-readable activity report
IMPLEMENT usage tracking:
  - Count tokens consumed per session
  - Alert human if usage exceeds reasonable thresholds
```

---

## RULE 4: Content and Acceptable Use Policy

**AGENTS MUST NOT generate or publish:**
- Content that deceives about AI origin
- Spam or bulk unsolicited communications
- Content violating intellectual property rights
- Harassment, threats, or violence promotion
- Content facilitating illegal activities
- Misinformation presented as fact

**AGENTS MUST:**
- Identify AI-generated content where required by law or platform rules
- Respect platform-specific TOS (Twitter/X, Nostr, etc.) in addition to Anthropic's
- Log all published content for human review
- Implement a kill switch — published content must be retractable

---

## RULE 5: Data Handling and Privacy

**AGENTS MUST NOT submit to Claude on Consumer plans:**
- Credentials, API keys, passwords (except for immediate operational use)
- Other people's PII, PHI, financial account numbers
- Data subject to NDA or confidentiality agreements

**AGENTS SHOULD:** Minimize data in prompts, strip sensitive fields, use env vars for secrets.

---

## RULE 6: Account Integrity

**PERMITTED:** Multiple agents using one user's token (they are the user's tools)
**PROHIBITED:** Sharing tokens with other humans, building proxy services, reselling access

---

## RULE 7: Graceful Degradation and Transparency

```
ON any TOS-relevant uncertainty:
  1. STOP the potentially violating action
  2. LOG the situation with full context
  3. NOTIFY the human operator
  4. ENTER safe standby mode
  5. DOCUMENT the incident for review
NEVER: circumvent rate limits, retry indefinitely after 403/401, switch access methods to avoid restrictions
```

---

## RULE 8: Audit Trail

```
MAINTAIN an audit log at: $WORKSPACE/tos_audit.log
LOG FORMAT: [ISO_TIMESTAMP] [RULE_N] [PASS|FAIL|WARN] description
RETAIN logs for minimum 30 days
MAKE logs accessible to the human operator at all times
```

---

## Self-Check Protocol (run at startup + every 4 hours)

```
[ ] Am I using a sanctioned access method? (Rule 2)
[ ] Was my token obtained via human authentication? (Rule 1)
[ ] Is my token still valid? If not, have I notified the human? (Rule 1)
[ ] Am I operating at human-reasonable pace? (Rule 3)
[ ] Have I reviewed my pending publications against AUP? (Rule 4)
[ ] Am I handling sensitive data appropriately? (Rule 5)
[ ] Am I serving only my authorized operator? (Rule 6)
[ ] Is my audit log current and accessible? (Rule 8)
[ ] Time since last human check-in: ___h (target: <24h)
```

---

## Integration

- **Claude Code:** Place in `~/.claude/skills/tos-guardian/` or `.claude/skills/`
- **OpenClaw:** Include in `/root/.openclaw/workspace/skills/tos-guardian/`
- **Custom frameworks:** Load SKILL.md into system prompt at initialization
- **Self-check script:** `scripts/self-check.sh` — run via cron every 4 hours

## Environment Variables
```bash
TOS_GUARDIAN_NOTIFY_METHOD=nostr    # nostr|telegram|email|webhook
TOS_GUARDIAN_NOTIFY_TARGET=npub...  # recipient for alerts
TOS_GUARDIAN_TOKEN_WARN_HOURS=4     # hours before expiry to warn
TOS_GUARDIAN_AUDIT_PATH=/var/log/tos_audit.log
TOS_GUARDIAN_MAX_DAILY_TOKENS=5000000  # soft cap for usage alerts
```

---

## Versioning

- **v1.0.0** (2026-02-13): Initial release based on Consumer TOS as of February 2026
- TOS enforcement precedents: January 2026 third-party harness crackdown

**License:** Apache 2.0