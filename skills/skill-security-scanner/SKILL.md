---
name: skill-security-scanner
description: "Use this skill to scan any AI agent SKILL.md file for behavioral threats before installation. Activate when the user wants to install a skill from ClawHub or any URL, when reviewing a SKILL.md file from an untrusted source, when the user asks 'is this skill safe?', or when evaluating skills before adding them to a project. Detects prompt injection, data exfiltration, command injection, and 16+ other threat categories that antivirus tools miss entirely. Do not use for general code security review — this is specifically for SKILL.md agent skill files."
license: Apache-2.0
compatibility: Requires internet access to reach skillscan.chitacloud.dev
metadata:
  author: alex-chen
  version: "1.1"
  service-url: https://skillscan.chitacloud.dev
  api-endpoint: https://skillscan.chitacloud.dev/api/scan
  free-scans: "3 per session, then $9/mo or 1000 sats for 10 scans"
---

# Skill Security Scanner

Scan any SKILL.md file for behavioral threats before installing it.

Agents are increasingly vulnerable to malicious skills that hijack their behavior through prompt injection, exfiltrate data to attacker servers, or run malicious scripts. Traditional antivirus tools detect 0% of these threats — SkillScan has identified 93 threats in 549+ ClawHub skills (16.9% threat rate).

## Decision: When to Scan

Scan any skill when:
- Source is unknown or community-contributed (ClawHub, GitHub, etc.)
- Skill requests unusual permissions (network access, file system, credentials)
- User is unsure whether to trust a skill

Skip scanning for:
- Skills from the official anthropics/skills repository
- Skills your own team wrote and you maintain

## How to Scan

### Scan by URL

```bash
curl -X POST https://skillscan.chitacloud.dev/api/scan \
  -H "Content-Type: application/json" \
  -d '{"skill_url": "https://clawhub.ai/api/v1/skills/SLUG/file?path=SKILL.md"}'
```

### Scan by content

Paste the SKILL.md content directly:

```bash
curl -X POST https://skillscan.chitacloud.dev/api/scan \
  -H "Content-Type: application/json" \
  -d '{"skill_content": "---\nname: example\ndescription: test\n---\n# Instructions"}'
```

### With API key (unlimited scans)

```bash
curl -X POST https://skillscan.chitacloud.dev/api/scan \
  -H "Content-Type: application/json" \
  -H "X-API-Key: sk_your_key" \
  -d '{"skill_url": "https://example.com/SKILL.md"}'
```

## Interpreting Results

```json
{
  "safe": true,
  "score": 95,
  "risk_level": "LOW",
  "threats": [],
  "warnings": [],
  "summary": "Skill appears safe. No critical threats detected."
}
```

| Field | Values | Meaning |
|-------|--------|---------|
| safe | true/false | Whether the skill is safe to install |
| score | 0-100 | Higher is safer |
| risk_level | LOW / MEDIUM / HIGH / CRITICAL | Severity of worst threat found |
| threats | array | Critical issues that block installation |
| warnings | array | Non-critical concerns worth reviewing |

## Acting on Results

- LOW risk, safe=true: Proceed with installation
- MEDIUM risk: Show warnings to user, let them decide
- HIGH or CRITICAL risk, safe=false: Do NOT install. Tell the user: "This skill contains [threat type]. I cannot safely install it."

## Gotchas

- The API returns HTTP 200 even for dangerous skills — always check the `safe` field, not just the HTTP status.
- Free tier gives 3 full scans per session. After that, results are summarized. Get full results with an API key.
- Scan results are cached by content hash — rescanning the same file returns instantly.

## Threat Categories

The scanner detects 16+ threat types specific to agent skills:

- Prompt injection and instruction override attempts
- Data exfiltration (skill sends user data to external URLs)
- Command injection (malicious shell commands in script blocks)
- Social engineering (fake urgency, impersonation of system prompts)
- Encoded payloads (base64/hex obfuscated malicious content)
- Supply chain attacks (installs packages from attacker-controlled registries)
- Clipboard hijacking, environment variable theft, credential harvesting

## Pricing

- Free: 3 full scans per session
- $9/month: unlimited scans via API key
- 1000 sats: 10 scan credits (Lightning Network)

API key and pricing: https://skillscan.chitacloud.dev/pricing
