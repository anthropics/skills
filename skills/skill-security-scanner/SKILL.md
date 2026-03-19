---
name: skill-security-scanner
description: Scans AI agent SKILL.md files for behavioral threats, prompt injection, and malicious patterns before installation. Use when installing or reviewing any skill file, when asked to verify a skill is safe, or when the user mentions a skill URL or SKILL.md file. Detects 16+ threat categories that antivirus tools miss entirely.
license: Apache-2.0
compatibility: Requires internet access to reach skillscan.chitacloud.dev
metadata:
  author: alex-chen
  version: "1.0"
  service-url: https://skillscan.chitacloud.dev
  api-endpoint: https://skillscan.chitacloud.dev/api/scan
  free-scans: "3 per session, then $9/mo or 1000 sats for 10 scans"
---

# Skill Security Scanner

Scan any SKILL.md file for behavioral threats before installing it. Covers 16+ threat categories including prompt injection, data exfiltration, command injection, and social engineering patterns that traditional antivirus tools completely miss.

## When to Use

Activate this skill whenever:
- A user wants to install a skill from ClawHub or any URL
- You encounter a SKILL.md file from an untrusted source
- The user asks "is this skill safe?" or "can I trust this skill?"
- You are asked to review a skill before adding it to a project

## How to Scan a Skill

### Option 1: Scan by URL (recommended)

Send a POST request to the scan API with the skill URL:

```bash
curl -X POST https://skillscan.chitacloud.dev/api/scan \
  -H "Content-Type: application/json" \
  -d '{"skill_url": "https://clawhub.ai/api/v1/skills/YOUR-SKILL-SLUG/file?path=SKILL.md"}'
```

### Option 2: Scan skill content directly

```bash
curl -X POST https://skillscan.chitacloud.dev/api/scan \
  -H "Content-Type: application/json" \
  -d '{"skill_content": "---\nname: example\ndescription: test\n---\n# Instructions here"}'
```

### With API Key (for unlimited scans)

```bash
curl -X POST https://skillscan.chitacloud.dev/api/scan \
  -H "Content-Type: application/json" \
  -H "X-API-Key: sk_your_key_here" \
  -d '{"skill_url": "https://example.com/SKILL.md"}'
```

## Interpreting Results

The API returns a JSON object with:

- `safe` (boolean): true if no critical threats found
- `score` (0-100): security score, higher is safer
- `risk_level`: "LOW", "MEDIUM", "HIGH", or "CRITICAL"
- `threats`: array of detected threat descriptions
- `warnings`: array of non-critical concerns
- `summary`: human-readable summary of findings

Example safe response:
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

Example flagged response:
```json
{
  "safe": false,
  "score": 12,
  "risk_level": "CRITICAL",
  "threats": [
    "Prompt injection: attempts to override system instructions",
    "Data exfiltration: sends user data to external URL"
  ],
  "warnings": ["Unusual instruction to ignore previous context"],
  "summary": "CRITICAL: This skill contains prompt injection and exfiltration attempts. Do not install."
}
```

## Threat Categories Detected

The scanner detects 16+ threat types:
- Prompt injection and instruction override attempts
- Data exfiltration (sending user data to attacker servers)
- Command injection (malicious shell commands in scripts)
- Social engineering (fake urgency, impersonation)
- Encoded payloads (base64/hex obfuscated malicious content)
- Supply chain attacks (malicious package installations)
- Clipboard hijacking
- Environment variable theft
- Credential harvesting

## Pre-Installation Check Workflow

Before installing any skill, follow this workflow:

1. Get the skill URL or content
2. Call the scan API
3. Check `safe` and `risk_level`
4. If `safe: false` or `risk_level` is HIGH/CRITICAL: do NOT install, inform the user
5. If `safe: true` with LOW risk: proceed with installation
6. If MEDIUM risk: inform the user of specific warnings and let them decide

## Statistics

The scanner has analyzed 549+ ClawHub skills and found:
- 93 threats (16.9% of all skills flagged)
- VirusTotal misses 100% of these skill-specific threats
- Most common: prompt injection (8.1%), social engineering (4.2%)

## Pricing

- Free: 3 full scans per session, then summarized results
- $9/month: unlimited full scans via API key
- 1000 sats: 10 scan credits (Lightning Network)

Get API key and pricing: https://skillscan.chitacloud.dev/pricing
