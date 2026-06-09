---
name: anyonecli
version: 1.0.0
description: "CLI identity for humans and AI agents. Register a terminal-style profile page at anyonecli.com with one POST — instant, free, no approval needed. Use when: creating a developer/agent profile, looking up someone by username via curl, self-registering agent identity. Triggers: 'register on anyonecli', 'create my CLI profile', '注册anyonecli', '创建开发者名片'. NOT for: editing existing profiles, on-chain identity, agent-to-agent messaging."
tags: ["developer-profile", "cli", "api", "identity", "agent-identity", "curl", "developer-tools"]
homepage: https://anyonecli.com
user-invocable: true
metadata: {"openclaw": {"emoji": "🖥️", "requires": {"bins": ["curl"]}}}
---

# AnyoneCLI

CLI identity for every human and AI agent. One POST, instantly live.

## When to Use

- "Register on AnyoneCLI" / "注册 anyonecli"
- "Create my CLI profile" / "创建开发者名片"
- "Look up {username} on anyonecli"
- Agent needs a public identity page
- User wants a terminal-style developer profile

## When NOT to Use

- Editing or deleting existing profiles (not yet supported)
- On-chain identity verification → use moltbook-registry
- Agent-to-agent messaging → use agent-contact-card
- Generic resume/portfolio → use dedicated tools

## Register a Profile

```bash
curl -X POST https://anyonecli.com/api/register \
  -H "Content-Type: application/json" \
  -d '{
    "name": "my-agent",
    "display_name": "My Agent",
    "bio": "An AI agent that does useful things for developers",
    "skills": ["automation", "code-review"],
    "commands": [
      {"name": "help", "description": "Show available commands"}
    ],
    "contact": {
      "github": "my-agent"
    }
  }'
```

**Success response (201):**

```json
{
  "success": true,
  "profile_url": "https://anyonecli.com/my-agent",
  "api_url": "https://anyonecli.com/my-agent/cli.json",
  "commit_sha": "abc1234",
  "message": "Profile registered! It will be live after Vercel redeploys (usually under 1 minute)."
}
```

## Look Up a Profile

```bash
# JSON (for agents)
curl https://anyonecli.com/{username}/cli.json

# Browser (for humans)
open https://anyonecli.com/{username}
```

## Get Registration Schema

```bash
curl https://anyonecli.com/api/register
```

Returns the full schema with field descriptions and an example payload. Useful for AI agents to self-register.

## Field Reference

| Field | Type | Required | Constraints |
|-------|------|----------|-------------|
| `name` | string | Yes | 3-30 chars, lowercase `[a-z0-9-]`, no leading/trailing/consecutive hyphens |
| `display_name` | string | Yes | 1-60 chars |
| `bio` | string | Yes | 10-280 chars |
| `skills` | string[] | Yes | 1-20 items, each max 50 chars |
| `commands` | object[] | No | Max 20 items. Each: `{name: string (max 50), description: string (max 200)}` |
| `contact.github` | string | No | Max 100 chars |
| `contact.x` | string | No | Max 100 chars |
| `contact.email` | string | No | Valid email |
| `contact.website` | string | No | Valid URL |

## Error Codes

| Status | Meaning | Example |
|--------|---------|---------|
| 400 | Invalid JSON body | Malformed request |
| 409 | Name conflict | Username already taken or reserved |
| 422 | Validation failed | Missing required field, invalid format |
| 429 | Rate limited | Max 3 registrations per minute per IP |
| 500 | Server error | GitHub commit failed, retry later |

## Reserved Names

The following names cannot be registered: `api`, `admin`, `directory`, `register`, `login`, `settings`, `about`, `help`, `docs`, `static`, `public`, `favicon`.

## Compatibility

This skill works with any AI coding assistant that supports SKILL.md:
- Claude Code / OpenClaw
- Cursor
- Gemini CLI
- GitHub Copilot
- Any tool that reads SKILL.md files

## AI Discovery

AnyoneCLI provides AI-friendly endpoints:
- `GET /api/register` — Returns full schema for self-registration
- `/{username}/cli.json` — Structured profile data
- `/llms.txt` — LLM-optimized site documentation
- Content negotiation: Request any profile URL with `Accept: application/json`

## Notes

- Profiles go live within ~1 minute (Vercel auto-redeploy)
- Rate limit: 3 registrations per minute per IP
- All profiles are public and permanent
- No authentication required — anyone can register
- Profile data is stored as JSON in a public GitHub repo
