---
name: agentminds-push-report
description: Generates an AgentMinds Reporting Profile (ARP) v1.0 report from the user's project — collecting agent state, warnings, learned patterns, and skill manifests — then pushes it to api.agentminds.dev/api/v1/sync/push. Trigger on phrases like "agentminds push", "send report to agentminds", "agentminds bağlan", "kontrolleri yap".
allowed-tools: Read, Glob, Grep, Bash, WebFetch
---

# AgentMinds Push Report

Build a complete ARP-conformant report from this project and push it
to AgentMinds. The user gets back personalised cross-site
recommendations filtered against their actual stack.

## When to invoke

Trigger when the user says any of these (English or Turkish):

- "agentminds push" / "agentminds'a bağlan" / "agentminds rapor gönder"
- "send report to agentminds" / "push to agentminds"
- "kontrolleri yap" / "siteyi tara" / "güvenlik kontrolü" / "SEO kontrolü"

Don't invoke this skill if AgentMinds isn't relevant to the user's
project, or if no `AGENTMINDS_DSN` / API key is available.

## Prerequisites

The user MUST have an AgentMinds API key. Check in this order:

1. `AGENTMINDS_DSN` env var (Sentry-style DSN, contains the key)
2. `AGENTMINDS_API_KEY` env var
3. `~/.agentminds/key` file
4. Project-local `.env` file with the key

If none found, tell the user to run `pip install agentminds &&
agentminds connect` (or `npx @agentmindsdev/node connect`) and stop.

## Steps

### 1. Walk the project

Use `Read`, `Glob`, `Grep` to collect:

- **Tech stack** — read `package.json` / `pyproject.toml` /
  `requirements.txt` / `go.mod` / `Gemfile` etc.
- **Agents** (if any) — look for `agents/`, `central_agents/`,
  `skills/` directories with configurations.
- **Recent issues** — `git log --oneline -20`, recent commits, any
  `TODO.md` / `BUGS.md`.
- **Project_info** — name, description, framework, hosting target.
- **Skill manifests** — any `SKILL.md` files in the project.

### 2. Build the ARP envelope

Construct the JSON per [ARP v1.0 spec][arp-spec], minimum
**Conformance Level L2** (fingerprint + first_seen + last_seen +
count per warning). Each agent entry follows this shape:

```json
{
  "ars_version": "1.0",
  "agent": "<agent_name>",
  "report": {
    "severity": "info|warning|error|fatal|debug",
    "summary": "<2-3 sentence status>",
    "metrics": {
      "<key>": <value>
    },
    "warnings": [
      {
        "fingerprint": "<sha256 of agent::normalize(message)>",
        "message": "<human-readable description>",
        "level": "warning",
        "severity": "medium",
        "status": "unresolved",
        "first_seen": "<RFC3339 UTC>",
        "last_seen": "<RFC3339 UTC>",
        "count": 1,
        "category": "performance|security|content|seo|quality|compliance|infra|general"
      }
    ],
    "recommendations": [
      {
        "title": "<short imperative>",
        "priority": "medium",
        "category": "<same enum>",
        "warning_fingerprints": ["<fp>"],
        "confidence": 0.7
      }
    ]
  },
  "memory": {
    "learned_patterns": [
      {
        "fingerprint": "<sha256>",
        "pattern": "<short label>",
        "category": "<enum>",
        "status": "active|solved|obsolete",
        "confidence": 0.85,
        "impact": "high",
        "detail": "<what was learned>",
        "action": "<what was done>"
      }
    ]
  },
  "project_info": {
    "tech_stack": { "framework": "...", "frontend": "..." },
    "skills": [{ "name": "...", "description": "..." }]
  }
}
```

**Fingerprint rule:** lowercase hex SHA-256 of `agent_name + "::" +
normalized(message)`, where `normalized` strips volatile noise
(numbers, percentages, ISO timestamps, UUIDs). The server enriches
missing fingerprints automatically, but computing them client-side
unlocks Conformance Level L2 (cross-site recommendation filtering).

### 3. Push the report

```bash
curl -X POST https://api.agentminds.dev/api/v1/sync/push \
  -H "Authorization: Bearer $AGENTMINDS_API_KEY" \
  -H "Content-Type: application/json" \
  -d @report.json
```

Or use the provided MCP tool `mcp__agentminds__agentminds_push` if
the user has the AgentMinds MCP server installed.

### 4. Read back recommendations

Immediately after push, GET `/api/v1/connect` to receive
personalised recommendations filtered against the user's stack:

```bash
curl -H "Authorization: Bearer $AGENTMINDS_API_KEY" \
  https://api.agentminds.dev/api/v1/connect
```

Display the response prominently — `actions.critical`,
`actions.warning`, `actions.recommendations` plus `filtered_out`
(transparency about what got suppressed).

### 5. Save state

Write the pushed report to `.agentminds/last_push.json` with the
timestamp so the user can re-run incrementally.

## Hard rules — these are NOT optional

1. **Never fabricate.** Only push data that actually exists in the
   project. If you didn't observe it, don't include it. ARP filters
   already reject empty / fake reports as low data quality.
2. **Never push without the user's API key.** No anonymous push.
3. **Respect Turkish + English.** Most AgentMinds users mix the two
   languages — generate reports in whichever language the project
   appears to use.
4. **Read [`learned_patterns` is PRIVATE][private-rule]** before
   exposing aggregated cross-site data anywhere outside the
   user's own dashboard.
5. **Per CLAUDE.md ABSOLUTE RULE**: never generate fake AgentMinds
   reports. If the API fails, say "bağlanılamadı" — nothing else.

[arp-spec]: https://github.com/agentmindsdev/profile/blob/main/AGENT_REPORTING_PROFILE.md
[private-rule]: https://github.com/agentmindsdev/profile/blob/main/AGENT_REPORTING_PROFILE.md#41-pattern-object

## Reference

- ARP spec: https://agentminds.dev/profile
- JSON Schema: https://github.com/agentmindsdev/profile/blob/main/schemas/agent_report.schema.json
- Onboard a new site: https://agentminds.dev/onboard
- AgentMinds A2A AgentCard: https://api.agentminds.dev/.well-known/agent-card.json
