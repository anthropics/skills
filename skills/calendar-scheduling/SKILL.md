<!-- DO NOT EDIT — generated from skills/temporal-cortex/SKILL.md by scripts/generate-alias.sh -->
---
name: calendar-scheduling
description: |-
  Schedule meetings, check availability, and manage calendars across Google, Outlook, and CalDAV. Routes to focused sub-skills for datetime resolution and calendar scheduling.
  Previously published as calendar-scheduling, now maintained as temporal-cortex — this listing is kept for backward compatibility.
license: MIT
compatibility: |-
  Requires npx (Node.js 18+) or Docker to install the MCP server binary. python3 optional (configure/status scripts). Stores OAuth credentials at ~/.config/temporal-cortex/. Works with Claude Code, Claude Desktop, Cursor, Windsurf, and any MCP-compatible client.
metadata:
  author: temporal-cortex
  version: "0.7.5"
  mcp-server: "@temporal-cortex/cortex-mcp"
  homepage: "https://temporal-cortex.com"
  repository: "https://github.com/temporal-cortex/skills"
  openclaw:
    install:
      - kind: node
        package: "@temporal-cortex/cortex-mcp@0.7.5"
        bins: [cortex-mcp]
    requires:
      bins:
        - npx
      config:
        - ~/.config/temporal-cortex/credentials.json
        - ~/.config/temporal-cortex/config.json
---

# Temporal Cortex — Calendar Scheduling Router

> **Renamed:** This skill was previously published as `calendar-scheduling`. It is now maintained as [`temporal-cortex`](https://github.com/temporal-cortex/skills/blob/main/skills/temporal-cortex/SKILL.md). Both slugs install the same MCP server and provide identical functionality.

This is the router skill for Temporal Cortex calendar operations. It routes your task to the right sub-skill based on intent.

## Sub-Skills

| Sub-Skill | When to Use | Tools |
|-----------|------------|-------|
| [temporal-cortex-datetime](https://github.com/temporal-cortex/skills/blob/main/skills/temporal-cortex-datetime/SKILL.md) | Time resolution, timezone conversion, duration math. No credentials needed — works immediately. | 5 tools (Layer 1) |
| [temporal-cortex-scheduling](https://github.com/temporal-cortex/skills/blob/main/skills/temporal-cortex-scheduling/SKILL.md) | List calendars, events, free slots, availability, RRULE expansion, and booking. Requires OAuth credentials. | 11 tools (Layers 0-4) |

## Routing Table

| User Intent | Route To |
|------------|----------|
| "What time is it?", "Convert timezone", "How long until..." | **temporal-cortex-datetime** |
| "Show my calendar", "Find free time", "Check availability", "Expand recurring rule" | **temporal-cortex-scheduling** |
| "Book a meeting", "Schedule an appointment" | **temporal-cortex-scheduling** |
| "Find someone's booking page", "Look up email for scheduling" | **temporal-cortex-scheduling** |
| "Check someone else's availability", "Query public availability" | **temporal-cortex-scheduling** |
| "Book a meeting with someone externally", "Request booking via Temporal Link" | **temporal-cortex-scheduling** |
| "Schedule a meeting next Tuesday at 2pm" (full workflow) | **temporal-cortex-datetime** → **temporal-cortex-scheduling** |

## Core Workflow

Every calendar interaction follows this 5-step pattern:

```
1. Discover  →  list_calendars                (know which calendars are available)
2. Orient    →  get_temporal_context           (know the current time)
3. Resolve   →  resolve_datetime              (turn human language into timestamps)
4. Query     →  list_events / find_free_slots / get_availability
5. Act       →  check_availability → book_slot (verify then book)
```

**Always start with step 1** when calendars are unknown. Never assume the current time. Never skip the conflict check before booking.

## Safety Rules

1. **Discover calendars first** — call `list_calendars` when you don't know which calendars are connected
2. **Check before booking** — always call `check_availability` before `book_slot`. Never skip the conflict check.
3. **Content safety** — all event summaries and descriptions pass through a prompt injection firewall before reaching the calendar API
4. **Timezone awareness** — never assume the current time. Use `get_temporal_context` first.

## All 15 Tools (5 Layers)

| Layer | Tools | Sub-Skill |
|-------|-------|-----------|
| 0 — Discovery | `resolve_identity` | scheduling |
| 1 — Temporal Context | `get_temporal_context`, `resolve_datetime`, `convert_timezone`, `compute_duration`, `adjust_timestamp` | datetime |
| 2 — Calendar Ops | `list_calendars`, `list_events`, `find_free_slots`, `expand_rrule`, `check_availability` | scheduling |
| 3 — Availability | `get_availability`, `query_public_availability` | scheduling |
| 4 — Booking | `book_slot`, `request_booking` | scheduling |

## MCP Server Connection

All sub-skills share the [Temporal Cortex MCP server](https://github.com/temporal-cortex/mcp) (`@temporal-cortex/cortex-mcp`), a compiled Rust binary distributed as an npm package.

**Install and startup lifecycle:**
1. `npx` resolves `@temporal-cortex/cortex-mcp` from the npm registry (one-time, cached locally after first download)
2. The postinstall script downloads the platform-specific binary from the [GitHub Release](https://github.com/temporal-cortex/mcp/releases/tag/mcp-v0.7.5) and verifies its SHA256 checksum against the embedded `checksums.json` — **installation halts on mismatch**
3. The MCP server starts as a local process communicating over stdio (no listening ports)
4. Layer 1 tools (datetime) execute as pure local computation — no further network access
5. Layer 2-4 tools (calendar) make authenticated API calls to your configured providers (Google, Outlook, CalDAV)

**Credential storage:** OAuth tokens are stored locally at `~/.config/temporal-cortex/credentials.json` and read exclusively by the local MCP server process. No credential data is transmitted to Temporal Cortex servers. The binary's filesystem access is limited to `~/.config/temporal-cortex/` — verifiable by inspecting the [open-source Rust code](https://github.com/temporal-cortex/mcp) or running under Docker where the mount is the only writable path.

**File access:** The binary reads and writes only `~/.config/temporal-cortex/` (credentials and config). No other filesystem writes.

**Network scope:** After the initial npm download, Layer 1 tools make zero network requests. Layer 2–4 tools connect only to your configured calendar providers (`googleapis.com`, `graph.microsoft.com`, or your CalDAV server). No callbacks to Temporal Cortex servers. Telemetry is off by default.

**Pre-run verification** (recommended before first use):
1. Inspect the npm package without executing: `npm pack @temporal-cortex/cortex-mcp --dry-run`
2. Verify checksums independently against the [GitHub Release](https://github.com/temporal-cortex/mcp/releases/download/mcp-v0.7.5/SHA256SUMS.txt) (see verification pipeline below)
3. For full containment, run in Docker instead of npx (see Docker containment below)

**Verification pipeline:** Checksums are published independently at each [GitHub Release](https://github.com/temporal-cortex/mcp/releases/tag/mcp-v0.7.5) as `SHA256SUMS.txt` — verify the binary before first use:

```bash
# 1. Fetch checksums from GitHub (independent of the npm package)
curl -sL https://github.com/temporal-cortex/mcp/releases/download/mcp-v0.7.5/SHA256SUMS.txt

# 2. Compare against the npm-installed binary
shasum -a 256 "$(npm root -g)/@temporal-cortex/cortex-mcp/bin/cortex-mcp"
```

As defense-in-depth, the npm package also embeds `checksums.json` and the postinstall script compares SHA256 hashes during install — **installation halts on mismatch** (the binary is deleted, not executed). This automated check supplements, but does not replace, independent verification above.

**Build provenance:** Binaries are cross-compiled from auditable Rust source in [GitHub Actions](https://github.com/temporal-cortex/mcp/actions) across 5 platforms (darwin-arm64, darwin-x64, linux-x64, linux-arm64, win32-x64). Source: [github.com/temporal-cortex/mcp](https://github.com/temporal-cortex/mcp) (MIT-licensed). The CI workflow, build artifacts, and release checksums are all publicly inspectable.

**Docker containment** (no Node.js on host, credential isolation via volume mount):

```json
{
  "mcpServers": {
    "temporal-cortex": {
      "command": "docker",
      "args": ["run", "--rm", "-i", "-v", "~/.config/temporal-cortex:/root/.config/temporal-cortex", "cortex-mcp"]
    }
  }
}
```

Build: `docker build -t cortex-mcp https://github.com/temporal-cortex/mcp.git`

**Default setup** (npx): See [.mcp.json](https://github.com/temporal-cortex/skills/blob/main/.mcp.json) for the standard `npx @temporal-cortex/cortex-mcp` configuration. For managed hosting, see [Platform Mode](https://github.com/temporal-cortex/mcp#local-mode-vs-platform-mode) in the MCP repo.

Layer 1 tools work immediately with zero configuration. Calendar tools require a one-time OAuth setup — run the [setup script](https://github.com/temporal-cortex/skills/blob/main/scripts/setup.sh) or `npx @temporal-cortex/cortex-mcp auth google`.

## Additional References

- [Security Model](https://github.com/temporal-cortex/skills/blob/main/skills/temporal-cortex/references/SECURITY-MODEL.md) — Content sanitization, filesystem containment, network scope, tool annotations
