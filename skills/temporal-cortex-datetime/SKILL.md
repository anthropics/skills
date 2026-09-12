---
name: temporal-cortex-datetime
description: |-
  Convert timezones, resolve natural language times ("next Tuesday at 2pm"), compute durations, and adjust timestamps with DST awareness. No credentials needed — all tools run fully offline after one-time binary install.
license: MIT
compatibility: |-
  Requires npx (Node.js 18+) or Docker to install the MCP server binary (one-time). After installation, all 5 tools run fully offline with zero network access. No OAuth or credentials needed. Works with Claude Code, Claude Desktop, Cursor, Windsurf, and any MCP-compatible client.
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
        - ~/.config/temporal-cortex/config.json
---

# Temporal Context & Datetime Resolution

5 tools for temporal orientation and datetime computation. All tools execute locally within the compiled MCP server binary — no external API calls, no network access at runtime, no credential files. The binary is installed once via npm (or built from source with Docker) and all subsequent executions are fully offline. No OAuth, credentials, or configuration required.

## Tools

| Tool | When to Use |
|------|------------|
| `get_temporal_context` | First call in any session. Returns current time, timezone, UTC offset, DST status, DST prediction, day of week. |
| `resolve_datetime` | Convert human expressions to RFC 3339. Supports 60+ patterns: `"next Tuesday at 2pm"`, `"tomorrow morning"`, `"+2h"`, `"start of next week"`, `"third Friday of March"`. |
| `convert_timezone` | Convert RFC 3339 datetime between IANA timezones. |
| `compute_duration` | Duration between two timestamps (days, hours, minutes). |
| `adjust_timestamp` | DST-aware timestamp adjustment. `"+1d"` across spring-forward = same wall-clock time. |

## Runtime

These tools run inside the [Temporal Cortex MCP server](https://github.com/temporal-cortex/mcp) (`@temporal-cortex/cortex-mcp`), a compiled Rust binary distributed as an npm package.

**Install and startup lifecycle:**
1. `npx` resolves `@temporal-cortex/cortex-mcp` from the npm registry (one-time, cached locally after first download)
2. The postinstall script downloads the platform-specific binary from the [GitHub Release](https://github.com/temporal-cortex/mcp/releases/tag/mcp-v0.7.5) and verifies its SHA256 checksum against the embedded `checksums.json` — **installation halts on mismatch**
3. The MCP server starts as a local process communicating over stdio (no listening ports)
4. All 5 datetime tools execute locally — zero network access, zero filesystem writes, no credentials

**Network access:** Only during the initial npm download. Once cached, subsequent launches are fully offline. The 5 datetime tools make zero network requests — all computation is local.

**File access:** The binary reads only `~/.config/temporal-cortex/config.json` (for timezone and week-start preferences). No filesystem writes. No credential files accessed.

**No credentials required.** Unlike the scheduling skill, this skill needs no OAuth tokens or API keys.

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

**Docker containment** (recommended for maximum isolation — zero Node.js dependency, zero host filesystem access, zero network after build):

```json
{
  "mcpServers": {
    "temporal-cortex": {
      "command": "docker",
      "args": ["run", "--rm", "-i", "--network=none", "cortex-mcp"]
    }
  }
}
```

Build: `docker build -t cortex-mcp https://github.com/temporal-cortex/mcp.git` — No volume mount needed since the datetime skill requires no OAuth tokens or credential files. The `--network=none` flag enforces the zero-network guarantee at the OS level.

## Critical Rules

1. **Always call `get_temporal_context` before time-dependent work** — never assume the time or timezone.
2. **Resolve before querying** — convert `"next Tuesday at 2pm"` to RFC 3339 with `resolve_datetime` before passing to calendar tools.
3. **Timezone awareness** — all datetime tools produce RFC 3339 with timezone offsets.

## resolve_datetime Expression Patterns

The expression parser supports 60+ patterns across 10 categories:

| Category | Examples |
|----------|---------|
| Relative | `"now"`, `"today"`, `"tomorrow"`, `"yesterday"` |
| Named days | `"next Monday"`, `"this Friday"`, `"last Wednesday"` |
| Time of day | `"morning"` (09:00), `"noon"`, `"evening"` (18:00), `"eob"` (17:00) |
| Clock time | `"2pm"`, `"14:00"`, `"3:30pm"` |
| Offsets | `"+2h"`, `"-30m"`, `"in 2 hours"`, `"3 days ago"` |
| Compound | `"next Tuesday at 2pm"`, `"tomorrow morning"`, `"this Friday at noon"` |
| Period boundaries | `"start of week"`, `"end of month"`, `"start of next week"`, `"end of last month"` |
| Ordinal weekday | `"first Monday of March"`, `"third Friday of next month"` |
| RFC 3339 passthrough | `"2026-03-15T14:00:00-04:00"` (returned as-is) |
| Week start aware | Uses configured `WEEK_START` (Monday default, Sunday option) |

## Common Patterns

### Get Current Time Context

```
get_temporal_context()
→ utc, local, timezone, utc_offset, dst_active, dst_next_transition,
  day_of_week, iso_week, is_weekday, day_of_year, week_start
```

### Resolve a Meeting Time

```
resolve_datetime("next Tuesday at 2pm")
→ resolved_utc, resolved_local, timezone, interpretation
```

### Convert Across Timezones

```
1. get_temporal_context → user's timezone
2. convert_timezone(datetime: "2026-03-15T14:00:00-04:00", target_timezone: "Asia/Tokyo")
   → same moment in Tokyo time with DST and offset info
```

### Calculate Duration

```
compute_duration(start: "2026-03-15T09:00:00-04:00", end: "2026-03-15T17:30:00-04:00")
→ total_seconds: 30600, hours: 8, minutes: 30, human_readable: "8 hours 30 minutes"
```

### DST-Aware Adjustment

```
adjust_timestamp(
  datetime: "2026-03-07T23:00:00-05:00",
  adjustment: "+1d",
  timezone: "America/New_York"
) → same wall-clock time (23:00) on March 8, even though DST spring-forward occurs
```

## Additional References

- [Datetime Tools Reference](references/DATETIME-TOOLS.md) — Complete input/output schemas for all 5 tools
