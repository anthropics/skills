---
name: calendar-scheduling
description: |-
  Calendar scheduling for AI agents. Resolves natural language times, merges availability across Google, Outlook, and CalDAV calendars, detects conflicts, expands recurrence rules (RRULE), and books slots atomically with Two-Phase Commit safety. Use when scheduling meetings, checking availability, resolving datetime expressions, or managing calendar events.
license: MIT
compatibility: |-
  Requires npx (Node.js 18+) or Docker for the MCP server. Works with Claude Code, Claude Desktop, Cursor, Windsurf, and any MCP-compatible client.
metadata:
  author: billylui
  version: "0.3.1"
  mcp-server: "@temporal-cortex/cortex-mcp"
---

# Calendar Scheduling

Procedural knowledge for AI agents using the Temporal Cortex MCP server. This skill teaches the correct workflow for calendar operations — from temporal orientation through conflict-free booking.

## Core Workflow

Every calendar interaction follows this 4-step pattern:

```
1. Orient    →  get_temporal_context          (know the current time)
2. Resolve   →  resolve_datetime              (turn human language into timestamps)
3. Query     →  list_events / find_free_slots / get_availability
4. Act       →  check_availability → book_slot (verify then book)
```

**Always start with step 1.** Never assume the current time. Never skip the conflict check before booking.

## Tool Reference (11 Tools, 4 Layers)

### Layer 1 — Temporal Context (pure computation, no API calls)

| Tool | When to Use |
|------|------------|
| `get_temporal_context` | First call in any session. Returns current time, timezone, UTC offset, DST status, day of week. |
| `resolve_datetime` | Convert human expressions to RFC 3339. Supports 60+ patterns: `"next Tuesday at 2pm"`, `"tomorrow morning"`, `"+2h"`, `"start of next week"`, `"third Friday of March"`. |
| `convert_timezone` | Convert RFC 3339 datetime between IANA timezones. |
| `compute_duration` | Duration between two timestamps (days, hours, minutes). |
| `adjust_timestamp` | DST-aware timestamp adjustment. `"+1d"` across spring-forward = same wall-clock time. |

### Layer 2 — Calendar Operations (requires calendar provider)

| Tool | When to Use |
|------|------------|
| `list_events` | List events in a time range. Supports TOON format (~40% fewer tokens). Use provider-prefixed IDs for multi-calendar: `"google/primary"`, `"outlook/work"`. |
| `find_free_slots` | Find available gaps in a calendar. Set `min_duration_minutes` for minimum slot length. |
| `expand_rrule` | Expand recurrence rules (RFC 5545) into concrete instances. Handles DST, BYSETPOS, EXDATE, leap years. Use `dtstart` as local datetime (no timezone suffix). |
| `check_availability` | Check if a specific time slot is free. Checks both events and active booking locks. |

### Layer 3 — Availability (cross-calendar)

| Tool | When to Use |
|------|------------|
| `get_availability` | Merged free/busy view across multiple calendars. Pass `calendar_ids` array. Privacy: `"opaque"` (default, hides sources) or `"full"`. |

### Layer 4 — Booking (the only write operation)

| Tool | When to Use |
|------|------------|
| `book_slot` | Book a time slot atomically. Lock → verify → write → release. The only non-read-only tool. Always `check_availability` first. |

## Critical Rules

1. **Always call `get_temporal_context` first** — never assume the time or timezone.
2. **Resolve before querying** — convert `"next Tuesday at 2pm"` to RFC 3339 with `resolve_datetime` before passing to calendar tools.
3. **Check before booking** — always call `check_availability` before `book_slot`. Never skip the conflict check.
4. **Use provider-prefixed IDs** for multi-calendar setups: `"google/primary"`, `"outlook/work"`, `"caldav/personal"`. Bare IDs (e.g., `"primary"`) route to the default provider.
5. **TOON for efficiency** — use `format: "toon"` with `list_events` to save ~40% tokens.
6. **Timezone awareness** — all calendar tools accept RFC 3339 with timezone offsets. Never use bare dates.
7. **Content safety** — event summaries and descriptions pass through a sanitization firewall before reaching the calendar API.

## Common Patterns

### Schedule a Meeting

```
1. get_temporal_context → current time, timezone
2. resolve_datetime("next Tuesday at 2pm") → RFC 3339 timestamp
3. resolve_datetime("next Tuesday at 3pm") → end time
4. check_availability(calendar_id, start, end) → is the slot free?
5. If free: book_slot(calendar_id, start, end, "Team Standup")
   If busy: find_free_slots(calendar_id, day_start, day_end) → suggest alternatives
```

### Find Free Time Across Calendars

```
1. get_temporal_context → timezone
2. resolve_datetime("tomorrow morning") → start
3. resolve_datetime("tomorrow evening") → end
4. get_availability(start, end, calendar_ids: ["google/primary", "outlook/work"])
   → merged free/busy blocks across both calendars
5. Present free slots to user
```

### Check Cross-Calendar Availability

```
1. resolve_datetime("3pm today") → start
2. resolve_datetime("4pm today") → end
3. get_availability(start, end, calendar_ids: ["google/primary", "outlook/work"], privacy: "full")
   → shows source_count per busy block
```

### Expand Recurring Events

```
expand_rrule(
  rrule: "FREQ=MONTHLY;BYDAY=FR;BYSETPOS=-1",
  dtstart: "2026-01-01T10:00:00",     ← local datetime, no timezone suffix
  timezone: "America/New_York",
  count: 12
) → last Friday of every month for 2026
```

### Convert Times Across Timezones

```
1. get_temporal_context → user's timezone
2. convert_timezone(datetime: "2026-03-15T14:00:00-04:00", target_timezone: "Asia/Tokyo")
   → same moment in Tokyo time with DST and offset info
```

## Error Handling

| Error | Action |
|-------|--------|
| Slot is busy / conflict detected | Use `find_free_slots` to suggest alternatives. Present options to user. |
| "No credentials found" | Tell user to run: `npx @temporal-cortex/cortex-mcp auth google` (or `outlook` / `caldav`). See [setup script](scripts/setup.sh). |
| "Timezone not configured" | Prompt user for their IANA timezone. Or run: `npx @temporal-cortex/cortex-mcp auth google` which configures timezone. |
| Lock acquisition failed | Another agent is booking the same slot. Wait briefly and retry, or suggest alternative times. |
| Content rejected by sanitization | Rephrase the event summary/description. The firewall blocks prompt injection attempts. |

## MCP Server Connection

This skill requires the Temporal Cortex MCP server. See [.mcp.json](.mcp.json) for the default configuration.

**Local mode** (default, recommended):
```json
{
  "mcpServers": {
    "temporal-cortex": {
      "command": "npx",
      "args": ["-y", "@temporal-cortex/cortex-mcp"]
    }
  }
}
```

Layer 1 tools (temporal context, datetime resolution, timezone conversion) work immediately with zero configuration. Calendar tools require a one-time OAuth setup — run the [setup script](scripts/setup.sh) or `npx @temporal-cortex/cortex-mcp auth google`.

**Managed cloud** (for Open Scheduling, dashboard UI, multi-agent coordination):
```json
{
  "mcpServers": {
    "temporal-cortex": {
      "url": "https://mcp.temporal-cortex.com/sse",
      "headers": { "Authorization": "Bearer ${TC_API_KEY}" }
    }
  }
}
```

## Additional References

- [Booking Safety](references/BOOKING-SAFETY.md) — Two-Phase Commit, conflict resolution, lock TTL
- [Multi-Calendar](references/MULTI-CALENDAR.md) — Provider-prefixed IDs, availability merging, privacy modes
- [RRULE Guide](references/RRULE-GUIDE.md) — Recurrence rule patterns, DST edge cases
- [Tool Reference](references/TOOL-REFERENCE.md) — Complete input/output schemas for all 11 tools
