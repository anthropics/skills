# Tool Reference

Complete input/output schemas for all 11 MCP tools. All datetime parameters use RFC 3339 format.

## Tool Annotations

| Tool | `readOnlyHint` | `destructiveHint` | `idempotentHint` | `openWorldHint` |
|------|:-:|:-:|:-:|:-:|
| `get_temporal_context` | true | false | true | false |
| `resolve_datetime` | true | false | true | false |
| `convert_timezone` | true | false | true | false |
| `compute_duration` | true | false | true | false |
| `adjust_timestamp` | true | false | true | false |
| `list_events` | true | false | true | true |
| `find_free_slots` | true | false | true | true |
| `expand_rrule` | true | false | true | false |
| `check_availability` | true | false | true | true |
| `get_availability` | true | false | true | true |
| `book_slot` | **false** | false | **false** | true |

Layer 1 tools and `expand_rrule` are closed-world (no external API calls). All tools except `book_slot` are read-only and idempotent.

---

## get_temporal_context

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `timezone` | string | No | IANA timezone override |

**Output:** `utc`, `local`, `timezone`, `timezone_configured`, `utc_offset`, `dst_active`, `day_of_week`, `iso_week`, `is_weekday`, `day_of_year`, `week_start`

---

## resolve_datetime

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `expression` | string | Yes | Human time expression |
| `timezone` | string | No | IANA timezone override |

**Supported expressions:** `"now"`, `"today"`, `"tomorrow"`, `"yesterday"`, `"next Monday"`, `"this Friday"`, `"morning"` (09:00), `"noon"`, `"evening"` (18:00), `"eob"` (17:00), `"2pm"`, `"14:00"`, `"+2h"`, `"-30m"`, `"in 2 hours"`, `"3 days ago"`, `"next Tuesday at 2pm"`, `"tomorrow morning"`, `"start of week"`, `"end of month"`, `"start of next week"`, `"end of last month"`, `"first Monday of March"`, `"third Friday of next month"`, RFC 3339 passthrough.

**Output:** `resolved_utc`, `resolved_local`, `timezone`, `interpretation`

---

## convert_timezone

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `datetime` | string | Yes | RFC 3339 datetime |
| `target_timezone` | string | Yes | Target IANA timezone |

**Output:** `utc`, `local`, `timezone`, `utc_offset`, `dst_active`

---

## compute_duration

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `start` | string | Yes | First timestamp (RFC 3339) |
| `end` | string | Yes | Second timestamp (RFC 3339) |

**Output:** `total_seconds`, `days`, `hours`, `minutes`, `seconds`, `human_readable`

---

## adjust_timestamp

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `datetime` | string | Yes | RFC 3339 datetime |
| `adjustment` | string | Yes | Duration: `"+2h"`, `"-30m"`, `"+1d2h30m"` |
| `timezone` | string | No | IANA timezone for day-level adjustments |

DST-aware: `"+1d"` across spring-forward maintains same wall-clock time.

**Output:** `original`, `adjusted_utc`, `adjusted_local`, `adjustment_applied`

---

## list_events

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `calendar_id` | string | Yes | Calendar ID (supports provider prefix) |
| `start` | string | Yes | Range start (RFC 3339) |
| `end` | string | Yes | Range end (RFC 3339) |
| `format` | string | No | `"json"` (default) or `"toon"` (~40% fewer tokens) |

**Output:** `content`, `format`, `count`

---

## find_free_slots

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `calendar_id` | string | Yes | Calendar ID (supports provider prefix) |
| `start` | string | Yes | Window start (RFC 3339) |
| `end` | string | Yes | Window end (RFC 3339) |
| `min_duration_minutes` | integer | No | Minimum slot length (default: 30) |

**Output:** `slots` (array of `{start, end, duration_minutes}`), `count`

---

## expand_rrule

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `rrule` | string | Yes | RFC 5545 RRULE string |
| `dtstart` | string | Yes | Local datetime (no timezone suffix) |
| `timezone` | string | Yes | IANA timezone |
| `duration_minutes` | integer | No | Instance duration (default: 60) |
| `count` | integer | No | Max instances to return |

**Output:** `instances` (array of `{start, end}`), `count`

---

## check_availability

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `calendar_id` | string | Yes | Calendar ID (supports provider prefix) |
| `start` | string | Yes | Slot start (RFC 3339) |
| `end` | string | Yes | Slot end (RFC 3339) |

**Output:** `available` (boolean)

---

## get_availability

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `start` | string | Yes | Window start (RFC 3339) |
| `end` | string | Yes | Window end (RFC 3339) |
| `calendar_ids` | string[] | No | Calendar IDs (default: `["primary"]`) |
| `min_free_slot_minutes` | integer | No | Min free slot (default: 30) |
| `privacy` | string | No | `"opaque"` (default) or `"full"` |

**Output:** `busy` (array of `{start, end, source_count}`), `free` (array of `{start, end, duration_minutes}`), `calendars_merged`, `privacy`

---

## book_slot

**Input:**

| Param | Type | Required | Description |
|-------|------|----------|-------------|
| `calendar_id` | string | Yes | Calendar ID (supports provider prefix) |
| `start` | string | Yes | Event start (RFC 3339) |
| `end` | string | Yes | Event end (RFC 3339) |
| `summary` | string | Yes | Event title |
| `description` | string | No | Event description |
| `attendees` | string[] | No | Attendee email addresses |

**Output:** `success`, `event_id`, `booking_id`, `summary`, `start`, `end`

See [BOOKING-SAFETY.md](BOOKING-SAFETY.md) for the Two-Phase Commit protocol.
