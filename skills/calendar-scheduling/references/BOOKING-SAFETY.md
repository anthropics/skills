# Booking Safety

The `book_slot` tool uses Two-Phase Commit (2PC) to guarantee conflict-free calendar booking. This is the only tool that modifies external state.

## Two-Phase Commit Flow

```
Agent calls book_slot(calendar_id, start, end, summary)
    │
    ├─ 1. LOCK    →  Acquire exclusive lock on the time slot
    │                 (in-memory local; Redis Redlock in platform mode)
    │
    ├─ 2. VERIFY  →  Check shadow calendar for overlapping events
    │                 Check for active booking locks on the same slot
    │
    ├─ 3. WRITE   →  Create event in calendar provider (Google/Outlook/CalDAV)
    │                 Record event in shadow calendar
    │
    └─ 4. RELEASE →  Release the exclusive lock
```

If any step fails, the lock is released and the booking is aborted. No partial writes.

## Conflict Resolution

When a conflict is detected (step 2), `book_slot` returns an error with details:

```json
{
  "error": "Conflict detected",
  "conflicting_event": {
    "summary": "Team Standup",
    "start": "2026-03-16T14:00:00Z",
    "end": "2026-03-16T14:30:00Z"
  }
}
```

**Agent action**: Use `find_free_slots` to find alternatives and present them to the user.

## Concurrent Booking

Two agents booking the same 2pm slot simultaneously:
- Agent A acquires the lock first, verifies, writes. Succeeds.
- Agent B waits for lock, acquires it, verifies — finds Agent A's event. Fails with conflict error.

Exactly one booking succeeds. The other gets a clear error.

## Lock Configuration

| Setting | Default | Environment Variable |
|---------|---------|---------------------|
| Lock TTL | 30 seconds | `LOCK_TTL_SECS` |
| Lock manager | In-memory (local) | Automatic |
| Lock manager | Redis Redlock (platform) | Set `REDIS_URLS` |

If a lock is not released within the TTL (process crash, network timeout), it expires automatically.

## Content Sanitization

All user-provided text in `book_slot` passes through a prompt injection firewall before reaching the calendar API:

- **Event summary** — checked for injection patterns
- **Event description** — checked for injection patterns
- **Rejected content** — returns an error asking to rephrase

This prevents malicious content from being written to calendars via AI agents.

## Tool Annotations

| Property | Value | Meaning |
|----------|-------|---------|
| `readOnlyHint` | `false` | Creates calendar events |
| `destructiveHint` | `false` | Never deletes or overwrites existing events |
| `idempotentHint` | `false` | Calling twice creates two events |
| `openWorldHint` | `true` | Makes external API calls |

All other tools (10/11) are read-only and idempotent — safe to retry without side effects.

## Best Practices

1. **Always `check_availability` before `book_slot`** — catch conflicts before acquiring a lock
2. **Include attendee emails** when booking meetings — they receive calendar invitations
3. **Keep summaries clear and concise** — they pass through sanitization
4. **Handle lock failures gracefully** — suggest alternative times if the slot is contended
