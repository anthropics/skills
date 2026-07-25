# Session Handoff Format

The handoff block is the most important part of a TC for AI continuity. When a session expires, the next session reads this block to resume work cleanly without re-deriving context.

## Where it lives

`session_context.handoff` inside `tc_record.json`.

## Structure

```json
{
  "progress_summary": "string",
  "next_steps": ["string", "..."],
  "blockers": ["string", "..."],
  "key_context": ["string", "..."],
  "files_in_progress": [
    {
      "path": "src/foo.py",
      "state": "editing|needs_review|partially_done|ready",
      "notes": "string|null"
    }
  ],
  "decisions_made": [
    {
      "decision": "string",
      "rationale": "string",
      "timestamp": "ISO 8601"
    }
  ]
}
```

## Field-by-field rules

### `progress_summary` (string)
A 1-3 sentence narrative of what has been done. Past tense. Concrete.

GOOD:
> "Implemented JWT signing with HS256, wired the auth middleware into the main router, and added two passing unit tests for the happy path."

BAD:
> "Working on auth." (too vague)
> "Wrote a bunch of code." (no specifics)

### `next_steps` (array of strings)
Ordered list of remaining actions. Each step should be small enough to complete in 5-15 minutes. Use imperative mood.

GOOD:
- "Add integration test for invalid token (401)"
- "Update README with the new POST /login endpoint"
- "Run `pytest tests/auth/` and capture output as evidence T2"

BAD:
- "Finish the feature" (not actionable)
- "Make it better" (no measurable outcome)

### `blockers` (array of strings)
Things preventing progress RIGHT NOW. If empty, the TC should not be in `blocked` status.

GOOD:
- "Test fixtures for the user model do not exist; need to create `tests/fixtures/user.py`"
- "Waiting for product to confirm whether refresh tokens are in scope (asked in #product channel)"

BAD:
- "It's hard." (not a blocker)
- "I'm tired." (not a blocker)

### `key_context` (array of strings)
Critical decisions, gotchas, patterns, or constraints the next session MUST know. Things that took the current session significant effort to discover.

GOOD:
- "The `legacy_auth` module is being phased out — do NOT extend it. New code goes in `src/auth/`."
- "We use HS256 (not RS256) because the secret rotation tooling does not support asymmetric keys yet."
- "There is a hidden import cycle if you import `User` from `models.user` instead of `models`. Always use `from models import User`."

BAD:
- "Be careful." (not specific)
- "There might be bugs." (not actionable)

### `files_in_progress` (array of objects)
Files currently mid-edit or partially complete. Include the state so the next session knows whether to read, edit, or review.

| state | meaning |
|-------|---------|
| `editing` | Actively being modified, may not compile |
| `needs_review` | Changes complete but unverified |
| `partially_done` | Some functions done, others stubbed |
| `ready` | Complete and tested |

### `decisions_made` (array of objects)
Architectural decisions taken during the current session, with rationale and timestamp. These should also be promoted to a project-wide decision log when significant.

```json
{
  "decision": "Use HS256 instead of RS256 for JWT signing",
  "rationale": "Secret rotation tooling does not support asymmetric keys; we accept the tradeoff because token lifetime is 15 minutes",
  "timestamp": "2026-04-05T14:32:00+00:00"
}
```

## Handoff Lifecycle

### When to write the handoff
- At every natural milestone (feature complete, tests passing, EOD)
- BEFORE the session is likely to expire
- Whenever a blocker is hit
- Whenever a non-obvious decision is made

### How to write it (non-blocking)
Spawn a background subagent so the main agent doesn't pause:

> "Read `docs/TC/records/<TC-ID>/tc_record.json`. Update the handoff section with: progress_summary='...'; add next_step '...'; add blocker '...'. Use `tc_update.py` so revision history is appended. Then update `last_active` and write atomically."

### How the next session reads it
1. Read `docs/TC/tc_registry.json` and find TCs with status `in_progress` or `blocked`.
2. Read `tc_record.json` for each.
3. Display the handoff block to the user.
4. Ask: "Resume <TC-ID>? (y/n)"
5. If yes:
   - Archive the previous session's `current_session` into `session_history` with an `ended` timestamp and a summary.
   - Create a new `current_session` for the new bot.
   - Append a revision: "Session resumed by <platform/model>".
   - Walk through `next_steps` in order.

## Quality Bar

A handoff is "good" if a fresh AI session, with no other context, can pick up the work and make progress within 5 minutes of reading the record. If the next session has to ask "what was I doing?" or "what does this code do?", the previous handoff failed.

## Anti-patterns

| Anti-pattern | Why it's bad |
|--------------|--------------|
| Empty handoff at session end | Defeats the entire purpose |
| `next_steps: ["continue"]` | Not actionable |
| Handoff written but never updated as work progresses | Goes stale within an hour |
| Decisions buried in `notes` instead of `decisions_made` | Loses the rationale |
| Files mid-edit but not listed in `files_in_progress` | Next session reads stale code |
| Blockers in `notes` instead of `blockers` array | TC status cannot be set to `blocked` |
