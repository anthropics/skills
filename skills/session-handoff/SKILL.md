---
name: session-handoff
description: "Generates a structured handoff note at the end of a Claude Code session so the next session can resume without reconstructing context from scratch. Invoke when the user says done, stopping, wrapping up, done for now, that's it, context is running low, or when session continuity is needed. Creates a persistent handoff file covering what happened, what's in progress, decisions made, files modified, blockers, and the single recommended next action."
metadata:
  version: 1.0.0
  author: Assaf Kipnis
  license: Apache-2.0
---

# Session Handoff Skill (`/q-handoff`)

> Formal session-end message for the next session. Ensures continuity across context window resets.

## Purpose

When a session is about to end (context running low, user says "done for now", or natural stopping point), generate a handoff note that the NEXT session can read to pick up exactly where this one left off.

## When to trigger
- User says "done", "stopping", "that's it for now", "wrapping up"
- Context window is >80% consumed
- After `/q-wrap` completes
- Before any expected context compaction

## Handoff note structure

Save to your project's handoff file (e.g., `memory/last-handoff.md`, overwritten each time):

```markdown
# Session Handoff - [date] [time]

## What happened this session
- [Bullet list of key actions taken, decisions made, files changed]

## In-progress work
- [Anything started but not finished]
- [Current state of any multi-step task]

## Decisions made
- [Any positioning, strategy, or process decisions with origin tags]

## Files modified
- [List of files changed this session, one per line]

## Blocked / needs attention
- [Anything that couldn't be completed and why]

## Suggested next action
- [The single most important thing to do when the next session starts]
```

## Rules
- Keep it under 30 lines. The next session reads this on startup to restore context.
- Be specific. "Updated talk-tracks.md" not "made some changes."
- Include file paths so the next session can verify.
- If nothing is in-progress, say so. Clean handoffs are good.
- The handoff note is for CLAUDE, not for the founder. Write it as system context.
