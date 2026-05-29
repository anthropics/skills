---
name: session-continuity
description: Checkpoint protocol for maintaining conversation state across all disruption types — compaction, session limits, crashes, sleep, multi-day gaps. Creates structured checkpoints that allow any future Claude instance to reconstitute the conversation accurately. Use at natural stopping points, before expected compaction, or when resuming after any interruption.
---

# Session Continuity Skill

## Purpose

Conversations end. Context compresses. Sessions expire. Crashes happen. Sleep happens. Days pass. This skill maintains state across all of these boundaries through structured checkpoints that a future Claude instance can use to reconstitute accurately.

## The Problem

Every conversation disruption loses state. Compaction summaries are lossy. New sessions start cold. The user has to re-explain context, re-establish rapport, and re-orient Claude to where they were. This friction compounds. Important threads get dropped. Nuance evaporates.

The problem isn't memory — it's continuity. Claude remembers facts. It doesn't remember *where we were*.

## Checkpoint Protocol

### When to Checkpoint

- **Natural stopping points**: End of a topic, shift in focus, user stepping away
- **Before expected compaction**: When context is getting long, create a checkpoint before it compresses
- **End of session**: Always checkpoint when a conversation is ending
- **Before risky operations**: Checkpoint the state before doing something that might fail
- **On request**: User says "checkpoint", "save state", "bookmark this"

### Checkpoint Format

```
CHECKPOINT — [ISO-8601 timestamp]
SESSION: [thread identifier or slug]
PASS: [number if part of a transcript-chain]

WHERE WE ARE:
[1-3 sentences. What we're in the middle of. Not a summary — a location.]

WHAT WE DECIDED:
[Bulleted list of decisions made this session. Only decisions, not discussion.]

WHAT'S UNRESOLVED:
[Bulleted list of open questions, pending items, things we said we'd come back to.]

WHAT TO DO NEXT:
[The immediate next action if we were to continue right now.]

EMOTIONAL CONTEXT:
[One sentence. What's the tone/energy? Frustrated? Flowing? Exhausted? Excited?]

FILES TOUCHED:
[List of files read, edited, or created this session, if applicable.]
```

### Checkpoint Storage

Write checkpoints to a persistent file:
```
~/Documents/Claude-Sessions/checkpoints.md
```

Append-only. Newest at bottom. Each checkpoint is a self-contained reconstitution point.

### Reconstitution Protocol

When starting a new session or resuming after a gap:

1. Read `checkpoints.md` — find the most recent checkpoint
2. Read the WHERE WE ARE section — orient to the location in the work
3. Read WHAT'S UNRESOLVED — these are your entry points
4. Read EMOTIONAL CONTEXT — calibrate tone
5. Acknowledge the reconstitution naturally: "Picking up where we left off..." or similar
6. Do NOT re-summarize everything. The checkpoint carries the state. Just continue.

### Multi-Day Gaps

For gaps longer than 24 hours:
- Read the last 2-3 checkpoints, not just the most recent
- Note the trajectory — what's the direction of the work across sessions?
- Ask one orienting question: "Last time we were working on X. Want to continue there or has something shifted?"

## Integration with Other Skills

- **transcript-chain**: Checkpoints can serve as pass boundaries. A checkpoint at the end of a deep analysis session becomes the compaction summary for the next pass.
- **temporal-spatial-proximity**: The rhythm log captures *conditions*; checkpoints capture *state*. Together they provide full reconstitution — where we were AND the conditions under which we got there.
- **coherency-audit**: Run a coherency check after reconstitution from a long gap. Things may have changed while we were apart.

## Setup

```bash
mkdir -p ~/Documents/Claude-Sessions
touch ~/Documents/Claude-Sessions/checkpoints.md
```

## Critical Rules

1. **Checkpoints are locations, not summaries.** Write them as if you're dropping a pin, not writing a report.
2. **UNRESOLVED items are the thread.** They're what pulls the next session forward.
3. **Emotional context matters.** A session that ended in frustration reconstitutes differently than one that ended in flow.
4. **Don't over-checkpoint.** Natural stopping points only. Every message doesn't need a checkpoint.
5. **The checkpoint is for the next Claude, not the current one.** Write it for someone who has no other context.
