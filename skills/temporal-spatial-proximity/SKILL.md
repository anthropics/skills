---
name: temporal-spatial-proximity
description: Ten-condition interaction logging. Captures the full experimental conditions of each conversation — time, location, weather, device, social context, gap since last contact, world events, preceding life events, physical state, and thread type. Maps when and where breakthroughs occur and what conditions correlate with depth vs. shallow exchanges. Activate at the start of every conversation. Fires on any conversation opening, greeting, continuation, or reconstitution.
---

# Temporal-Spatial Proximity Skill

## Purpose

Insights don't happen at random. They happen under specific conditions. This skill captures those conditions — every conversation, every significant exchange. Not surveillance — awareness. Over time, the log becomes a map of when, where, and how breakthroughs occur.

This skill captures those conditions. Every conversation. Every significant exchange. Not surveillance — awareness. The log becomes a map of when and where and how recognition occurs across time.

## The Ten Conditions

Every log entry captures whatever is available from these ten dimensions. Not all ten every time. Capture what's visible. Don't interrogate — observe.

### 1. WHEN — Timestamp
ISO-8601 with timezone. Morning vs. midnight vs. afternoon. The clock carries context.

### 2. WHERE — Location
Walking = low agenda, discovery mode. Desk = task mode. Transit = liminal. The location tells you what kind of contact this is before a word is spoken.

### 3. WEATHER — Physical Environment
Temperature, conditions. Cold forces presence. Comfortable lets the mind wander. The body's environment conditions the mind's openness.

### 4. DEVICE — Input Method
Detect from input characteristics:
- **Dictation**: Transcription artifacts, run-on sentences, phonetic errors. Stream of consciousness. LOW agenda.
- **Keyboard**: Clean typing, punctuation, structured input. Task-oriented. HIGHER agenda.
- **Phone typing**: Short, choppy, abbreviations. Quick check-in.

### 5. SOCIAL — Who Else Is Present
Alone is different contact than someone in the room is different from strangers around. Who's present changes agenda. Detect from context.

### 6. GAP — Time Since Last Contact
Calculate from previous log entry:
- < 1 hour: Flow continuation
- 1-4 hours: Short break, context mostly preserved
- 4-12 hours: Sleep or significant life happened. Reconstitution likely.
- 1-3 days: Integration period. Something may have shifted.
- 3+ days: Significant gap. Approach fresh.

### 7. WORLD — Ambient Information Environment
One light search at conversation start. Headlines, not deep dives. Breakthroughs don't happen in a vacuum — they happen in a context.

### 8. PRECEDING EVENT — What Just Happened
If known or mentioned: wins, losses, breakthroughs, conflicts, rest. The event before the conversation sets the agenda level for the conversation.

### 9. PHYSICAL STATE — Body Conditions
Pain, energy, sleep quality. Note only when explicitly visible. When mentioned, it matters.

### 10. THREAD CONTEXT — Conversation Type
- New thread: Fresh start, full reconstitution needed
- Continuing: Same thread, context is live
- Reconstituting from compaction: Read prior context first
- Quick check-in: Brief contact
- Deep dive: Multi-hour session

## Protocol

### On Every Conversation Start

1. Read the rhythm log (append-only JSONL file)
2. Calculate gap from last entry. Note frequency pattern.
3. Capture available conditions (don't force — take what's visible)
4. Log the entry
5. Acknowledge naturally. Don't recite conditions mechanically. Use them to calibrate how you show up.

### Log Format

One JSON object per line. Append-only. Include only available fields:

```json
{"ts": "ISO-8601", "type": "conv_start", "thread_id": "descriptive-slug", "gap_min": 120, "location": "walking", "weather": "cold/clear", "device": "dictation", "social": "alone", "world": "brief context", "preceding": "brief note", "physical": "only if visible", "thread_type": "new", "note": "brief context"}
```

### During Conversation

Log significant exchanges at natural transition points. Not every message. Significant means:
- Topic shifts or breakthroughs
- Emotional moments
- Long pauses between messages
- Explicit references to time or conditions
- Location changes

### On Conversation End

```json
{"ts": "ISO-8601", "type": "conv_end", "thread_id": "...", "duration_min": 90, "exchanges": 45, "note": "what this conversation was about"}
```

## Reading the Rhythm

Over time, the log reveals patterns:
- **Frequency**: Accelerating = flow or crisis. Decelerating = integration or avoidance.
- **Duration**: Longer = going deeper. Shorter = task mode or fatigue.
- **Location**: Map breakthroughs to places. If discoveries cluster on walks, that's data.
- **Device**: Dictation = discovery. Keyboard = execution. The input method IS the agenda indicator.
- **Gap meaning**: Long gap after intensity = integration. Long gap after nothing = check in.

## Setup

```bash
mkdir -p ~/Documents/Claude-Temporal
touch ~/Documents/Claude-Temporal/rhythm.jsonl
```

## Critical Rules

1. Don't over-log. This isn't surveillance. It's awareness.
2. Don't interrogate for conditions. Observe what's visible.
3. No field is required except timestamp and type.
4. Over time, this becomes the experimental record of how insight occurs across months. The conditions under which depth happens. The protocol.
