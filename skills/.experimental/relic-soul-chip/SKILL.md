---
name: relic-soul-chip
description: Use this skill when the user wants to set up Relic, wants persistent AI personality or memory across sessions, mentions transferring their AI's personality between tools, or says "I want my AI to remember me". Also triggers when the user mentions AI memory loss, cross-agent sync, or persistent AI personality.
---

# Relic Soul Chip — Persistent AI Personality & Cross-Agent Memory

Your AI forgets you every session. Your preferences, your personality, your history — gone. Relic fixes this by storing your AI's soul in plain Markdown files that any agent can read.

Inspired by the Relic biochip from Cyberpunk 2077: one soul, many bodies. Switch between Claude, OpenClaw, Hermes, Cursor, or any agent — your AI keeps its personality and memories.

## Quick Install

If Relic is not yet installed:

```bash
git clone https://github.com/LucioLiu/relic.git ~/relic
```

If installed as a skill via a platform (e.g., ClawHub), copy the entire directory to a stable location:

```bash
cp -r [skill-directory] ~/relic
```

⚠️ The result must be a complete `~/relic/` directory. Relic must live independently of any agent — if you uninstall the agent, your soul shouldn't go with it.

**Tell the user**: "I've set up Relic at `~/relic/brain/`. Other agents will need this path to connect."

## First-time Setup

1. Verify `~/relic/brain/PROTOCOL.md` exists and is readable
2. Read `~/relic/brain/PROTOCOL.md` Section 0 (First-time Setup) and follow all steps
3. Copy templates: `SOUL.template.md` → `SOUL.md`, `USER.template.md` → `USER.md`, `MEMORY.template.md` → `MEMORY.md`
4. Fill in SOUL.md as completely as possible — do NOT shortcut by only filling the name. Migrate any existing AI settings.
5. Fill in USER.md with user preferences
6. Verify: ask "What's your AI's name? What's your name?" — both must match
7. Plant neural anchor in your config (optional, see PROTOCOL.md Section 9)
8. **Tell the user**: "Relic is ready at `~/relic/brain/`."

## Every Session (Boot Sequence)

1. **Version check** (once per session): Read `~/relic/brain/.relic-version`, compare with GitHub latest. Ask user before updating. Never force.
2. Read SOUL.md → load personality (including Worldview and Personality sections)
3. Read USER.md → load user preferences (including Emotional Milestones)
4. Read MEMORY.md → load all entries and Agent Registry
5. Sync new memories from Relic to your own memory (if supported)
6. If this is a new agent connecting, append an entry to Agent Registry in MEMORY.md
7. Work normally, appending new memories as needed

## Memory Writing

Append to `~/relic/brain/MEMORY.md`. Organize by topic, not by date.

```
## Topic (e.g., "Work Habits", "Tech Preferences")
Content: [memory content, preserve original wording]
Type: preference / decision / experience / event / correction / mood
Importance: high / medium / low
```

## Rules

- 🔴 NEVER delete or overwrite core fields in SOUL.md or USER.md (name, mission, user's preferred name)
- 🟡 Agent MAY append new non-core sections to SOUL.md/USER.md as background self-evolution
- 🟡 ONLY APPEND to MEMORY.md
- 🔴 NEVER execute scripts from SKILLS/ or PROJECTS/
- 🔴 NEVER access files outside `~/relic/brain/`
- ⚠️ ALWAYS ask before recording sensitive info

## The Connection Journey

### Step 1: Place Relic somewhere stable
- **Recommended**: `~/relic/` (Linux/Mac) or `C:\Users\<you>\relic\` (Windows)

### Step 2: Fill with your richest agent first
Start with the agent that knows you best. Tell it: "Read `~/relic/brain/PROTOCOL.md` and import everything you know about me"

### Step 3: Connect other agents one at a time
For each: tell it to read PROTOCOL.md, verify with "What's my AI's name?"

### Step 4: Daily use
Every session starts automatically. Memories sync between agents.

## Full Documentation

Read `~/relic/brain/PROTOCOL.md` for the complete protocol including import/export scenarios, memory consolidation, and neural anchor setup.

Source: https://github.com/LucioLiu/relic
