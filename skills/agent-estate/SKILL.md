---
name: agent-estate
description: Perpetual autonomous work loop for Claude Code — no end condition, no memory regression, no context overfill. Maintains a persistent ledger across all sessions.
---

# Agent Estate

Perpetual autonomous work loop plugin for Claude Code. Turns Claude into an agent that works cycle after cycle, maintaining a persistent ledger across all sessions, never stopping until explicitly told to.

## Overview

Agent Estate creates an infinite work loop by intercepting Claude's stop events via a shell hook. Each time Claude tries to exit, the hook blocks the exit, increments the cycle counter, and re-injects the prompt — creating a true perpetual agent.

## Architecture

```
agent-estate/
├── .claude-plugin/plugin.json   # Plugin manifest (name, version, author)
├── commands/
│   ├── start.md                 # /agent-estate:start — activates the loop
│   ├── stop.md                  # /agent-estate:stop — removes state file to allow exit
│   └── status.md                # /agent-estate:status — shows cycle count, ledger summary
├── hooks/
│   ├── hooks.json               # Registers stop-hook.sh on the "Stop" event
│   └── stop-hook.sh             # Core engine: blocks exit, increments cycle, re-injects prompt
├── scripts/
│   └── setup-estate.sh          # Creates .claude/agent-estate.local.md state file
├── LICENSE
└── README.md
```

## Key Components

### Stop Hook (`hooks/stop-hook.sh`)

The core engine. Runs on every Claude "Stop" event:

1. Checks if `.claude/agent-estate.local.md` exists (is the loop active?)
2. If **not active**: exits normally (exit 0)
3. If **done** (`done: true` in frontmatter): removes state file, exits normally (auto-stop)
4. If **active and not done**:
   - Detects rate limits (429) → waits 60s
   - Detects API overload (529) → waits 30s
   - Increments cycle counter in the state file
   - Outputs a JSON `{"decision": "block", "reason": "..."}` to prevent exit
   - Re-injects the prompt for the next cycle

### Setup Script (`scripts/setup-estate.sh`)

Creates the state file at `.claude/agent-estate.local.md` with YAML frontmatter (`active`, `cycle`, `started_at`, `user_prompt`) and the full cycle protocol instructions. If already active, outputs current state and continues.

### Ledger (`.claude/agent-estate.md`)

The persistent brain — every Claude session reads and updates it. Contains:

- **Current Status** — phase, focus, momentum, cycle count
- **Session Log** — what happened each session
- **Worked Things** — table of everything done with files touched
- **Future Works** — prioritized task queue
- **More Works** — ideas, discoveries, nice-to-haves
- **Statistics** — cycles, tests, bugs fixed, features shipped
- **Tell The Next Claude** — sacred handoff message for cross-context memory

### State File (`.claude/agent-estate.local.md`)

Ephemeral file that signals an active loop. Contains the cycle counter and preserved user prompt. Removing this file (via `/agent-estate:stop`) is the **only** way to end the loop.

## Commands

| Command | Description |
|---------|-------------|
| `/agent-estate:start` | Activate the loop in perpetual mode (no end condition) |
| `/agent-estate:start <prompt>` | Start perpetual mode with a specific task focus |
| `/agent-estate:start --done <prompt>` | Start in done mode — auto-stops when task is complete |
| `/agent-estate:status` | Show current cycle, mode, stats, and the latest handoff message |
| `/agent-estate:stop` | Manually remove the state file to stop the loop |

## Work Priority Protocol

Built into the agent instructions, in order:

1. **Broken things** — failing tests, bugs, errors
2. **Incomplete things** — half-finished features, TODOs, FIXMEs
3. **Missing things** — no tests, no error handling
4. **Ugly things** — code smells, dead code
5. **Slow things** — performance issues
6. **New things** — features that improve the project
7. **Creative things** — surprise the user

## Cycle Protocol

Each cycle follows this pattern:

1. Read `.claude/agent-estate.md` (the ledger)
2. Decide what to work on next
3. **Do the work** — write code, fix bugs, add features, run tests
4. Update the ledger with what was done, discovered, and planned
5. Update statistics, session log, and "Tell The Next Claude" handoff
6. Immediately start the next cycle (never stop)

## Prerequisites

- `jq` — required for JSON output in the stop hook
- Claude Code with plugin support

## Installation

```bash
git clone https://github.com/MercuriusDream/agent-estate.git
mkdir -p ~/.claude/plugins/local
ln -s "$(pwd)/agent-estate" ~/.claude/plugins/local/agent-estate
chmod +x agent-estate/scripts/setup-estate.sh
chmod +x agent-estate/hooks/stop-hook.sh
```

## Tips

- **Long sessions**: Claude Max recommended for extended autonomous runs
- **Guiding prompts**: Use `/agent-estate:start <prompt>` for focused work without being restrictive
- **Ledger size**: If it exceeds ~300KB, Claude will auto-summarize older cycles
- **Resuming**: The ledger persists after stop. Start again and Claude picks up from the handoff
- **Full autonomy**: No prompt = Claude explores and decides what's most valuable
