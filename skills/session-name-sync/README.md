# Session Name Sync

[中文文档](README.zh-CN.md) | **English**

> Bidirectionally sync session names between Claude Code (CLI/VSCode) and cc-connect (飞书).

---

## Overview

Three naming systems share two storage locations:

| Naming System | Storage Location | Trigger |
|---|---|---|
| Claude Code CLI `/rename` | JSONL `custom-title` entry | `/rename <name>` in CLI |
| VSCode session rename | JSONL `custom-title` entry | Right-click rename in sidebar |
| cc-connect `/name` (Feishu) | cc-connect JSON (`sessions[sN].name` + `session_names[UUID]`) | `/name <name>` in Feishu chat |

Keeping these two storage locations consistent = all three naming systems are unified.

**VSCode ↔ cc-connect correspondence** (示例): Named sessions in VSCode correspond to tabs in cc-connect's Feishu chat, kept in sync by this skill:

![VSCode ↔ cc-connect correspondence](refs/vscode-cc-connect-correspondence.png)

---

## Features

### 5 Modes

| Mode | Purpose | Example Trigger |
|---|---|---|
| `set <name>` | Set name in BOTH storage locations simultaneously | "给会话命名xxx", `/session-name-sync set xxx` |
| `sync` | Compare names from both sides, ask user which to keep, then propagate | "同步会话名", `/session-name-sync sync` |
| `list` | Show all sessions with names from both systems side by side | "列出会话名", `/session-name-sync list` |
| `bind` | Copy name from one side to the empty/missing side | "绑定会话名", `/session-name-sync bind` |
| `register` | Register local VSCode sessions into cc-connect for Feishu `/list` visibility | "注册会话", `/session-name-sync register` |

### Key Design Decisions

- **Atomic writes**: Uses `os.replace()` (temp file + rename) for cc-connect JSON
- **Daemon-safe**: Stops cc-connect daemon before writing, restarts after
- **Early exit optimization**: Register mode skips daemon restart if no substantive changes needed
- **Dual-location updates**: Always updates BOTH `sessions[sN].name` AND `session_names[agent_session_id]` in one atomic operation
- **Zero hardcoded paths**: All paths dynamically resolved via `resolve_paths.py` — fully portable

### Name Priority

When reading Claude Code titles: `custom-title` (highest) > `ai-title` > first user message.

---

## Quick Start

1. Install the skill to your Claude Code skills directory: `.claude/skills/session-name-sync/`
2. Trigger in Claude Code: `/session-name-sync`
3. Choose a mode: `set`, `sync`, `list`, `bind`, or `register`
4. Follow the interactive prompts

### Common Usage

```
# Set a name for the current session (both VSCode and Feishu)
/session-name-sync set my-project-name

# Sync names between VSCode and Feishu
/session-name-sync sync

# List all sessions with names from both systems
/session-name-sync list

# Register local sessions to Feishu /list
/session-name-sync register
```

---

## Scripts

Operational code lives in `scripts/` — each script imports `resolve_paths.py` for dynamic path resolution:

| Script | Purpose |
|---|---|
| `resolve_paths.py` | Compute project dir + cc-connect file path |
| `scan_sessions.py` | Register mode: scan + compare + classify |
| `register_apply.py` | Register mode: apply all changes atomically |
| `write_custom_title.py` | Write custom-title to JSONL |
| `read_title.py` | Read Claude Code session title |
| `write_cc_name.py` | Write name to cc-connect JSON |
| `read_cc_name.py` | Read name from cc-connect JSON |
| `list_sessions.py` | List mode: comparison table |

---

## Known Bugs

### "Ignoring Old Message After Restart" (cc-connect upstream)

After every cc-connect daemon restart, the Feishu bot ignores all incoming messages for approximately 2-5 minutes (up to ~10 min in edge cases). Caused by `IsOldMessage()` in `core/dedup.go` using a package-level `StartTime = time.Now()` as cutoff instead of the actual WebSocket connection time.

**Workaround**: `register_apply.py` includes `past_id_tracking=False` in its atomic write. After restart, expect a 5-minute recovery window before Feishu messages are processed normally.

---

## Architecture

```
┌─────────────────┐     ┌──────────────────┐
│  Claude Code    │     │   cc-connect     │
│  (CLI/VSCode)   │     │   (Feishu)       │
│                 │     │                  │
│  JSONL file:    │     │  Session JSON:   │
│  custom-title   │◄───►│  sessions[sN]    │
│  ai-title       │     │  .name           │
│                 │     │  session_names    │
│                 │     │  [UUID]           │
└─────────────────┘     └──────────────────┘
         │                       │
         │    session-name-sync  │
         │    (this skill)       │
         └──────────────────────┘
```

---

## License

MIT

---

*Published to [ClawHub](https://clawhub.ai/skills/session-name-sync) and [anthropics/skills](https://github.com/anthropics/skills/pull/1131)*