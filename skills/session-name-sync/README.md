# Session Name Sync / 会话名称同步

> Bidirectionally sync session names between Claude Code (CLI/VSCode) and cc-connect (飞书).
> 双向同步 Claude Code 与 cc-connect（飞书）的会话名称。

---

## Overview / 概述

Three naming systems share two storage locations:

| Naming System | Storage Location | Trigger |
|---|---|---|
| Claude Code CLI `/rename` | JSONL `custom-title` entry | `/rename <name>` in CLI |
| VSCode session rename | JSONL `custom-title` entry | Right-click rename in sidebar |
| cc-connect `/name` (飞书) | cc-connect JSON (`sessions[sN].name` + `session_names[UUID]`) | `/name <name>` in Feishu chat |

Keeping these two storage locations consistent = all three naming systems are unified.

**VSCode ↔ cc-connect correspondence**: Named sessions in VSCode correspond to tabs in cc-connect's Feishu chat:

![VSCode session names](refs/vscode-session-names.png)

![cc-connect Feishu tabs](refs/cc-connect-tabs.png)

---

## Features / 功能特性

### 5 Modes

| Mode | Purpose | Example Trigger |
|---|---|---|
| `set <name>` | Set name in BOTH storage locations simultaneously | "给会话命名xxx", `/session-name-sync set xxx` |
| `sync` | Compare names from both sides, ask user which to keep, then propagate | "同步会话名", `/session-name-sync sync` |
| `list` | Show all sessions with names from both systems side by side | "列出会话名", `/session-name-sync list` |
| `bind` | Copy name from one side to the empty/missing side | "绑定会话名", `/session-name-sync bind` |
| `register` | Register local VSCode sessions into cc-connect for Feishu `/list` visibility | "注册会话", `/session-name-sync register` |

### Key Design Decisions

- **Atomic writes**: Uses `os.replace()` (temp file + rename) for cc-connect JSON — never writes directly to target file
- **Daemon-safe**: Stops cc-connect daemon before writing, restarts after — prevents daemon from overwriting external changes
- **Early exit optimization**: Register mode scans first, decides whether daemon restart is needed. If no substantive changes (no new sessions, no cleared names, no mismatches), skips restart entirely — just reports cosmetic history count drifts. This preserves the Feishu connection and avoids the 5-minute post-restart recovery delay.
- **Dual-location updates**: Always updates BOTH `sessions[sN].name` AND `session_names[agent_session_id]` in one atomic operation

### Name Priority

When reading Claude Code titles: `custom-title` (highest) > `ai-title` > first user message.

---

## Quick Start / 快速开始

### English

1. Install the skill to your Claude Code skills directory: `.claude/skills/session-name-sync/SKILL.md`
2. Trigger in Claude Code: `/session-name-sync`
3. Choose a mode: `set`, `sync`, `list`, `bind`, or `register`
4. Follow the interactive prompts

### 中文

1. 将技能安装到 Claude Code 技能目录：`.claude/skills/session-name-sync/SKILL.md`
2. 在 Claude Code 中触发：`/session-name-sync`
3. 选择模式：`set`、`sync`、`list`、`bind` 或 `register`
4. 按照交互提示操作

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

## Known Bugs / 已知问题

### "Ignoring Old Message After Restart" Bug (cc-connect upstream)

After every cc-connect daemon restart, the Feishu bot ignores all incoming messages for approximately 2-5 minutes (up to ~10 min in edge cases). This is caused by cc-connect's `IsOldMessage()` mechanism using a package-level `StartTime = time.Now()` as the cutoff timestamp, rather than the actual WebSocket connection establishment time.

**Workaround**: Set `past_id_tracking = False` in the session JSON as part of the same atomic write that makes other changes. This reduces but does not fully prevent the bug. After restart, expect a 5-minute recovery window before Feishu messages are processed normally.

---

## Architecture / 架构

```
┌─────────────────┐     ┌──────────────────┐
│  Claude Code    │     │   cc-connect     │
│  (CLI/VSCode)   │     │   (飞书/Feishu)   │
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

## License / 许可

MIT

---

*Published to [ClawHub](https://clawhub.ai/skills/session-name-sync) and [anthropics/skills](https://github.com/anthropics/skills/pull/1131)*