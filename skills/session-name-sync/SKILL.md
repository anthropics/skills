---
name: session-name-sync
description: >
  Bidirectionally sync session names between Claude Code (CLI/VSCode) and cc-connect.
  Three naming systems share two storage locations: Claude Code CLI /rename and VSCode both
  read/write the JSONL custom-title entry; cc-connect /name writes its own JSON file.
  This skill unifies all three by keeping both storage locations consistent.
  Use when: (1) User says "给会话命名", "命名会话", "会话名", "session name";
  (2) User says "sync 会话名", "同步会话名", "绑定会话名";
  (3) User invokes /session-name-sync;
  (4) User wants to list or compare session names across VSCode/CLI and cc-connect;
  (5) User sets a name in cc-connect and wants it reflected in VSCode/CLI, or vice versa.
  Modes: set <name> | sync | list | bind | register
version: 1.0.0
author: Xiaowangzi
license: MIT
trigger: 给会话命名, session name, sync 会话名, 会话名同步, /session-name-sync, rename 会话, 注册会话, register sessions
---

# Session Name Sync

Bidirectionally sync session names between Claude Code (CLI + VSCode) and cc-connect (飞书).

## Environment Check

**Before executing any mode, run this first:**

1. Run: `python3 scripts/check_env.py` — check if cc-connect and VSCode Claude Code extension are installed
2. If any dependency is missing, run: `python3 scripts/check_env.py --install` — auto-install latest versions
3. Proceed only after all dependencies are confirmed OK

Dependencies:
- **cc-connect**: npm global package (`npm install -g cc-connect`)
- **VSCode Claude Code extension**: `anthropic.claude-code` (`code --install-extension anthropic.claude-code`)

Three naming systems → two storage locations:
- **Claude Code CLI `/rename`** and **VSCode** → both read/write JSONL `custom-title` entry
- **cc-connect `/name`** (飞书) → writes own JSON file (`sessions[sN].name` + `session_names[UUID]`)

Keeping these two storage locations consistent = all three naming systems are unified.

## Scripts

All operational code is in `scripts/` directory. Each script imports `resolve_paths.py` to dynamically compute `cc_project_dir` and `cc_file` from the current environment — zero hardcoded paths.

| Script | Purpose | Usage |
|---|---|---|
| `resolve_paths.py` | Compute project dir + cc-connect file path | `python3 scripts/resolve_paths.py` |
| `check_env.py` | Check & install dependencies (cc-connect, VSCode Claude Code extension) | `python3 scripts/check_env.py [--install]` |
| `scan_sessions.py` | Register mode: scan + compare + classify changes | `python3 scripts/scan_sessions.py` |
| `register_apply.py` | Register mode: apply all changes atomically | `python3 scripts/register_apply.py [--resolve s2=name]` |
| `write_custom_title.py` | Write custom-title to JSONL | `python3 scripts/write_custom_title.py <name> <uuid>` |
| `read_title.py` | Read Claude Code session title | `python3 scripts/read_title.py <uuid>` |
| `write_cc_name.py` | Write name to cc-connect JSON | `python3 scripts/write_cc_name.py <uuid> <name>` |
| `read_cc_name.py` | Read name from cc-connect JSON | `python3 scripts/read_cc_name.py <uuid>` |
| `list_sessions.py` | List mode: comparison table | `python3 scripts/list_sessions.py` |

## Modes

### 1. `set <name>` — Set name in BOTH storage locations simultaneously

Steps:
1. Determine current session UUID from `$CLAUDE_CODE_SESSION_ID` env var
2. Run: `python3 scripts/write_custom_title.py <name> <uuid>` (Claude Code side)
3. Stop cc-connect daemon (see Daemon section below)
4. Run: `python3 scripts/write_cc_name.py <uuid> <name>` (cc-connect side)
5. Restart cc-connect daemon
6. Report success with both locations confirmed

### 2. `sync` — Read both sides, report mismatches, ask user, then fix

Steps:
1. Determine current session UUID
2. Run: `python3 scripts/read_title.py <uuid>` — get Claude Code title
3. Run: `python3 scripts/read_cc_name.py <uuid>` — get cc-connect name
4. Compare and report; if mismatch, ask user which name to use (AskUserQuestion)
5. Apply chosen name to both sides using `write_custom_title.py` and `write_cc_name.py`

### 3. `list` — Show all sessions with names from both systems side by side

Steps:
1. Run: `python3 scripts/list_sessions.py` — outputs comparison table
2. Present table to user

### 4. `bind` — Sync current session name from one side to the other

Steps:
1. Determine current session UUID
2. Run: `python3 scripts/read_title.py <uuid>` and `python3 scripts/read_cc_name.py <uuid>`
3. If one side has name and other is empty, copy using the appropriate write script
4. If both match, report "already bound"
5. If both differ, ask user (same as sync mode)

### 5. `register` — Register local VSCode sessions into cc-connect

**Optimized flow — avoid daemon restart unless necessary:**

1. Run: `python3 scripts/scan_sessions.py` — outputs summary of changes needed
2. **Early exit**: If summary shows no new sessions, no cleared names, and no mismatches → skip daemon stop/restart. History drifts are cosmetic only.
3. If action needed: resolve name mismatches with AskUserQuestion, then:
   - Stop cc-connect daemon
   - Run: `python3 scripts/register_apply.py [--resolve s2=name ...]` — applies all changes atomically
   - Restart cc-connect daemon
   - Warn user about 5-minute recovery delay

**Only register sessions WITH names.** Unnamed sessions are skipped.

**Never re-register**: Skip sessions whose `agent_session_id` already exists in cc-connect.

**History count**: cc-connect `/list` shows message count from `history` array length. Registered sessions get minimal entries (role + "." content) matching JSONL message count. These "." entries do NOT appear in model context — Claude Code only loads `type=human/assistant/user` messages.

## Daemon Overwrite Problem

**cc-connect daemon periodically writes its internal state to the session JSON file**, overwriting external modifications. Always **stop daemon before writing, restart after**.

```bash
# Stop daemon
kill $(pgrep -f 'cc-connect') 2>/dev/null; sleep 1; kill -9 $(pgrep -f 'cc-connect') 2>/dev/null; rm -f ~/.cc-connect/.config.toml.lock; sleep 1

# ... run scripts that write to cc-connect JSON ...

# Restart daemon
nohup cc-connect --force > /tmp/cc-connect.log 2>&1 & disown; sleep 3

# WARN USER: Feishu messages ignored for ~5 minutes after restart
```

## "Ignoring Old Message" Bug

After every cc-connect daemon restart, Feishu messages are silently dropped for approximately 2-5 minutes (up to ~10 min in edge cases). Caused by `IsOldMessage()` in `core/dedup.go` using `StartTime = time.Now()` (package-level var) as cutoff instead of actual WebSocket connection time.

**Workaround**: `register_apply.py` includes `past_id_tracking=False` in its atomic write. This reduces but does not fully prevent the bug.

**After restart, warn user**: messages will be silently dropped for ~5 minutes.

## Edge Cases

| Scenario | Action |
|----------|--------|
| cc-connect session has empty agent_session_id | Cannot sync — label as "cc-connect only" |
| Claude Code session not in cc-connect | Register via `register` mode |
| Both names empty | Suggest setting a name |
| Both names differ | Ask user which to keep — never silently overwrite |
| cc-connect daemon concurrently writes JSON | STOP daemon before writing, restart after |
| Daemon cleared a name after external write | Re-apply via stop→write→restart cycle |
| Existing custom-title entry in JSONL | New appended entry takes priority |
| Session JSONL title is literal string "None" | Skip — not a meaningful title |

## Important Rules

1. **STOP cc-connect daemon before writing its JSON file, restart after**
2. **Early exit: skip daemon restart if no substantive changes**
3. Always update BOTH `sessions[sN].name` AND `session_names[agent_session_id]` in one atomic operation
4. Only add to `session_names` when `agent_session_id` is non-empty
5. Use `os.replace()` for cc-connect JSON writes
6. **Include `past_id_tracking=False` in the same atomic write**
7. Read Claude Code titles: `custom-title` (highest) > `ai-title`
8. For `set` and `bind` modes, use `$CLAUDE_CODE_SESSION_ID`
9. For `list` mode, scan all sessions
10. Always report what was done to both storage locations
11. Never silently overwrite a name — always ask the user first
12. **After daemon restart, warn user about ~5 minute message silence**