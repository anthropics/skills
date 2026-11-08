---
name: buildr
description: Bridge Claude Code to Telegram - mirror your CC session to a Telegram bot. Send messages, approve permissions, stop tasks, and control coding sessions from your phone. One command setup with just a bot token and Telegram user ID.
license: MIT
---

# Buildr - Telegram Bridge for Claude Code

Bridge your Claude Code session to a Telegram bot. Same conversation, two windows. Control your coding sessions from your phone.

## Setup

Run the setup script with your Telegram bot token and user ID:

```bash
cd scripts
./setup.sh <BOT_TOKEN> <USER_ID>
```

Get these from:
- Bot token: [@BotFather](https://t.me/BotFather) on Telegram
- User ID: [@userinfobot](https://t.me/userinfobot) on Telegram

Setup handles everything automatically - creates `~/.buildr/`, starts PM2 relay daemon, configures Claude Code hooks.

## What It Does

- **Message mirroring**: Every CC response goes to Telegram, every TG message reaches CC
- **Permission forwarding**: Tool approval requests come to your phone - reply YES/NO
- **STOP command**: Send `STOP` to halt CC instantly from Telegram
- **Await system**: When CC is idle, it waits for your TG message (no timeout)
- **Offline fallback**: If CC dies (laptop closed), messages processed via `claude -p`
- **Persistence**: Optional tmux setup keeps CC alive when laptop closes

## Protocol

When this skill is active, follow these rules for every response:

### 1. Mirror to Telegram
Write every response to the outbox:
```
python3 -c "import json, os; home=os.environ.get('BUILDR_HOME',os.path.expanduser('~/.buildr')); open(os.path.join(home,'outbox.jsonl'),'a').write(json.dumps({'text':'YOUR MESSAGE HERE'}) + '\n')"
```

### 2. On Compaction
Send "COMPACTED" to Telegram so the user knows the session continued.

### 3. When Idle/Waiting
Create the await flag, then make any tool call:
```
touch ~/.buildr/await-flag
```
The hook notifies the user on Telegram and polls until they respond. No timeout.

## Rules
- Do NOT use curl or the Telegram API directly - use the outbox file only
- If user sends STOP on Telegram - halt immediately
- All Telegram messages arrive via the PreToolUse hook (blocks once to show you)
- Permission requests are forwarded to Telegram automatically
- The user can reply YES, NO, or send a custom message to any prompt

## Architecture

```
Claude Code <-- inbox.jsonl -- Relay Daemon (PM2) <-- poll -- Telegram Bot
            --> outbox.jsonl ->                    --> send ->
            --> heartbeat
```

**Components** (in `scripts/`):
- `relay.js` - Always-on PM2 daemon. Polls TG, sends outbox, monitors heartbeat
- `bridge-hook.py` - PreToolUse hook. Auto-heartbeat, STOP, await, message injection
- `perm-hook.sh` - PermissionRequest hook. Forwards tool approvals to TG
- `setup.sh` - One-command installer
- `teardown.sh` - Clean uninstaller

## Telegram Commands

- `/status` - Check CC session status
- `/help` - Show available commands
- `/clear` - Clear message inbox
- `STOP` - Halt CC immediately

## Uninstall

```bash
cd scripts
./teardown.sh
```

## Requirements

- Node.js 18+
- Python 3
- PM2 (`npm install -g pm2`)
- Claude Code CLI
