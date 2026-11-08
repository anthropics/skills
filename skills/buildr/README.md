# Buildr

**Bridge Claude Code to Telegram** - control your coding sessions from your phone.

Buildr mirrors your Claude Code session to a Telegram bot. Same conversation, two windows. No extra API tokens wasted - it's pure file-based IPC.

## What You Get

- **Full mirror**: Every CC response appears in Telegram, every TG message reaches CC
- **Permission forwarding**: Tool approval requests come to TG - reply YES/NO from your phone
- **STOP command**: Send `STOP` in Telegram to halt CC immediately
- **Await system**: When CC is idle, it waits for your TG message (no timeout, no session death)
- **Offline fallback**: If CC dies (laptop closed), messages are processed via `claude -p`
- **Persistence**: Optional tmux setup keeps CC alive when you close your laptop
- **Typing indicator**: Shows "typing..." animation before every message

## Requirements

- Node.js 18+
- Python 3
- Claude Code CLI (`claude`)
- PM2 (`npm install -g pm2`)
- A Telegram bot token (from [@BotFather](https://t.me/BotFather))
- Your Telegram user ID (from [@userinfobot](https://t.me/userinfobot))

## Install

```bash
git clone <repo-url>
cd buildr
./setup.sh <BOT_TOKEN> <USER_ID>
```

Or run interactively (prompts for token and ID):
```bash
./setup.sh
```

That's it. The setup:
1. Creates `~/.buildr/` with all files
2. Starts the relay daemon via PM2
3. Configures Claude Code hooks automatically
4. Sends a test message to your Telegram

## Laptop Persistence

To keep CC alive when you close your laptop:

```bash
~/.buildr/start-cc.sh
```

This starts Claude Code inside a tmux session that survives SSH disconnects. Attach/detach with:
```bash
tmux attach -t buildr-cc   # attach
# Ctrl+B then D             # detach
```

## Telegram Commands

| Command | Description |
|---------|-------------|
| `/status` | Check CC session status |
| `/help` | Show available commands |
| `/clear` | Clear message inbox |
| `/reconnect` | Info about reconnecting |
| `STOP` | Halt CC immediately |

When CC is waiting, reply:
- **YES** - continue
- **Any message** - CC receives it as instructions

## How It Works

```
┌─────────────┐     files      ┌─────────────┐     HTTPS     ┌──────────┐
│ Claude Code │ ←── inbox ───  │   Relay     │ ←── poll ───  │ Telegram │
│   (hooks)   │ ─── outbox ──→ │  (PM2 daemon)│ ─── send ──→ │   Bot    │
│             │ ─── heartbeat  │             │               │          │
└─────────────┘                └─────────────┘               └──────────┘
```

**Files** (all in `~/.buildr/`):
- `inbox.jsonl` - TG messages (relay writes, CC reads via hook)
- `outbox.jsonl` - CC responses (CC writes, relay sends to TG)
- `heartbeat` - CC liveness timestamp (hook writes on every tool call)
- `stop-flag` - STOP signal (relay creates, hook checks)
- `await-flag` - CC waiting for user (CC creates, hook polls)
- `config.env` - Bot token + user ID

**Components**:
- `relay.js` - Always-on PM2 daemon. Polls TG, sends outbox, monitors heartbeat
- `bridge-hook.py` - PreToolUse hook. Auto-heartbeat, STOP, await, message injection
- `perm-hook.sh` - PermissionRequest hook. Forwards approvals to TG

## Uninstall

```bash
./teardown.sh
```

Stops PM2 process, removes hooks from Claude Code, optionally deletes `~/.buildr/`.

## Security

- Only the configured user ID can interact with the bot
- All other Telegram users are silently ignored
- Bot token and user ID stored in `~/.buildr/config.env`

## Troubleshooting

**Messages not appearing in Telegram?**
```bash
pm2 logs buildr-relay    # check relay logs
pm2 restart buildr-relay # restart if needed
```

**CC not reading TG messages?**
- Ensure Claude Code hooks are configured: check `~/.claude/settings.json`
- The PreToolUse hook runs before every tool call - CC must be actively working

**Session dying when laptop closes?**
- Use `~/.buildr/start-cc.sh` to run CC in tmux
- Or: relay automatically uses `claude -p` as offline fallback
