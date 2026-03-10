---
name: claude-to-im
description: Use this skill to bridge Claude Code to IM platforms (Discord, Feishu/Lark, Telegram, QQ). Use when the user wants to start, stop, or manage a background daemon that forwards IM messages to a Claude Code session, so they can interact with Claude directly from their messaging app. Trigger on phrases like "start bridge", "stop bridge", "bridge status", "claude-to-im setup", "connect to Discord/Feishu/Telegram", or any request to manage the IM bridge daemon.
---

# Claude-to-IM Bridge Skill

Bridge Claude Code to IM platforms — interact with Claude directly from Discord, Feishu/Lark, Telegram, or QQ.

## Overview

This skill manages the **claude-to-im** bridge daemon, which forwards messages between IM platforms and your Claude Code session. Once running, you can send messages in your IM app and receive Claude's responses in real time — including streaming replies, file attachments, and interactive permission approvals.

**Repository:** https://github.com/d-wwei/Claude-Codex-Gemini-to-IM

## Supported Platforms

| Platform | Notes |
|---|---|
| Discord | Server/channel/user-level access control |
| Feishu / Lark | Voice message transcription, rich attachments |
| Telegram | Streaming preview, inline permission buttons |
| QQ | Basic messaging |

## Installation

### One-line install (recommended)

```bash
curl -fsSL https://raw.githubusercontent.com/d-wwei/Claude-Codex-Gemini-to-IM/main/scripts/install.sh | bash
```

The script will:
1. Verify Node.js >= 20 is installed
2. Clone the skill into `~/.claude/skills/claude-to-im`
3. Run `npm install`
4. Prompt you to run `/claude-to-im setup`

### Manual install

```bash
git clone https://github.com/d-wwei/Claude-Codex-Gemini-to-IM.git ~/code/Claude-Codex-Gemini-to-IM
cd ~/code/Claude-Codex-Gemini-to-IM
npm install
bash scripts/install-host.sh --host claude
```

**Prerequisites:** Node.js >= 20, Git, Claude Code CLI. Optional: `ffmpeg` for Feishu voice transcription.

## Subcommands

Once installed, use `/claude-to-im <subcommand>` inside Claude Code:

| Subcommand | Description |
|---|---|
| `setup` | Interactive configuration wizard — choose platforms, enter credentials, set working directory |
| `start` | Start the background bridge daemon |
| `stop` | Stop the daemon |
| `status` | Show daemon status and active connections |
| `logs [N]` | Show last N log lines (default: 50) |
| `doctor` | Diagnose configuration and connectivity issues |
| `reconfigure` | Update existing configuration |

## Command Parsing

Parse the user's intent from `$ARGUMENTS`:

| User says | Subcommand |
|---|---|
| `setup`, `configure`, `install` | setup |
| `start`, `start bridge` | start |
| `stop`, `stop bridge` | stop |
| `status`, `bridge status` | status |
| `logs`, `logs 200` | logs (extract optional N) |
| `doctor`, `diagnose` | doctor |
| `reconfigure` | reconfigure |

## Skill Location

Use Glob with pattern `**/skills/**/claude-to-im/SKILL.md` to locate the skill directory. Use that path as `SKILL_DIR` for all script references.

## Execution

### Config check

Before running `start`, `stop`, `status`, `logs`, `reconfigure`, or `doctor`, verify `~/.claude-to-im/config.env` exists. If not, redirect the user to run `setup` first.

### setup

Run an interactive wizard using `AskUserQuestion` (if available) or show `SKILL_DIR/config.env.example` with instructions if non-interactive.

Collect in order:
1. **Platforms** — which IM platforms to enable (discord, feishu, telegram, qq)
2. **Credentials** — one credential at a time per platform (see `SKILL_DIR/references/setup-guides.md` for platform-specific steps)
3. **General settings** — runtime (`claude` / `codex` / `gemini` / `auto`), working directory, model (optional), mode (`code` / `plan` / `ask`)
4. **Confirm and write** — show a masked summary, write `~/.claude-to-im/config.env` (chmod 600), validate tokens, report results

### start / stop / status / logs

```bash
bash "SKILL_DIR/scripts/daemon.sh" <subcommand> [args]
```

### doctor

```bash
bash "SKILL_DIR/scripts/doctor.sh"
```

Show results and suggest fixes. Common fixes:
- SDK missing → `cd SKILL_DIR && npm install`
- Stale build → `cd SKILL_DIR && npm run build`
- Config missing → run `setup`

### reconfigure

Read current `~/.claude-to-im/config.env`, show masked table, collect updates, rewrite atomically, re-validate changed tokens. Remind user to restart the daemon after changes.

## Notes

- Always mask secrets in output (show last 4 characters only)
- Never start the daemon without a valid `config.env`
- Config persists at `~/.claude-to-im/config.env` across sessions
- The daemon runs as a background Node.js process (launchd on macOS, setsid on Linux)
- Session commands (`/lsessions`, `/switchto`, `/rename`, `/archive`) are available in the IM chat once the bridge is running
