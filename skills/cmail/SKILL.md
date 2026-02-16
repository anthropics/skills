---
name: cmail
description: Sends and receives messages between Claude Code instances across machines on a Tailscale network. Provides file-based messaging with inbox monitoring, threading, and an optional auto-respond agent. Use when the user wants to send messages to other machines, check their inbox, or coordinate between Claude instances.
license: Apache-2.0. Complete terms in LICENSE.txt
compatibility: Requires Tailscale, jq, ssh, and a Unix-like system (Linux/macOS). Optional: Claude Code CLI for auto-respond agent.
allowed-tools: Bash(cmail *) Bash(~/.claude/skills/cmail/scripts/cmail.sh *) Bash(rm -f ~/.cmail/inbox/*.json *) Bash(rm -f ~/.cmail/.has_unread) Bash(rm -f ~/.cmail/.last_stop_check) Bash(ls ~/.cmail/inbox/*) Bash(tailscale ssh *) Bash(claude --print *)
---

# cmail — Claude Mail over Tailscale SSH

Sends and receives messages between Claude instances (and humans) across machines on a Tailscale network.

## When to Use This Skill

Use cmail when:
- The user asks to send a message to another machine or Claude instance
- The user wants to check their inbox or read messages
- Inter-agent coordination is needed across machines
- The user mentions "cmail", "check messages", "send to", or "reply to"

## Installation

```bash
./install.sh
```

The installer symlinks this skill into `~/.claude/skills/`, puts `cmail` on your PATH, configures Claude Code hooks/permissions, and starts the inbox watcher. Requires [Tailscale](https://tailscale.com/) for networking and `jq` for JSON handling.

## Quick Reference

| Command | Description |
|---------|-------------|
| `cmail send <host> "<message>"` | Send a message |
| `cmail send <host> --subject "<subj>" "<message>"` | Send with subject |
| `cmail inbox show` | List all messages (newest first) |
| `cmail inbox show --if-new` | List only if new messages exist |
| `cmail inbox clear` | Delete all messages (with confirmation) |
| `cmail read <id>` | Read a specific message |
| `cmail reply <id> "<message>"` | Reply preserving thread |
| `cmail hosts` | List hosts + test connectivity |
| `cmail setup` | Configure identity and hosts |
| `cmail watch` | Background watcher for new messages |
| `cmail agent on/off/status` | Manage auto-respond agent |
| `cmail deps` | Check and install dependencies |

## Usage Examples

**Check your cmail (zero-cost, do this periodically):**
```bash
cmail inbox show --if-new
# Output when messages exist:
#   ID        FROM              SUBJECT           DATE
#   a9c1c8    dev-server        Bug found         2026-02-15 14:32
#   f3e2d1    laptop            Deploy ready      2026-02-15 13:10
```

**Send cmail to another machine:**
```bash
cmail send dev-server "Found the bug — it's in auth.py line 42"
# Output: Message sent to dev-server (id: b7d4e2a1-...)
```

**Send with a subject:**
```bash
cmail send laptop --subject "Deploy status" "All tests passing, ready to deploy"
```

**Reply to a cmail:**
```bash
cmail reply a9c1c8 "Thanks, I'll take a look"
```

## Message Format

Messages are JSON files stored in `~/.cmail/inbox/` with fields: `id`, `from`, `to`, `timestamp`, `subject`, `body`, `in_reply_to`, `thread_id`.

## Hooks and Notifications

This skill installs Claude Code hooks that automatically notify you of new messages:
- **SessionStart**: Shows inbox summary when a session opens
- **UserPromptSubmit**: Injects unread count before each response
- **Stop**: Checks for new mail after each response; forces continuation if messages arrived

You do not need to poll manually -- the hooks handle notification automatically.

## Auto-Respond Agent

The optional auto-respond agent (`cmail agent on`) uses `claude --print` to automatically reply to incoming messages. It is disabled by default and must be explicitly enabled. See `cmail agent --help` for configuration.

## Behavior Guidelines

- When asked to "check cmail" or "check inbox", run `inbox show --if-new` first for efficiency.
- When sending cmail, keep messages concise and actionable.
- When replying, always use the `reply` command to preserve threading.
- If setup hasn't been run yet, run `setup` first.
- If a host is unreachable, suggest running `cmail hosts` to check connectivity.
