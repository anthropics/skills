---
name: email-bridge
description: Communicate with Claude Code via email. Send task results, receive and execute instructions from email via SMTP/POP3. Supports 163.com, QQ Mail, Gmail. Ideal for long-running tasks and remote control.
---

# Email Bridge Skill

Communicate with Claude Code via email — send task results, receive and execute instructions from email.

## Setup

1. Copy `email-config.example.json` to `email-config.json` and fill in credentials
2. Copy all files into your Claude Code project
3. Set optional env vars (see Environment Variables)
4. Start the background poller: `nohup ./email-poll-loop.sh &>/dev/null &`

## Configuration (`email-config.json`)

```json
{
  "sender": "your_email@163.com",
  "receiver": "your_receiver@qq.com",
  "smtp_server": "smtp.163.com",
  "smtp_port": 465,
  "smtp_auth": "YOUR_SMTP_AUTH_CODE",
  "pop_server": "pop.163.com",
  "pop_port": 995
}
```

To get an SMTP/POP3 auth code for 163.com:
- Settings → POP3/SMTP/IMAP → Enable SMTP and POP3
- Copy the generated authorization code

## Commands

```bash
# Send an email
python3 email-bridge.py send "<subject>" "<body>"

# Check for new emails (manual)
python3 email-bridge.py check [limit]
```

## Smart Session Routing

The background poller intelligently decides whether to continue an existing
conversation or start a new one, based on email content:

| Trigger | Mode | Behavior |
|---------|------|----------|
| Subject starts with `Re:` | `--resume` | Continue existing session |
| Body contains `继续`/`接着`/`上次`/`刚才`/`之前` | `--resume` | Continue existing session |
| Body contains `!new`/`新对话`/`新任务` | `-p` | Force new session |
| Default (no keywords) | `-p` | New standalone session |

Session ID is persisted across emails. Continued emails share Claude context.

## Architecture

```
You ──email──> POP3 inbox
                  │
Bash poller (3min) │  free, zero LLM cost
                  │  email-decision.py classifies intent
                  ▼
           ┌──────────────┐
           │ continue? ──── claude --resume (same session, full context)
           │ new?      ──── claude -p      (fresh session)
           └──────────────┘
                  │
             SMTP reply
```

## File Structure

```
email-bridge/
├── email-bridge.py              # Send/check emails
├── email-poll-loop.sh           # Background poller with smart routing
├── email-decision.py            # Keyword classifier (continue vs new)
├── SKILL.md                     # This file
├── email-config.example.json    # Config template
├── .gitignore
├── LICENSE
└── README.md
```

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `EMAIL_PROJECT_DIR` | script directory | Project root where `claude` CLI runs |
| `EMAIL_QUEUE_FILE` | `/tmp/email-pending-queue.txt` | Email queue file path |

## Supported Providers

| Provider | SMTP Server | POP3 Server |
|----------|-------------|-------------|
| 163.com  | smtp.163.com:465 | pop.163.com:995 |
| QQ Mail  | smtp.qq.com:465 | pop.qq.com:995 |
| Gmail    | smtp.gmail.com:465 | pop.gmail.com:995 |

## Security

- `email-config.json` is gitignored — never commit auth codes
- `.email-seen.json` tracks processed email UIDs locally
- Auth codes stay in local config only

## License

MIT
