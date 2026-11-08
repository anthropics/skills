# RCS Message Skill

An Agent Skill for sending and receiving SMS / RCS messages via the mobile SMS interface.

## Description

RCS Message, the upgraded 5G intelligent SMS, supports mass sending and forwarding of text & template messages directly via phone numbers. No app download is required. With carrier real-name security, it delivers images, videos and interactive cards, enabling one-stop inquiry, reservation, payment and business handling for efficient precise reach and closed-loop services.

## Installation

### Via Claude Code Plugin Market

```bash
/plugin marketplace add anthropics/skills
/plugin install rcs-message
```

### Via GitHub

```bash
claude plugin install github:casperkwok/rcs-message
```

### Manual

Copy this folder to your project's `.claude/skills/` or `~/.claude/skills/` directory.

## Usage

Use when the user asks to send a text message, check text messages, use SMS, text message, RCS, or needs to forward or mass send received text messages.

## Requirements

- Python 3.6+
- `requests` library
- Valid API credentials (APP_ID, APP_SECRET)

## Configuration

Set environment variables:

```bash
export FIVE_G_APP_ID="your-app-id"
export FIVE_G_APP_SECRET="your-app-secret"
```

Or create a `.env` file in the project root.

## License

MIT
