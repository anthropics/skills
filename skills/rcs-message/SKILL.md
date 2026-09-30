---
description: RCS Message, the upgraded 5G intelligent SMS, supports mass sending and forwarding of text & template messages directly via phone numbers. No app download is required. With carrier real-name security, it delivers images, videos and interactive cards, enabling one-stop inquiry, reservation, payment and business handling for efficient precise reach and closed-loop services.
name: rcs-message
---

# RCS Message Skill

Send and receive SMS / RCS via the mobile SMS interface.Use when the user asks to send a text message, check text messages, use SMS, text message, RCS, or needs to forward or mass send received text messages.

## Overview

This skill provides message sending capabilities through channel-based delivery with template support, fallback handling, and natural language command parsing.

## Requirements

- Python 3.6 or higher
- requests library
- python-dotenv library (optional)
- Valid API credentials (APP_ID, APP_SECRET)

## Configuration

### API Endpoint

| Item | Value |
|------|-------|
| API Server | `https://5g.fontdo.com` (pre-configured) |
| Endpoint | `/messenger/api/v1/group/send` |
| Method | POST |

### Environment Variables

Set environment variables:

```bash
export FIVE_G_APP_ID="your-app-id"
export FIVE_G_APP_SECRET="your-app-secret"
```

Or create a `.env` file in the project root:

```bash
FIVE_G_APP_ID=your-app-id
FIVE_G_APP_SECRET=your-app-secret
```

## Quick Reference

| Action | Command |
|--------|---------|
| Send text message | `python3 scripts/send.py -n "+8613700000001" -m "Hello"` |
| Send template | `python3 scripts/send.py --type RCS --template-id "ID" -n "+8613700000001"` |
| Validate only | `python3 scripts/send.py -n "+8613700000001" --dry-run` |

## Usage

### Natural Language Commands

Use simple commands in Moltbot:

```
Send a message to 13700000001 with hello world
```

```
Send a template message using RCS template 269000000000000000 to 13700000001
```

### Command Line

Basic message sending:

```bash
python3 scripts/send.py -n "+8613700000001" -m "Hello"
```

Template message:

```bash
python3 scripts/send.py --type RCS --template-id "TEMPLATE_ID" -n "+8613700000001" --params "name:John,code:12345"
```

With fallback channels:

```bash
python3 scripts/send.py --type RCS --template-id "TEMPLATE_ID" -n "+8613700000001" --fallback-aim "FALLBACK_ID" --fallback-sms "SMS Content"
```

## Parameters

| Parameter | Description |
|-----------|-------------|
| -n, --numbers | Recipient number(s), comma separated |
| -m, --message | Message content for TEXT type |
| -t, --type | Message type: TEXT, RCS, AIM, MMS, SMS |
| --template-id | Template ID for non-TEXT types |
| --params | Template parameters as key:value pairs |
| --fallback-aim | Fallback template ID for AIM channel |
| --fallback-sms | Fallback content for SMS channel |
| --dry-run | Validate parameters without sending |

## Message Types

| Type | Description |
|------|-------------|
| TEXT | Direct text content delivery |
| RCS | Rich Communication Services messaging |
| AIM | Advanced Interactive Messaging |
| MMS | Multimedia Messaging Service |
| SMS | Short Message Service fallback |

## Validation Rules

| Rule | Limit |
|------|-------|
| Maximum recipients | 100 per request |
| Maximum message length | 1000 characters |
| Minimum interval | 60 seconds between requests |
| Number format | International format supported |

## Troubleshooting

| Problem | Solution |
|---------|----------|
| Authentication Error (403) | Verify APP_ID and APP_SECRET are correct. Confirm application is active. |
| Rate Limit Error | Wait 60 seconds before retry. Adjust MIN_INTERVAL_SECONDS in config. |
| Format Error | Use international format (+8613700000001) or domestic format (13700000001). |

Enable debug mode for detailed output:

```bash
python3 scripts/send.py -n "+8613700000001" -m "Test" --debug
```

## Project Structure

```
rcs-message/
├── SKILL.md               # Skill definition
├── scripts/
│   ├── send.py            # Core sending module
│   ├── main.py            # Entry point
│   ├── handle_user_input.py # Command parser
│   ├── check_config.py    # Config validator
│   ├── config.example.json # Config template
│   ├── privacy_protect.py # Privacy protection
│   └── session_creds.py   # Session credentials
└── references/
    └── USAGE_EXAMPLES.md  # Additional examples
```

## Limitations

- API credentials required for authentication
- Rate limiting applies to prevent abuse
- Session management handled per deployment

## Security

- Credentials stored in environment variables
- No hardcoded sensitive values
- Input validation on all parameters

## Version

1.0.0
