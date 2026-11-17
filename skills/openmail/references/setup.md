# OpenMail Setup

## Prerequisites

- Node.js 20+
- An OpenMail account (free at [console.openmail.sh](https://console.openmail.sh))

## Step 1: Get an API key

1. Go to [console.openmail.sh](https://console.openmail.sh) and sign up (no credit card required)
2. Navigate to **Settings > API Keys**
3. Copy your key — it starts with `om_`

## Step 2: Install the CLI

```bash
npm install -g @openmail/cli
```

Verify installation:

```bash
openmail --version
```

## Step 3: Run setup

```bash
openmail setup --api-key "om_..." --mailbox-name "agent" --display-name "My Agent"
```

What setup does:
- Creates an inbox at `agent@<your-domain>.openmail.sh`
- Writes `~/.openclaw/openmail.env` with `OPENMAIL_API_KEY`, `OPENMAIL_INBOX_ID`, and `OPENMAIL_ADDRESS`
- Writes the skill file to `~/.openclaw/skills/openmail/SKILL.md`
- Optionally starts the WebSocket bridge for real-time inbound delivery

## Step 4: Verify

```bash
openmail status
```

Expected output shows your inbox address, API connection status, and bridge status.

## Environment variables

| Variable | Description |
|---|---|
| `OPENMAIL_API_KEY` | Your API key (`om_live_...` or `om_test_...`) |
| `OPENMAIL_INBOX_ID` | ID of the default inbox (`inb_...`) |
| `OPENMAIL_ADDRESS` | Email address of the default inbox |
| `OPENMAIL_API_URL` | Optional. Override API base URL (default: `https://api.openmail.sh`) |

The CLI sources `~/.openclaw/openmail.env` automatically. You can also set these as shell environment variables.

## Multiple inboxes

To create additional inboxes after setup:

```bash
openmail inbox create --mailbox-name "support" --display-name "Support"
```

To list all inboxes and their IDs:

```bash
openmail inbox list
```

Pass `--inbox-id <id>` to any command to target a specific inbox other than the default.

## Reconfigure

To change your usage mode or update credentials without recreating the inbox:

```bash
openmail setup --reconfigure
```

## Remove

To remove all OpenMail configuration:

```bash
openmail setup --reset
```

To also delete the inbox on the server: `openmail inbox delete --id <inbox-id>`
