---
name: openai-voice-skill
description: Add real-time phone calling to AI agents using OpenAI Realtime API and Twilio Media Streams. Use when you want an AI agent to make or receive phone calls with sub-200ms latency, bidirectional audio streaming, and session continuity across voice, Telegram, and email channels. Requires Python 3.9+, a Twilio phone number, and an OpenAI API key with Realtime API access.
license: AGPL-3.0
compatibility: Requires Python 3.9+, Twilio account with a phone number, OpenAI API key with Realtime API access, and a publicly reachable webhook URL (ngrok, cloudflared, or deployed server). Compatible with Cursor, VS Code Copilot, Claude Code, OpenClaw, Gemini CLI, OpenHands, JetBrains Junie, Cody, Continue, Aider, Zed AI, and any agent platform that can run a Python process and make HTTP requests.
metadata:
  author: nia-agent-cyber
  version: "2.0"
  repo: https://github.com/nia-agent-cyber/openai-voice-skill
  tests: "727"
  coverage: "75%"
---

# openai-voice-skill

Open-source phone calling for AI agents. Bridges Twilio Media Streams to the OpenAI Realtime WebSocket API so your agent can make and receive phone calls with sub-200ms latency and natural barge-in support.

## Architecture

```
Inbound call:
  Phone → Twilio → POST /voice/incoming
       → TwiML <Connect><Stream url="wss://your-server/media-stream"/>
       → webhook-server.py (WebSocket bridge)
       → OpenAI Realtime API (wss://api.openai.com/v1/realtime)

Outbound call:
  POST /call → Twilio dials number → on answer → same TwiML flow
```

**Audio bridge** (inside `webhook-server.py`):
- Twilio sends: µ-law 8 kHz (base64)
- OpenAI expects: PCM16 24 kHz (base64)
- Conversion uses `audioop` (stdlib < 3.13) or `audioop-lts` (3.13+)

**No deprecated SIP endpoints.** This skill uses Twilio Media Streams (WebSocket) — not `sip.api.openai.com`, which OpenAI deprecated. All audio flows through `webhook-server.py`.

## Prerequisites

1. **Python 3.9+** with pip
2. **Twilio account** with a voice-capable phone number
3. **OpenAI API key** with `gpt-4o-realtime-preview` model access
4. **Public webhook URL** — ngrok, cloudflared, or a deployed server

## Setup

### 1. Clone and install

```bash
git clone https://github.com/nia-agent-cyber/openai-voice-skill.git
cd openai-voice-skill
python -m venv venv && source venv/bin/activate
pip install -r requirements.txt
```

### 2. Configure environment

```bash
cp .env.example .env
```

Edit `.env`:

```bash
OPENAI_API_KEY=sk-...
TWILIO_ACCOUNT_SID=AC...
TWILIO_AUTH_TOKEN=...
TWILIO_PHONE_NUMBER=+1XXXXXXXXXX   # E.164 format
PUBLIC_URL=https://your-tunnel.example.com
PORT=8080
ALLOW_INBOUND_CALLS=true           # set false to disable inbound
```

### 3. Expose your local server (development)

```bash
# Option A: cloudflared (recommended, no account needed)
cloudflared tunnel --url http://localhost:8080

# Option B: ngrok
ngrok http 8080
```

Set `PUBLIC_URL` in `.env` to the HTTPS URL from your tunnel.

### 4. Start the webhook server

```bash
source venv/bin/activate
python scripts/webhook-server.py
```

The server auto-registers its `/voice/incoming` URL as the Twilio webhook for your phone number on startup.

Verify it's healthy:

```bash
curl http://localhost:8080/health
```

### 5. Make your first call

**Inbound:** Call your Twilio number. The server answers and connects you to the OpenAI Realtime agent.

**Outbound via API:**

```bash
curl -X POST http://localhost:8080/call \
  -H "Content-Type: application/json" \
  -d '{"to": "+1234567890"}'
```

## Customising the Agent

The agent's identity, instructions, and voice are configured in `webhook-server.py` via the `OPENAI_VOICE` constant and the `build_call_prompt()` function. Edit those to change:

- **Voice:** `shimmer`, `alloy`, `echo`, `fable`, `onyx`, `nova`
- **Model:** `gpt-4o-realtime-preview` (default)
- **System prompt:** Anything returned by `build_call_prompt()`

## Session Continuity

After each call, `summarize_and_remember()` writes a transcript summary to `memory/YYYY-MM-DD.md` and emits a wake event to the OpenClaw gateway (if running). This means the same agent that handles phone calls also has full context from Telegram, email, and other channels.

Skip or remove this feature if you don't use OpenClaw — it degrades gracefully.

## Monitoring

```bash
# Active calls
curl http://localhost:8080/calls

# Server health
curl http://localhost:8080/health
```

Logs are written to stdout. For persistent logs, pipe through `tee` or configure `uvicorn` log file output.

## Production Deployment

For production, run behind a process supervisor:

```bash
# systemd (Linux)
ExecStart=/path/to/venv/bin/python scripts/webhook-server.py

# launchd (macOS) — see scripts/org.niavoice.voice-server.plist
launchctl load scripts/org.niavoice.voice-server.plist
```

Ensure `PUBLIC_URL` points to your stable public domain (Cloudflare tunnel, Fly.io, Railway, etc.).

## Troubleshooting

**Call connects but no audio / robotic voice:**
- Verify your tunnel is working: `curl https://your-tunnel.example.com/health`
- Check audio conversion: `audioop` or `audioop-lts` must be installed
- Sample rate mismatch causes robotic audio — do not bypass the µ-law ↔ PCM16 conversion

**Agent doesn't pick up inbound calls:**
- Set `ALLOW_INBOUND_CALLS=true` in `.env`
- Verify Twilio webhook points to `https://your-public-url/voice/incoming`
- The server logs the webhook URL it registers on startup

**Outbound call placed but agent doesn't speak:**
- OpenAI session setup takes ~300ms; speech before `session.updated` is silently dropped
- The server gates audio forwarding until `session.updated` is confirmed (3s timeout)

**Python 3.13+ import error on audioop:**
- Add `audioop-lts` to your virtualenv: `pip install audioop-lts`

## License

AGPL-3.0 — see LICENSE file. Self-hosting for personal or internal use is unrestricted. Distribution of modified versions requires source disclosure.
