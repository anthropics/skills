# x402

Claude Code skill for BSV micropayments. Discover, authenticate, and pay AI services with Bitcoin SV — all from natural language.

## What It Does

Say what you want. The skill handles the rest:

```
/x402 generate an image of a mountain sunset
/x402 transcribe this audio file
/x402 search twitter for AI agent discussions
/x402 upload this file to NanoStore for a year
```

Under the hood:

1. **Discovers** available services from the [x402agency.com](https://x402agency.com) agent directory
2. **Authenticates** with [BRC-31](https://brc.dev/31) mutual auth (automatic handshake + session caching)
3. **Pays** with [BRC-29](https://brc.dev/29) micropayments (automatic 402 handling, transaction creation)
4. **Refunds** automatically if a paid request fails — the refund is internalized to your wallet with no manual steps

## Available Services

The skill discovers agents from [x402agency.com/.well-known/agents](https://x402agency.com/.well-known/agents):

| Agent | What it does | Cost |
|:------|:-------------|:-----|
| **Banana Agent** | AI image generation (Google Nano Banana Pro) | ~$0.19/image |
| **Veo Agent** | AI video generation with audio (Google Veo 3.1 Fast) | ~$0.75–$1.50/clip |
| **Whisper Agent** | Speech-to-text transcription (Whisper Large v3 Turbo) | ~$0.0006/min |
| **X Research Agent** | Twitter/X search, profiles, threads, trending | ~$0.005–$0.06/req |
| **NanoStore** | File hosting with UHRP content addressing (Babbage) | ~$0.0004/MB/yr |

Third-party services like NanoStore are listed in the directory with hosted manifests — clients connect directly, no proxy.

## Install

Requires [Claude Code](https://docs.anthropic.com/en/docs/claude-code) and [MetaNet Client](https://getmetanet.com).

```
/plugin marketplace add calgooon/x402
/plugin install x402@calgooon-x402
```

> **Troubleshooting:** If you get a "Failed to finalize marketplace cache" error, run `/plugin`, select **Manage marketplaces > Add marketplace**, and paste `https://github.com/Calgooon/x402`. Then run `/plugin install x402@calgooon-x402`.

### Prerequisites

- **MetaNet Client** running at `localhost:3321` (download from [getmetanet.com](https://getmetanet.com))
- **Python 3** with `requests` (`pip install requests`)

## Usage

The `/x402` command is the entry point. You can use it conversationally or with specific commands:

### Natural language
```
/x402 generate a photo of a cat in a top hat
/x402 upload report.pdf to NanoStore for 1 year
/x402 search twitter for "bitcoin scaling" from the last 24 hours
/x402 transcribe meeting.wav
```

### Specific commands
```
/x402 list                              # List all agents in the directory
/x402 discover banana                   # Show endpoints, pricing, schemas for an agent
/x402 discover nanostore                # Works for third-party services too
/x402 auth GET nanostore/list           # Authenticated request (no payment)
/x402 pay POST banana/generate {"prompt":"a sunset"}  # Paid request
```

### Command reference

| Command | What it does |
|:--------|:-------------|
| `/x402 list` | List all registered agents with capabilities and pricing |
| `/x402 discover <agent>` | Fetch the x402-info manifest — endpoints, schemas, pricing, error codes |
| `/x402 auth <METHOD> <agent/path>` | Make a BRC-31 authenticated request (no payment) |
| `/x402 pay <METHOD> <agent/path> [body]` | Make an authenticated + paid request (auto-handles 402 flow) |
| `/x402 identity` | Show your wallet's identity key |
| `/x402 session <url>` | Inspect a cached BRC-31 session |

Agent names (`banana`, `nanostore`, `whisper`, etc.) resolve automatically. Full URLs work too.

## Examples

### Generate an image
```
/x402 generate a photo of a cat wearing a top hat
→ discovers banana agent, pays ~9,000 sats, returns image URL
```

### Upload a file
```
/x402 upload report.pdf to NanoStore for 1 year
→ discovers NanoStore, pays ~730 sats for 1MB/year, returns presigned upload URL
```

### Search Twitter
```
/x402 find tweets about bitcoin scaling from the last 24 hours
→ discovers x-research agent, pays ~3,000 sats, returns sorted results
```

### Transcribe audio
```
/x402 transcribe meeting.wav
→ discovers whisper agent, pays based on audio length, returns text
```

## How It Works

```
/x402 <user request>
  → skill runs `list` to find matching agent by capabilities
  → skill runs `discover <agent>` to read the x402-info manifest
  → skill reads endpoint schemas, pricing, auth requirements
  → skill runs `pay POST <agent>/<endpoint> '{...}'`
    → BRC-31 handshake (automatic, cached 1 hour)
    → initial request → server returns 402 with price
    → wallet creates payment transaction
    → retry with x-bsv-payment header → server accepts, returns result
  → skill presents result to user
```

All payment is automatic — no confirmation prompts for typical micropayments (1–100,000 sats).

## Agent Directory

The skill resolves short names (like `banana` or `nanostore`) to full URLs via the [x402agency.com](https://x402agency.com) registry. Any BRC-31/BRC-29 service can be listed — including third-party services that don't serve their own discovery manifest.

The registry is cached locally for 5 minutes. Full URLs (`https://...`) bypass the registry entirely.

## Protocol

- **[BRC-31](https://brc.dev/31)**: Mutual HTTP authentication with identity keys and signed requests
- **[BRC-29](https://brc.dev/29)**: HTTP micropayments via 402 Payment Required flow
- **[BRC-100](https://brc.dev/100)**: MetaNet Client wallet interface (key derivation, signing, transaction creation)

## License

MIT
