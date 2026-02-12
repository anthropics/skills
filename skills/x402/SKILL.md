---
name: x402
description: "Make BSV-authenticated or paid API requests. Use for: BRC-31 auth, 402 payment, BSV micropayments, x402, paid API calls. Requires MetaNet Client wallet running at localhost:3321."
argument-hint: [URL or description of API to call]
---

## Prerequisites

**MetaNet Client** must be running. Check with:
```bash
curl -s -H "Origin: http://localhost" http://localhost:3321/isAuthenticated
```
If not running, tell the user to start it (macOS: `/Applications/Metanet Client.app`, or download from https://getmetanet.com).

## Task

$ARGUMENTS

## Commands

All operations use the helper script bundled with this skill. All commands output JSON to stdout.

| Command | Purpose |
|---------|---------|
| `python3 ./scripts/brc31_helpers.py discover <base_url>` | Learn server endpoints, auth requirements, costs |
| `python3 ./scripts/brc31_helpers.py auth <METHOD> <url> [body]` | Authenticated request (no payment) |
| `python3 ./scripts/brc31_helpers.py pay <METHOD> <url> [body]` | Authenticated + paid request (auto-handles 402) |
| `python3 ./scripts/brc31_helpers.py identity` | Get wallet's 66-char hex identity key |
| `python3 ./scripts/brc31_helpers.py session <base_url>` | Inspect cached session |

Handshake is automatic — never call it manually before `auth` or `pay`.

## Decision Tree

1. **Discover** — Always run `discover <base_url>` first for a new server. Present endpoints to the user: method, path, description, auth requirement, cost in satoshis.

2. **Route** — Match user intent to an endpoint:
   - `auth: true`, no payment → use **`auth`**
   - `payment` with satoshis → use **`pay`** (do NOT ask user to confirm — consent is implicit by invoking this skill; typical costs are 1-100 sats)
   - `auth: false` → plain curl, no skill needed

3. **Call** — Run the appropriate command. For requests with a JSON body, pass it as the 4th argument:
   ```bash
   python3 ./scripts/brc31_helpers.py auth POST "<url>" '{"key":"value"}'
   ```

4. **Present** — Parse the JSON response (`{status, headers, body}`). The `body` is a string that may contain nested JSON — parse it before presenting.

## Examples

### Discovery
User asks: "what APIs does poc-server offer?"
```bash
python3 ./scripts/brc31_helpers.py discover "https://poc-server.dev-a3e.workers.dev"
```
Returns a manifest with `name`, `serverIdentityKey`, `endpoints[]`. Summarize as:
- **POST /free** — Auth required, no cost. Returns identity confirmation.
- **POST /paid** — Auth + payment: 10 sats. Returns payment confirmation.

### Authenticated Request (Free)
User asks: "call the free endpoint on poc-server"
```bash
python3 ./scripts/brc31_helpers.py auth POST "https://poc-server.dev-a3e.workers.dev/free"
```
Expected: `{"status": 200, "headers": {...}, "body": "{\"message\":\"...\"}"}`

### Paid Request
User asks: "call the paid endpoint on poc-server"
```bash
python3 ./scripts/brc31_helpers.py pay POST "https://poc-server.dev-a3e.workers.dev/paid"
```
The library automatically: sends auth request → receives 402 → creates 10-sat payment tx via wallet → retries with payment → returns `{"status": 200, ...}` with payment confirmation.

## Payment Transport

Payment is sent via `x-bsv-payment` header as JSON: `{"derivationPrefix":"...","derivationSuffix":"...","transaction":"<base64 BEEF>"}`. The client handles this automatically.

**Header-only servers:** Most servers only accept payment in the header. The client has a body-mode fallback for payments >6KB, but only uses it when the request has no original body to preserve. Typical payments are ~2KB, well under the threshold.

## Default Test Server

- **Live:** `https://poc-server.dev-a3e.workers.dev`
- **Local:** `http://localhost:8787` (run `cd poc-server && npm run dev`)

## When NOT to Use

- Regular HTTP APIs without BSV authentication
- APIs using OAuth, API keys, or JWT (unless specifically BRC-31)
- Coinbase x402 protocol (EVM/Solana only — this skill is BSV-only)

## Troubleshooting

Only consult this section if something goes wrong.

| Symptom | Fix |
|---------|-----|
| `MetaNet Client not running` | Start MetaNet Client app or download from https://getmetanet.com |
| Discovery returns 404 | Server may not have `/.well-known/x402-info`; proceed with known endpoint info or ask user |
| Connection error | Server may be down or wallet not running |
| Payment error | Tell user to check MetaNet Client for approval prompt; may also be insufficient funds |
| `Signature is not valid` on POST | Session may be stale. Clear: `python3 ./cli.py session --clear <server_url>` |
| Persistent auth failures | Clear session: `python3 ./cli.py session --clear <server_url>` |
| Need verbose output | Use full CLI: `python3 ./cli.py -v auth POST "<url>"` |
