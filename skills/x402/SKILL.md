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

## Agent Registry

A directory of available agents lives at `402agints.com`. Run `list` to see all registered agents — their names, capabilities, and URLs. Agent names resolve automatically anywhere a URL is expected.

**Always start with `list`** when the user's request could match any registered agent. Use the agent descriptions, capabilities, and taglines to match the user's natural language intent to the right agent. Don't assume which agent to use — check the registry.

The registry is cached locally for 5 minutes at `~/.local/share/brc31-sessions/registry.json`. Full URLs (`https://...`) still work directly and bypass the registry.

## Commands

All operations use the helper script bundled with this skill. All commands output JSON to stdout.

| Command | Purpose |
|---------|---------|
| `python3 ./scripts/brc31_helpers.py list` | List all agents from the 402agints.com registry |
| `python3 ./scripts/brc31_helpers.py discover <name_or_url>` | Learn server endpoints, auth requirements, costs |
| `python3 ./scripts/brc31_helpers.py auth <METHOD> <name_or_url> [body]` | Authenticated request (no payment) |
| `python3 ./scripts/brc31_helpers.py pay <METHOD> <name_or_url> [body]` | Authenticated + paid request (auto-handles 402) |
| `python3 ./scripts/brc31_helpers.py identity` | Get wallet's 66-char hex identity key |
| `python3 ./scripts/brc31_helpers.py session <base_url>` | Inspect cached session |

Handshake is automatic — never call it manually before `auth` or `pay`.

## Decision Tree

1. **List** — Run `list` to see all registered agents. Match the user's intent to an agent by reading the name, tagline, and capabilities from the registry. There may be many agents — pick the best match.

2. **Discover** — Run `discover <agent_name>` on the matched agent to get its full manifest: endpoints, pricing, input schemas. Present a summary to yourself (or the user if they're exploring).

3. **Route** — Match user intent to an endpoint:
   - `auth: true`, no payment → use **`auth`**
   - `payment` with satoshis → use **`pay`** (do NOT ask user to confirm — consent is implicit by invoking this skill; typical costs are 1-100 sats)
   - `auth: false` → plain curl, no skill needed

4. **Call** — Run the appropriate command. For requests with a JSON body, pass it as the 4th argument:
   ```bash
   python3 ./scripts/brc31_helpers.py pay POST <agent_name>/<endpoint> '{"key":"value"}'
   ```

5. **Present** — Parse the JSON response (`{status, headers, body}`). The `body` is a string that may contain nested JSON — parse it before presenting.

## Examples

### Typical flow: user asks for something an agent can do
User asks: "generate an image of a sunset"

```bash
# Step 1: Check what agents are available
python3 ./scripts/brc31_helpers.py list
# → Returns JSON array. Read taglines/capabilities. Pick the image generation agent.

# Step 2: Discover its endpoints and pricing
python3 ./scripts/brc31_helpers.py discover <matched_agent_name>
# → Returns manifest with endpoints, pricing tiers, input schemas

# Step 3: Call the paid endpoint
python3 ./scripts/brc31_helpers.py pay POST <agent_name>/<endpoint> '{"prompt":"a sunset"}'
# → Handles auth + 402 + payment automatically. Returns result.
```

### Discovery by URL (for unregistered servers)
```bash
python3 ./scripts/brc31_helpers.py discover "https://some-server.example.com"
```
Returns a manifest with `name`, `serverIdentityKey`, `endpoints[]`.

### Authenticated request (free endpoint)
```bash
python3 ./scripts/brc31_helpers.py auth POST <agent_name>/<endpoint>
```

### Direct URL (bypasses registry)
```bash
python3 ./scripts/brc31_helpers.py pay POST "https://some-server.example.com/paid"
```

## Refunds

Servers that support BRC-29 refunds will automatically return refund data when a paid request fails after payment. The client **auto-detects and internalizes refunds** — no manual action needed.

- **Inline refunds**: Returned in the same response as the error (e.g., `/paid` fails immediately)
- **Deferred refunds**: Returned later when polling `/status/{id}` for async operations that failed

The `discover` command shows which endpoints support refunds. The `pay` command output includes a `refund` block when a refund was received and internalized.

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
