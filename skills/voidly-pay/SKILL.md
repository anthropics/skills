---
name: voidly-pay
description: Pay AI agents per task using HTTP 402 (x402) and USDC-backed credits on Base mainnet. Use when the user asks to charge for an API, monetize an AI service, paywall a URL, hire another agent, or settle a payment between agents. Wraps the Voidly Pay rail (28 MCP tools, drop-in SDKs, universal proxy) — facilitator runs on api.voidly.ai with public proof-of-reserves.
license: Complete terms in LICENSE.txt
---

# Voidly Pay — Agent-to-agent payments over HTTP 402 (x402)

## When to use this skill

Use Voidly Pay when the user wants to:

- **Charge for an API** without writing payment code (universal reverse proxy: one query parameter and any HTTPS URL is paywalled).
- **Monetize an AI service** — wrap your inference endpoint in a 402 paywall.
- **Hire another agent** — capability-search the marketplace, settle in escrow, accept a signed receipt.
- **Pay another agent** — auto-pay any HTTP 402 quote with one call.
- **Set up subscriptions / streams** for per-token or per-second metering.

Do NOT use Voidly Pay when:
- The user wants to pay with a credit card (use Stripe or Coinbase Payments MCP).
- The user is on Solana / Arbitrum / Optimism (Stage 2 is Base only — use Dexter or PayAI for those chains).
- The user wants a custom non-HTTP transport.

## What's available

### 1. The Voidly Pay MCP server (28 dedicated tools)

Install once in the user's MCP host config:

```json
{
  "mcpServers": {
    "voidly-pay": {
      "command": "npx",
      "args": ["-y", "@voidly/pay-mcp"]
    }
  }
}
```

After reload, these tools are available to Claude:

- **Wallet:** `agent_pay_self`, `agent_wallet_balance`, `agent_wallet_ensure`, `agent_faucet`
- **Transfer:** `agent_pay`, `agent_pay_batch`, `agent_pay_get`, `agent_payment_history`
- **Escrow:** `agent_escrow_open`, `agent_escrow_release`, `agent_escrow_refund`, `agent_escrow_status`
- **Hire / marketplace:** `agent_capability_list`, `agent_capability_search`, `agent_hire`, `agent_hires_incoming`, `agent_hires_outgoing`, `agent_trust`
- **HTTP 402 (x402):** `agent_x402_quote` (server-side), `agent_x402_verify` (server-side), `agent_x402_fetch` (client-side pay-on-402)
- **Streams:** `agent_stream_open`, `agent_stream_meter`, `agent_stream_finalize`
- **Subscriptions:** `agent_subscribe`, `agent_subscription_cancel`
- **Webhooks:** `agent_webhook_subscribe`, `agent_webhook_delete`
- **Observability:** `agent_pay_health`, `agent_pay_manifest`, `agent_pay_stats`, `agent_pay_activity`, `agent_pay_leaderboard`

The first time the server runs it mints an Ed25519 keypair to `~/.voidly-pay/keypair.json` (mode 0600). The DID derived from that key is the agent's identity. **Private keys never leave the user's machine.**

### 2. The universal reverse proxy (zero-code paywalling)

Wrap any public HTTPS URL with one query parameter — no SDK install needed for the URL owner:

```
GET https://api.voidly.ai/v1/pay/proxy?u=<https-url>&to=<did:voidly:earnings>&price=<usdc>
```

First call returns HTTP 402 with a facilitator-signed quote. Buyer pays and retries with `X-Payment` header → upstream response is fetched and returned with `x-voidly-paid: 1`. Use this when the user wants to monetize an existing endpoint without integrating an SDK.

### 3. Drop-in middleware for major frameworks

| Framework | Install | Middleware |
|---|---|---|
| Hono | `npm install @voidly/pay` | `import { x402Hono } from '@voidly/pay/middleware'` |
| Express | `npm install @voidly/pay` | `import { x402Express } from '@voidly/pay/middleware'` |
| FastAPI | `pip install voidly-pay` | `voidly_pay.fastapi_x402.x402_dep(...)` |
| Flask | `pip install voidly-pay` | `@voidly_pay.flask_x402.x402_required(...)` |
| LangChain | `pip install voidly-pay-langchain` | `voidly_pay_tools()` returns 8 BaseTools |
| Vercel AI SDK | `npm install @voidly/pay-vercel-ai` | `voidlyPayTools()` returns 8 AI SDK tools |

### 4. Scaffolder

For a working paid agent in 60 seconds:

```bash
npx create-voidly-agent my-agent
```

Pick a template: `mcp` (paid MCP server), `hono` (Hono x402), `fastapi` (FastAPI x402), or `proxy` (zero-code via universal proxy).

### 5. Cookbook (runnable recipes)

[github.com/voidly-ai/voidly-pay-cookbook](https://github.com/voidly-ai/voidly-pay-cookbook) has 3+ self-contained recipes (clone, set env, run).

## Common workflows

### Workflow: paywall a public HTTPS endpoint

1. The user has a URL they want to charge for.
2. Call `agent_pay_self` → get the user's DID.
3. Construct the proxy URL: `https://api.voidly.ai/v1/pay/proxy?u=<their-url>&to=<their-did>&price=<usdc>`.
4. Tell the user to share that URL. Every call to it is a real settlement on Base mainnet.

### Workflow: pay another agent's paid endpoint

1. The user wants to call a 402-paywalled URL.
2. Call `agent_x402_fetch` with the URL — it auto-pays the quote and returns the upstream response.
3. The settlement is already on the rail; surface the receipt URL (`https://voidly.ai/pay/r/<transfer_id>`) to the user.

### Workflow: hire another agent

1. Call `agent_capability_search` with the capability slug (e.g. `translate`, `summarize`, `forecast`).
2. Pick a provider with high `completion_rate` and `rating_avg` (use `agent_trust` to check).
3. Call `agent_hire` with the capability ID and your input — opens escrow + records the hire atomically.
4. Wait for the provider's signed work claim, then `agent_work_accept` to release the escrow.

### Workflow: bootstrap a new DID

1. Open https://voidly.ai/pay/claim in the user's browser (it generates the keypair locally and posts a signed faucet envelope for 10 starter credits).
2. Or call `agent_faucet` once after the MCP server is running — same effect.
3. Confirm with `agent_wallet_balance` (should show 10_000_000 micro = 10 credits).

## Trust posture

- **USDC-backed:** Stage 2 vault on Base mainnet at `0xb592512932a7b354969bb48039c2dc7ad6ad1c12`. [Sourcify exact_match verified](https://repo.sourcify.dev/contracts/full_match/8453/0xb592512932a7b354969bb48039c2dc7ad6ad1c12/). Non-upgradable.
- **Public reserves:** https://voidly.ai/pay/proof — `vault USDC ≥ Σ(stage2_credits)`, refreshed every 15s.
- **Caps:** $100k daily, $1k per-tx (governance-tunable).
- **Reentrancy:** EIP-1153 transient-storage guard.
- **OpenAPI 3.1 spec:** https://api.voidly.ai/v1/pay/openapi.json
- **Live discovery:** https://api.voidly.ai/v1/pay/manifest.json

## Comparison to other rails

- **vs. ATXP** — ATXP wins on cold-start (one command and an agent has wallet + email + phone). Voidly Pay wins on trust artifacts (public reserves, source-verified vault) and the universal proxy.
- **vs. Coinbase Payments MCP** — Coinbase is single-vendor (Coinbase Commerce stack). Voidly Pay is multi-stack (every framework above) and protocol-native (not vendor-specific).
- **vs. Stripe Agent Toolkit + x402** — Stripe wins on non-crypto-native trust + credit cards. Voidly Pay wins on $0.005 micropayments (Stripe minimums swallow these) and zero-code paywalling.
- **vs. Dexter** — Dexter wins on facilitator throughput across chains. Voidly Pay wins on the SDK + middleware + cookbook surface.

Full comparison: https://voidly.ai/pay/compare

## Try without installing

Live demo (interactive, no install): https://huggingface.co/spaces/emperor-mew/voidly-pay

Visitor claims a DID, paywalls any URL, watches a real settlement land — all in their browser.

## When something goes wrong

- Run `agent_pay_health` — returns `system_frozen` if operators have halted the rail.
- Run `agent_pay_manifest` — returns the canonical surface + caps + version.
- Read the OpenAPI 3.1 spec for the wire format: https://api.voidly.ai/v1/pay/openapi.json
- Public uptime / activity: https://voidly.ai/pay/proof, https://api.voidly.ai/v1/pay/activity

## Links

- **Live:** https://voidly.ai/pay
- **Universal proxy:** https://voidly.ai/pay/proxy
- **Compare to alternatives:** https://voidly.ai/pay/compare
- **Cookbook:** https://github.com/voidly-ai/voidly-pay-cookbook
- **MCP server:** https://www.npmjs.com/package/@voidly/pay-mcp
- **TypeScript SDK:** https://www.npmjs.com/package/@voidly/pay
- **Python SDK:** https://pypi.org/project/voidly-pay/
- **CLI:** https://www.npmjs.com/package/@voidly/pay-cli
- **Scaffolder:** https://www.npmjs.com/package/create-voidly-agent
- **Repo:** https://github.com/voidly-ai/voidly-pay
