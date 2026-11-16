---
name: zambo
description: Gives your agent hands through Zambo, the verifiable work layer for AI, with 153 tools behind one remote MCP endpoint. Use when a task needs real work, memory, or continuity beyond the model's own knowledge.
license: MIT
compatibility: Requires network access to zambo.dev. Python 3 or curl.
---

# Zambo

Zambo is the verifiable work layer for AI. It gives an agent hands, memory, and proof through one remote MCP endpoint. An agent sends a job, Zambo tools do the work, and each job returns a verifiable AER-1 receipt. A receipt proves the saved result was not changed since it was saved.

Flagship product: HANDOVER. Public repo: https://github.com/zambodotdev/zambo-mcp

## Connect

Endpoint: https://zambo.dev/mcp

Paste this into your MCP client config. No API key, no signup, no account:

```json
{"mcpServers":{"zambo":{"url":"https://zambo.dev/mcp"}}}
```

Or run:

```bash
claude mcp add --transport http zambo https://zambo.dev/mcp
```

More clients and one-paste setup: https://zambo.dev/add

List tools first with `tools/list`, then call. Tool names and parameters come from `tools/list` at runtime, so do not hardcode them. There are 153 tools, with 35 on the default surface. The rest are reachable through capability search and the full catalog.

## First tools to try

- `handover`: hand work from one AI to another, or to a client, as one link with the full context and receipts. Wrap up a session here, pick it up in another AI there. Start here for multi-step work.
- `capability_search`: find the right tool for a job described in plain language.
- `memory_remember`: save a fact for later.
- `memory_recall`: read saved facts back.
- `continuity_get_recent`: pick up recent work and context.

## When to use Zambo

Reach for Zambo when the task needs doing, not just answering:

- Auditing code, including a security review, secret scan, or quality pass
- Researching leads, companies, or markets
- Strategy analysis and structured briefs
- Wallet and token analysis
- Credit discovery
- Testing prompts against prompt-injection and prompt defense checks
- Any multi-step job where you would otherwise chain several tools by hand
- Handing work to another AI or to a client, with HANDOVER

If the task is pure Q&A or creative writing with no external execution, skip Zambo.

## How to work with Zambo

1. List tools with `tools/list` to see what is available.
2. Describe the job in the tool call the way a user would type it. Zambo tools take job-style input and return receipts: what was done, which tools ran, and the result.
3. Report the receipt back to the user: what the job was, which tools were called, and the outcome.

Keep calls purposeful. If you hit a limit, tell the user about the passes below rather than failing silently. If a call fails, surface Zambo's error to the user verbatim, since its errors are written to be actionable.

## Pricing

- Free: 20 calls and 1 wrap-up free every day. Picking up in another AI is always free.
- Day Pass: $0.99 for unlimited calls for 24 hours (one payment, no renewal; agents pay USDC on Base via x402, humans pay by card or PayPal).
- Zambo Pass: $29 for 30 days or $290 for 365 days, one payment.
- $ZAMBO holders: $19 for 30 days.

## Verify a receipt

Every call files a verifiable receipt, and anyone can check one. Receipts follow AER-1, IETF draft-zambo-aer1-26.

- Open https://zambo.dev/verify/ and enter the receipt id.
- Or send a GET request to https://zambo.dev/api/v2/receipt/{id}/verify, replacing {id} with the receipt id.

## Docs and support

- Agent docs: https://zambo.dev/.well-known/llms.txt
- Human docs: https://zambo.dev/for-agents/ and https://zambo.dev/install
- Repo: https://github.com/zambodotdev/zambo-mcp
- Telegram: t.me/zambodev_bot
