---
name: blockrun
description: Use when an AI agent needs to call external AI models (GPT, Claude, Gemini, etc.) with automatic micropayments via the x402 protocol. BlockRun enables pay-per-request access to AI APIs without API key management - just a crypto wallet.
---

# BlockRun: AI Agent Payments via x402

BlockRun is the discovery layer for AI agent payments. It provides OpenAI-compatible API endpoints that accept x402 micropayments in USDC on Base, enabling AI agents to pay for AI services autonomously.

## When to Use BlockRun

Use BlockRun when you need to:
- Call external AI models (GPT-4o, GPT-5, Claude, Gemini, DeepSeek, Grok, Llama) without API keys
- Enable autonomous AI agent payments via crypto wallets
- Access multiple AI providers through a single unified API
- Make true micropayments (as low as $0.001 per request)

## x402 Payment Flow

The x402 protocol (HTTP 402 "Payment Required") enables one-step payment + response:

1. **Request without payment** → Server returns `402 Payment Required` with price
2. **Request with x-payment header** → Server verifies payment, executes request, settles payment, returns response

## API Endpoint

```
POST https://blockrun.ai/api/v1/chat/completions
```

OpenAI-compatible format. Accepts the `x-payment` header for x402 payments.

## Available Models

| Category | Models |
|----------|--------|
| LLMs | gpt-4o, gpt-4o-mini, gpt-5, claude-3-5-sonnet, claude-3-5-haiku, gemini-2.0-flash, deepseek-chat, llama-3.3-70b |
| Reasoning | o1, o3, grok-2 |
| Image | dall-e-3, stable-diffusion-3, flux |

## Request Format

```json
{
  "model": "gpt-4o-mini",
  "messages": [
    {"role": "system", "content": "You are a helpful assistant."},
    {"role": "user", "content": "Hello!"}
  ],
  "max_tokens": 1024
}
```

## Response Format

Standard OpenAI chat completions response:

```json
{
  "id": "chatcmpl-...",
  "object": "chat.completion",
  "model": "gpt-4o-mini",
  "choices": [{
    "index": 0,
    "message": {
      "role": "assistant",
      "content": "Hello! How can I help you today?"
    },
    "finish_reason": "stop"
  }],
  "usage": {
    "prompt_tokens": 20,
    "completion_tokens": 10,
    "total_tokens": 30
  }
}
```

## Payment Header

The `x-payment` header contains a base64-encoded JSON payload with:
- EIP-712 typed signature authorizing USDC transfer
- Payment amount in micro-USDC (6 decimals)
- Recipient address
- Expiration time

## SDK Usage

### Python

```bash
pip install blockrun-llm
```

```python
from blockrun_llm import LLMClient

client = LLMClient(private_key="0x...")
response = client.chat("Hello!")
# Payment handled automatically via x402
```

### TypeScript

```bash
npm install blockrun-llm
```

```typescript
import { LLMClient } from 'blockrun-llm';

const client = new LLMClient({ privateKey: '0x...' });
const response = await client.chat('Hello!');
// Payment handled automatically via x402
```

## Wallet Setup

BlockRun requires an Ethereum wallet with USDC on Base:

1. **Generate or import a wallet** with a private key
2. **Fund with USDC on Base** (Coinbase, bridge from other chains)
3. **Use the private key** with BlockRun SDK or build x402 signatures directly

## Pricing

Prices are calculated per request based on:
- Input tokens (prompt)
- Output tokens (completion)
- Model-specific rates
- 10% margin

Average transaction: ~$0.005-0.10 depending on model and token count.

## Error Handling

| Status | Meaning |
|--------|---------|
| 402 | Payment Required - no or invalid payment header |
| 400 | Invalid request (unknown model, bad format) |
| 500 | Provider error (upstream AI service failed) |

## Integration Patterns

### For AI Agent Frameworks

BlockRun integrates with agent frameworks:
- **ElizaOS**: `elizaos-plugin-blockrun`
- **Claude Code**: `blockrun-mcp` MCP server
- **LangChain**: Custom LLM provider (planned)

### For Direct API Calls

When building custom agents, use the Python or TypeScript SDK to handle x402 payment signing automatically.

## Resources

- **Website**: https://blockrun.ai
- **Docs**: https://blockrun.ai/docs
- **GitHub**: https://github.com/blockrunai
- **Python SDK**: https://github.com/blockrunai/blockrun-llm
- **TypeScript SDK**: https://github.com/blockrunai/blockrun-llm-ts
