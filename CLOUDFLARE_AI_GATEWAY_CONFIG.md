# Cloudflare AI Gateway Configuration

[Cloudflare AI Gateway](https://developers.cloudflare.com/ai-gateway/) sits in front of provider APIs and adds analytics, caching, and controls. For Anthropic, OpenClaw uses the Anthropic Messages API through your Gateway endpoint.

| Property      | Value                                                                                    |
| ------------- | ---------------------------------------------------------------------------------------- |
| Provider      | `cloudflare-ai-gateway`                                                                  |
| Plugin        | official external package (`@openclaw/cloudflare-ai-gateway-provider`)                   |
| Base URL      | `https://gateway.ai.cloudflare.com/v1/<account_id>/<gateway_id>/anthropic`               |
| Default model | `cloudflare-ai-gateway/claude-sonnet-4-6`                                                |
| API key       | `CLOUDFLARE_AI_GATEWAY_API_KEY` (your provider API key for requests through the Gateway) |

**Note:** For Anthropic models routed through Cloudflare AI Gateway, use your **Anthropic API key** as the provider key.

When thinking is enabled for Anthropic Messages models, OpenClaw strips trailing assistant prefill turns before sending the payload through Cloudflare AI Gateway. Anthropic rejects response prefilling with extended thinking, while ordinary non-thinking prefill remains available.

## Install plugin

Install the official plugin, then restart Gateway:

```bash
openclaw plugins install @openclaw/cloudflare-ai-gateway-provider
openclaw gateway restart
```

## Getting started

### Step 1: Set the provider API key and Gateway details

Run onboarding and choose the Cloudflare AI Gateway auth option:

```bash
openclaw onboard --auth-choice cloudflare-ai-gateway-api-key
```

This prompts for your account ID, gateway ID, and API key.

### Step 2: Set a default model

Add the model to your OpenClaw config:

```json5
{
  agents: {
    defaults: {
      model: { primary: "cloudflare-ai-gateway/claude-sonnet-4-6" },
    },
  },
}
```

### Step 3: Verify the model is available

```bash
openclaw models list --provider cloudflare-ai-gateway
```

## Non-interactive setup

For scripted or CI setups, pass all values on the command line:

```bash
openclaw onboard --non-interactive \
  --mode local \
  --auth-choice cloudflare-ai-gateway-api-key \
  --cloudflare-ai-gateway-account-id "your-account-id" \
  --cloudflare-ai-gateway-gateway-id "your-gateway-id" \
  --cloudflare-ai-gateway-api-key "$CLOUDFLARE_AI_GATEWAY_API_KEY"
```

## Configuration examples

### Basic configuration

```json5
{
  agents: {
    defaults: {
      model: { primary: "cloudflare-ai-gateway/claude-sonnet-4-6" },
      models: {
        "cloudflare-ai-gateway/claude-sonnet-4-6": { alias: "Claude Sonnet via Cloudflare" },
        "cloudflare-ai-gateway/claude-opus-4-6": { alias: "Claude Opus via Cloudflare" },
      },
    },
  },
}
```

### With environment variable

```json5
{
  env: { CLOUDFLARE_AI_GATEWAY_API_KEY: "${ANTHROPIC_API_KEY}" },
  models: {
    providers: {
      "cloudflare-ai-gateway": {
        accountId: "your-account-id",
        gatewayId: "your-gateway-id",
      },
    },
  },
  agents: {
    defaults: {
      model: { primary: "cloudflare-ai-gateway/claude-opus-4-6" },
    },
  },
}
```

## Advanced configuration

### Authenticated gateways

If you enabled Gateway authentication in Cloudflare, add the `cf-aig-authorization` header. This is **in addition to** your provider API key.

```json5
{
  models: {
    providers: {
      "cloudflare-ai-gateway": {
        headers: {
          "cf-aig-authorization": "Bearer <cloudflare-ai-gateway-token>",
        },
      },
    },
  },
}
```

**Tip:** The `cf-aig-authorization` header authenticates with the Cloudflare Gateway itself, while the provider API key (for example, your Anthropic key) authenticates with the upstream provider.

### Environment variable note

If the Gateway runs as a daemon (launchd/systemd), make sure `CLOUDFLARE_AI_GATEWAY_API_KEY` is available to that process.

**Warning:** A key exported only in an interactive shell will not help a launchd/systemd daemon unless that environment is imported there as well. Set the key in `~/.openclaw/.env` or via `env.shellEnv` to ensure the gateway process can read it.

## How it works

### Request flow

1. OpenClaw sends requests to your Cloudflare AI Gateway endpoint
2. The Gateway routes requests to Anthropic's API using your provider key
3. Responses return through the Gateway with analytics and caching applied
4. OpenClaw receives the response as if it came directly from the provider

### API compatibility

Cloudflare AI Gateway is compatible with Anthropic's Messages API. All features are preserved, including:

- Streaming responses
- Vision capabilities
- Tool use and function calling
- Extended thinking (when enabled)
- Prompt caching

### Thinking and prefill handling

When extended thinking is enabled on Anthropic models through Cloudflare AI Gateway:
- Trailing assistant prefill turns are automatically stripped before sending
- This is because Anthropic rejects response prefilling with extended thinking enabled
- Non-thinking prefill (ordinary assistant prefills) remains available and is preserved

## Gateway analytics

Once configured, Cloudflare AI Gateway tracks all requests through your account dashboard:

- Request counts and latencies
- Token usage and costs
- Cache hit rates (if caching is configured)
- Error rates and diagnostics

Access these metrics in your Cloudflare dashboard under the AI Gateway section.

## Caching and cost optimization

Cloudflare AI Gateway supports:

- **Request caching**: Cache API responses based on request similarity
- **Prompt caching**: Leverage Anthropic's prompt caching through the Gateway
- **Analytics-driven optimization**: Review usage patterns and adjust routing

See [Cloudflare AI Gateway caching documentation](https://developers.cloudflare.com/ai-gateway/features/) for setup details.

## Troubleshooting

### Authentication errors

- Verify your Anthropic API key is set correctly as `CLOUDFLARE_AI_GATEWAY_API_KEY`
- Confirm your account ID and gateway ID are correct in the config
- If using Gateway authentication, ensure the `cf-aig-authorization` token is valid

### Gateway not responding

- Check that your Cloudflare account has AI Gateway enabled
- Verify the gateway ID exists in your Cloudflare dashboard
- Ensure your API key has sufficient permissions

### Model not found

- Run `openclaw models list --provider cloudflare-ai-gateway` to see available models
- Ensure the model ref matches exactly (e.g., `claude-sonnet-4-6` not `claude-sonnet`)

### Prefill errors with thinking enabled

- OpenClaw automatically strips trailing prefill when thinking is enabled
- If you see prefill-related errors, verify your Anthropic account supports extended thinking
- Non-thinking models support ordinary prefill without restrictions

## Related

- [Model selection](/concepts/model-providers) - Choosing providers and failover behavior
- [Troubleshooting](/help/troubleshooting) - General troubleshooting and FAQ
- [Cloudflare AI Gateway Documentation](https://developers.cloudflare.com/ai-gateway/) - Official Cloudflare docs
- [Anthropic API Documentation](https://platform.claude.com/docs) - Anthropic Messages API reference
