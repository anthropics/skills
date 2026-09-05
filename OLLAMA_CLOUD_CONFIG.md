# Ollama Cloud Configuration

Ollama Cloud is Ollama's hosted model API. The `ollama-cloud` provider calls it directly at `https://ollama.com` over Ollama's native `/api/chat` API, with no local Ollama server and no local Ollama app signed into cloud mode. Use model refs like `ollama-cloud/kimi-k2.6`.

OpenClaw registers `ollama-cloud` as its own provider id so cloud-only credentials, live catalog discovery, and model selection do not get mixed with a local `ollama` host. For local Ollama, hybrid cloud-plus-local routing, embeddings, and custom host details, see [Ollama](/providers/ollama).

## Setup

Follow [Ollama's API key instructions](https://docs.ollama.com/api/authentication#api-keys), then run:

```bash
openclaw onboard --auth-choice ollama-cloud
```

Or set:

```bash
export OLLAMA_API_KEY="<your-ollama-cloud-api-key>"
```

Non-interactive onboarding accepts the key directly:

```bash
openclaw onboard --auth-choice ollama-cloud --ollama-cloud-api-key "<key>"
```

Onboarding sets the default model to `ollama-cloud/minimax-m2.7`.

## Defaults

- Provider: `ollama-cloud`
- Base URL: `https://ollama.com`
- Env var: `OLLAMA_API_KEY`
- API style: Ollama native `/api/chat`
- Onboarding default model: `ollama-cloud/minimax-m2.7`

## When to choose Ollama Cloud

- You want hosted Ollama models without running `ollama serve` locally.
- You want the same native Ollama chat API shape OpenClaw uses for local Ollama, but pointed at `https://ollama.com`.
- You want a simple cloud path for models that are already in Ollama's hosted catalog.
- You do not need local model pulls, local GPU control, or LAN-only inference.

Use [Ollama](/providers/ollama) instead when you want local-only or cloud-plus-local routing through a signed-in Ollama host. Use an OpenAI-compatible provider instead when you need `/v1/chat/completions` semantics or provider-specific OpenAI-style features.

## Models

The provider requires an API key; without one it stays inactive. With a key, OpenClaw discovers Ollama Cloud models live from the hosted catalog:

```bash
openclaw models list --provider ollama-cloud
openclaw models set ollama-cloud/kimi-k2.6
```

Hosted ids in the live catalog include:
- `deepseek-v4-flash`
- `glm-5.2`
- `gpt-oss:20b`
- `kimi-k2.6`
- `minimax-m2.7`

When live discovery returns nothing, OpenClaw falls back to the bundled rows `minimax-m2.7`, `glm-5.1`, and `glm-5.2`. The retiring `kimi-k2.5` model is hidden from model pickers but remains selectable by exact reference until Ollama retires it on July 31, 2026.

Model ids are cloud catalog ids, not local pull names. If a model name works in a local Ollama host but is absent from the hosted catalog, use the `ollama` provider with that local host instead.

## Configuration example

```json5
{
  env: { OLLAMA_API_KEY: "your-api-key-here" },
  agents: {
    defaults: {
      model: { primary: "ollama-cloud/kimi-k2.6" },
      models: {
        "ollama-cloud/kimi-k2.6": { alias: "Ollama Cloud - Kimi K2.6" },
        "ollama-cloud/minimax-m2.7": { alias: "Ollama Cloud - MiniMax M2.7" },
      },
    },
  },
}
```

## Live testing

For Ollama Cloud API-key smoke tests, point the Ollama live test at the hosted endpoint and choose a model from your current catalog:

```bash
export OLLAMA_API_KEY="<your-ollama-cloud-api-key>"

OPENCLAW_LIVE_TEST=1 \
OPENCLAW_LIVE_OLLAMA=1 \
OPENCLAW_LIVE_OLLAMA_BASE_URL=https://ollama.com \
OPENCLAW_LIVE_OLLAMA_MODEL=kimi-k2.6 \
pnpm test:live -- extensions/ollama/ollama.live.test.ts
```

The cloud smoke runs text, native stream, and web search; set `OPENCLAW_LIVE_OLLAMA_WEB_SEARCH=0` to skip web search. It skips embeddings by default for `https://ollama.com` because Ollama Cloud API keys may not authorize `/api/embed`; force them with `OPENCLAW_LIVE_OLLAMA_EMBEDDINGS=1`.

## Troubleshooting

### Ollama Cloud requires an API key / Set OLLAMA_API_KEY errors

Provide a real cloud API key. The local `ollama-local` marker is only for local or private Ollama hosts.

### Unknown model errors

Run `openclaw models list --provider ollama-cloud` and copy the hosted model id exactly.

### Tool-call or raw JSON issues on custom Ollama hosts

Check whether you are accidentally using an OpenAI-compatible `/v1` URL. Ollama routes should use the native base URL with no `/v1` suffix.

## API compatibility

Ollama Cloud uses Ollama's native `/api/chat` endpoint, which provides:

- Full streaming support
- Native JSON mode for structured responses
- Tool calling via function definitions
- Multi-turn conversations
- Stop sequences and token limits

OpenClaw's Ollama Cloud integration preserves these native capabilities without translation through an OpenAI-compatible shim.

## Performance and cost considerations

- API key authentication is required for every request to Ollama Cloud.
- Models are hosted and served by Ollama; latency depends on Ollama's infrastructure and your network.
- Rate limits and quotas apply per API key; check Ollama's dashboard for usage and limits.
- Unlike local Ollama, there is no local caching or GPU fallback; all requests go to the cloud.

## Model update frequency

The live model catalog is refreshed automatically. To manually refresh:

```bash
openclaw models list --provider ollama-cloud --force-refresh
```

New models added to Ollama Cloud's hosted catalog appear within the next discovery cycle. Deprecated models remain selectable by exact reference for a grace period before removal.

## Related

- [Ollama](/providers/ollama) - Local and hybrid Ollama setups
- [Model providers](/concepts/model-providers) - Choosing providers and failover behavior
- [All providers](/providers/index) - Full provider overview
- [Ollama Cloud Documentation](https://docs.ollama.com) - Official Ollama docs
