OpenAI provides the **GPT** model family. OpenClaw supports multiple auth routes:

- **API key** - direct OpenAI Platform access with usage-based billing (`openai/*` models)
- **ChatGPT/Codex subscription** - reuse an existing ChatGPT subscription with the native Codex app-server runtime
- **Azure OpenAI** - Azure resource access with regional deployment support

## Usage and cost tracking

OpenClaw detects the available OpenAI credential and selects the matching usage surface:

- ChatGPT/Codex OAuth shows the subscription plan, quota windows, and credit balance.
- `OPENAI_ADMIN_KEY` shows 30 days of provider-reported organization cost and completions usage in Control UI **Usage**, including daily spend, request/token totals, top models, and cost categories.
- An `sk-org-admin...` credential stored in the OpenAI provider profile is detected as an Admin API key automatically.

Admin API cost history comes from OpenAI's [Usage Dashboard API](https://help.openai.com/en/articles/10478918). It is actual provider billing, separate from OpenClaw's session-derived estimated cost.

## Getting started

### API key

**Best for:** standard API access and usage-based billing through OpenAI Platform.

#### Steps

1. **Get your API key**
   - Create an API key in the [OpenAI Platform Console](https://platform.openai.com/api-keys).

2. **Run onboarding**
   ```bash
   openclaw onboard --auth-choice openai-api-key
   ```

   Or pass the key directly:

   ```bash
   openclaw onboard --openai-api-key "$OPENAI_API_KEY"
   ```

3. **Verify the model is available**
   ```bash
   openclaw models list --provider openai
   ```

#### Config example

```json5
{
  env: { OPENAI_API_KEY: "example-openai-key-not-real" },
  agents: { defaults: { model: { primary: "openai/gpt-5.6" } } },
}
```

The bare direct-API `gpt-5.6` id resolves to the Sol tier. If your API organization does not expose GPT-5.6, set the primary to `openai/gpt-5.5` explicitly.

### ChatGPT/Codex subscription

**Best for:** using your ChatGPT/Codex subscription with native Codex app-server execution instead of a separate API key.

#### Steps

1. **Run Codex OAuth**
   ```bash
   openclaw onboard --auth-choice openai
   ```

   Or run OAuth directly:

   ```bash
   openclaw models auth login --provider openai
   ```

   For headless or callback-hostile setups, add `--device-code` to sign in with a ChatGPT device-code flow:

   ```bash
   openclaw models auth login --provider openai --device-code
   ```

2. **Use the canonical OpenAI model route**
   ```bash
   openclaw config set agents.defaults.model.primary openai/gpt-5.6-sol
   ```

   No runtime config is required for this exact official HTTPS native route. It may select the Codex app-server runtime automatically.

3. **Verify Codex auth is available**
   ```bash
   openclaw models list --provider openai
   ```

   After the gateway is running, send `/codex status` or `/codex models` in chat to verify the native app-server runtime.

#### Config example

Prefer the canonical OpenAI model ref with Codex OAuth:

```json5
{
  plugins: { entries: { codex: { enabled: true } } },
  agents: {
    defaults: {
      model: { primary: "openai/gpt-5.6-sol" },
    },
  },
}
```

With an API-key backup, keep the selected model under `openai/*` and put the auth order under `openai`:

```json5
{
  plugins: { entries: { codex: { enabled: true } } },
  agents: {
    defaults: {
      model: { primary: "openai/gpt-5.6-sol" },
    },
  },
  auth: {
    order: {
      openai: [
        "openai:user@example.com",
        "openai:api-key-backup",
      ],
    },
  },
}
```

### Azure OpenAI

**Best for:** Azure-hosted OpenAI resources with regional data residency or compliance requirements.

#### Steps

1. **Get your Azure OpenAI credentials**
   - Create or retrieve an Azure OpenAI resource from the [Azure Portal](https://portal.azure.com).
   - Note the resource name, API key, and deployment name for your model.

2. **Run onboarding**
   ```bash
   openclaw onboard --auth-choice azure-openai
   ```

   Or configure directly:

   ```bash
   openclaw config set models.providers.openai.baseUrl "https://<your-resource>.openai.azure.com"
   openclaw config set models.providers.openai.apiKey "<azure-openai-api-key>"
   ```

3. **Verify the model is available**
   ```bash
   openclaw models list --provider openai
   ```

#### Config example

For Azure image generation through the bundled `openai` provider:

```json5
{
  models: {
    providers: {
      openai: {
        baseUrl: "https://<your-resource>.openai.azure.com",
        apiKey: "<azure-openai-api-key>",
      },
    },
  },
  agents: { defaults: { model: { primary: "openai/gpt-5.6" } } },
}
```

## GPT-5.6 model tiers

OpenClaw recognizes exact `openai/gpt-5.6-sol`, `openai/gpt-5.6-terra`, and `openai/gpt-5.6-luna` model ids:

| Tier  | Use case              | Cost                |
| ----- | --------------------- | ------------------- |
| Sol   | Flagship, highest quality | Standard pricing    |
| Terra | Balanced performance  | Moderate pricing    |
| Luna  | Fast, lower cost      | Lower pricing       |

Check available models for your account:

```bash
openclaw models list --provider openai
```

## Image generation

The bundled `openai` plugin registers image generation through the `image_generate` tool. It supports both OpenAI API-key and Codex OAuth image generation.

| Capability                | OpenAI API key                     | Codex OAuth                          |
| ------------------------- | ---------------------------------- | ------------------------------------ |
| Model ref                 | `openai/gpt-image-2`               | `openai/gpt-image-2`                 |
| Auth                      | `OPENAI_API_KEY`                   | OpenAI Codex OAuth sign-in           |
| Transport                 | OpenAI Images API                  | Codex Responses backend              |
| Max images per request    | 4                                  | 4                                    |
| Edit mode                 | Enabled (up to 5 reference images) | Enabled (up to 5 reference images)   |
| Size overrides            | Supported, including 2K/4K sizes   | Supported, including 2K/4K sizes     |

Generate:

```
/tool image_generate model=openai/gpt-image-2 prompt="A clean poster" size=1024x1024 count=1
```

Generate a transparent PNG:

```
/tool image_generate model=openai/gpt-image-1.5 prompt="A red circle on transparent background" outputFormat=png background=transparent
```

## Video generation

The bundled `openai` plugin registers video generation through the `video_generate` tool.

| Capability       | Value                                                  |
| ---------------- | ------------------------------------------------------ |
| Default model    | `openai/sora-2`                                        |
| Modes            | Text-to-video, image-to-video, single-video edit       |
| Reference inputs | 1 image or 1 video                                     |

## Voice and speech

### Speech synthesis (TTS)

The bundled `openai` plugin registers speech synthesis for the `tts` surface.

| Setting      | Default                          |
| ------------- | ----------------------------------- |
| Model        | `gpt-4o-mini-tts`                |
| Voice        | `coral`                          |
| Voices       | `alloy`, `ash`, `ballad`, `cedar`, `coral`, `echo`, `fable`, `juniper`, `marin`, `onyx`, `nova`, `sage`, `shimmer`, `verse` |

```json5
{
  tts: {
    providers: {
      openai: { model: "gpt-4o-mini-tts", speakerVoice: "coral" },
    },
  },
}
```

### Speech-to-text (STT)

The bundled `openai` plugin registers batch speech-to-text through OpenClaw's media-understanding transcription surface.

- Default model: `gpt-4o-transcribe`
- Endpoint: OpenAI REST `/v1/audio/transcriptions`

### Realtime voice

The bundled `openai` plugin registers realtime voice for the Voice Call plugin using GPT-Realtime models.

| Setting              | Default                    |
| -------------------- | -------------------------- |
| Model                | `gpt-realtime-2.1`         |
| Voice                | `alloy`                    |
| Voices               | `alloy`, `ash`, `ballad`, `cedar`, `coral`, `echo`, `marin`, `sage`, `shimmer`, `verse` |

For GPT-Live browser Talk over ChatGPT OAuth:

```json5
{
  talk: {
    realtime: {
      provider: "openai",
      model: "gpt-live-1-codex",
      transport: "webrtc",
    },
  },
}
```

## Advanced configuration

### Transport (WebSocket vs SSE)

OpenClaw uses WebSocket-first with SSE fallback (`"auto"`) for `openai/*`:

```json5
{
  agents: {
    defaults: {
      models: {
        "openai/gpt-5.5": {
          params: { transport: "auto" },
        },
      },
    },
  },
}
```

| Value                | Behavior                          |
| ---------------------- | ------------------------------------ |
| `"auto"` (default)   | WebSocket first, SSE fallback     |
| `"sse"`              | Force SSE only                    |
| `"websocket"`        | Force WebSocket only              |

### Fast mode

Enable fast mode for higher output-token throughput on OpenAI priority processing:

```json5
{
  agents: {
    defaults: {
      models: {
        "openai/gpt-5.6": { params: { fastMode: "auto", fastAutoOnSeconds: 30 } },
      },
    },
  },
}
```

| Command | Effect                                      |
| --- | --- |
| `/fast on` | Enable priority processing (`service_tier = "priority"`) |
| `/fast auto` | Enable for first 60 seconds, then standard |
| `/fast off` | Standard speed; no priority processing |

### Server-side compaction

For direct OpenAI Responses models, enable server-side compaction for better context management:

```json5
{
  agents: {
    defaults: {
      models: {
        "openai/gpt-5.5": {
          params: {
            responsesServerCompaction: true,
            responsesCompactThreshold: 700000,
          },
        },
      },
    },
  },
}
```

### Priority processing (service_tier)

Set OpenAI priority processing per model:

```json5
{
  agents: {
    defaults: {
      models: {
        "openai/gpt-5.5": { params: { serviceTier: "priority" } },
      },
    },
  },
}
```

Supported values: `auto`, `default`, `flex`, `priority`.

## Context window and long-context opt-in

OpenClaw treats the provider's total model window and the active runtime budget separately:

- `contextWindow` declares the provider's total model window.
- `contextTokens` caps how much OpenClaw uses for active input.

Direct API-key GPT-5.5 and GPT-5.6 models default to `272000` `contextTokens` for consistency. The OpenAI Platform exposes a larger native window (`1050000` tokens), but the default keeps normal latency, quality, and cost profile consistent.

To opt into the full long-context allowance:

```json5
{
  models: {
    providers: {
      openai: {
        models: [
          {
            id: "gpt-5.6-terra",
            contextWindow: 1050000,
            contextTokens: 922000,
            maxTokens: 128000,
          },
        ],
      },
    },
  },
  agents: {
    defaults: {
      models: {
        "openai/gpt-5.6-terra": {
          params: {
            responsesServerCompaction: true,
            responsesCompactThreshold: 700000,
          },
        },
      },
    },
  },
}
```

**Warning:** OpenAI applies higher long-context pricing once a request exceeds 272000 input tokens: the whole qualifying request is billed at 2× input and 1.5× output rates. Opt-in sessions can cost substantially more than the default even when the visible reply is short.

## Troubleshooting

### 401 errors / invalid API key

Verify your API key is correct and has not expired:

```bash
openclaw models status
```

For new setups, use a fresh API key from the OpenAI Platform Console.

### No API key found for provider "openai"

OpenAI auth is **per agent**; new agents do not inherit the main agent's keys. Re-run onboarding for that agent, then verify with:

```bash
openclaw models status
```

### Rate limit cooldown

Check `openclaw models status --json` for `auth.unusableProfiles`. Add another OpenAI profile or wait for the rate-limit cooldown to expire.

### Model not found

Verify the model is available for your account:

```bash
openclaw models list --provider openai
```

If GPT-5.6 is not available, select GPT-5.5 explicitly:

```bash
openclaw models set openai/gpt-5.5
```

## Additional resources

- [OpenAI Platform Documentation](https://platform.openai.com/docs)
- [Model comparison and pricing](https://developers.openai.com/api/docs/models/compare)
- [GPT-5.6 launch announcement](https://openai.com/index/previewing-gpt-5-6-sol/)
- [Image generation guide](https://platform.openai.com/docs/guides/images)
- [Audio guide](https://platform.openai.com/docs/guides/audio)
- [Realtime API guide](https://platform.openai.com/docs/guides/realtime-websocket)
- [Troubleshooting](/help/troubleshooting)
- [FAQ](/help/faq)
