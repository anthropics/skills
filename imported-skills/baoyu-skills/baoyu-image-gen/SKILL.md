---
name: baoyu-image-gen
description: AI image generation with OpenAI GPT Image 2, Azure OpenAI, Google, OpenRouter, DashScope, Z.AI GLM-Image, MiniMax, Jimeng, Seedream, Replicate and Agnes APIs. Supports text-to-image, reference images, aspect ratios, and batch generation from saved prompt files. Sequential by default; use batch parallel generation when the user already has multiple prompts or wants stable multi-image throughput. Use when user asks to generate, create, or draw images.
version: 2.1.0
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-image-gen
    requires:
      anyBins:
        - bun
        - npx
---

# Image Generation (AI SDK)

Official API-based image generation. Supports OpenAI GPT Image 2, Azure OpenAI, Google, OpenRouter, DashScope (阿里通义万象), Z.AI GLM-Image, MiniMax, Jimeng (即梦), Seedream (豆包), Replicate and Agnes.

## User Input Tools

When this skill prompts the user, follow this tool-selection rule (priority order):

1. **Prefer built-in user-input tools** exposed by the current agent runtime — e.g., `AskUserQuestion`, `request_user_input`, `clarify`, `ask_user`, or any equivalent.
2. **Fallback**: if no such tool exists, emit a numbered plain-text message and ask the user to reply with the chosen number/answer for each question.
3. **Batching**: if the tool supports multiple questions per call, combine all applicable questions into a single call; if only single-question, ask them one at a time in priority order.

Concrete `AskUserQuestion` references below are examples — substitute the local equivalent in other runtimes.

## Script Directory

`{baseDir}` = this SKILL.md's directory. All `scripts/...` paths below are relative to `{baseDir}`. Main script: `{baseDir}/scripts/main.ts`. Batch payload helper: `{baseDir}/scripts/build-batch.ts`. Resolve `${BUN_X}`: prefer `bun`; else `npx -y bun`; else suggest `brew install oven-sh/bun/bun`.

## Step 0: Load Preferences ⛔ BLOCKING

This step MUST complete before any image generation — generation is blocked until EXTEND.md exists.

Check these paths in order; first hit wins:

| Path | Scope |
|------|-------|
| `.baoyu-skills/baoyu-image-gen/EXTEND.md` | Project |
| `${XDG_CONFIG_HOME:-$HOME/.config}/baoyu-skills/baoyu-image-gen/EXTEND.md` | XDG |
| `$HOME/.baoyu-skills/baoyu-image-gen/EXTEND.md` | User home |

- **Found** → load, parse, apply. If `default_model.[provider]` is null → ask model only.
- **Not found** → run first-time setup (`references/config/first-time-setup.md`) using AskUserQuestion to collect provider + model + quality + save location. Save EXTEND.md, then continue. Do not generate images before this completes.

Legacy compatibility: if `.baoyu-skills/baoyu-imagine/EXTEND.md` exists and the new path doesn't, the runtime renames it to `baoyu-image-gen`. If both exist, the runtime leaves them alone and uses the new path.

**EXTEND.md keys**: default provider, default quality, default aspect ratio, default image size, OpenAI image API dialect, default models, batch worker cap, provider-specific batch limits. Schema: `references/config/preferences-schema.md`.

## Usage

Minimum working examples — see `references/usage-examples.md` for the full set including per-provider invocations and batch mode.

### Identity-preserving reference prompts

When the user wants a real person/character/object preserved from reference images, do **not** replace the reference with a long generic description. Prefer short, hard identity-preservation language:

- "Use the person/object in the reference image(s) as the same identity. Do not redesign it or create a similar-looking new subject."
- "Only change scene, clothing, pose, lighting, rendering style, and composition. Keep the face/proportions/hair/key accessories/overall identity from the references."
- If using multiple references, state that they are the same subject and should jointly define identity.

Pitfall: long descriptions like "young East Asian woman, oval face, clear eyes..." can cause the model to synthesize a new person matching the description instead of preserving the referenced person.

```bash
# Basic
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image cat.png

# With aspect ratio and high quality
${BUN_X} {baseDir}/scripts/main.ts --prompt "A landscape" --image out.png --ar 16:9 --quality 2k

# Prompt from files
${BUN_X} {baseDir}/scripts/main.ts --promptfiles system.md content.md --image out.png

# With reference image
${BUN_X} {baseDir}/scripts/main.ts --prompt "Make blue" --image out.png --ref source.png

# Specific provider
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider dashscope --model qwen-image-2.0-pro

# OpenAI GPT Image 2
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider openai --model gpt-image-2

# Codex CLI (uses logged-in Codex subscription — no OPENAI_API_KEY required; requires `codex` on PATH)
${BUN_X} {baseDir}/scripts/main.ts --prompt "A cat" --image out.png --provider codex-cli --ar 16:9

# Batch mode
${BUN_X} {baseDir}/scripts/main.ts --batchfile batch.json --jobs 4

# Build a batch file from outline.md + prompts/ (e.g. baoyu-article-illustrator output)
${BUN_X} {baseDir}/scripts/build-batch.ts --outline outline.md --prompts prompts --output batch.json --images-dir attachments
${BUN_X} {baseDir}/scripts/main.ts --batchfile batch.json --jobs 4
```

## Reference-Image Identity Preservation

When the user wants a person/object preserved from reference images:

- Prefer a small curated set of existing source references (usually 2–4) over many images; large multi-megabyte refs can destabilize streaming providers.
- Make the prompt say the references are the same subject and the output must use that identity. Avoid long generic facial-feature descriptions that can cause the model to synthesize a new similar-looking person.
- Do not use newly generated outputs as references unless the user explicitly asks; generated refs compound drift.
- If results become too polished or influencer-like, reduce stylized refs and add explicit anti-beautification constraints (no face slimming, eye enlargement, heavy makeup, commercial travel shoot, over-smoothing).
- If the subject should look younger/older, preserve the face and express age through clothing, posture, scene, and styling; do not ask the model to change facial identity.

## Options

| Option | Description |
|--------|-------------|
| `--prompt <text>`, `-p` | Prompt text |
| `--promptfiles <files...>` | Read prompt from files (concatenated) |
| `--image <path>` | Output image path (required in single-image mode) |
| `--batchfile <path>` | JSON batch file for multi-image generation |
| `--jobs <count>` | Worker count for batch mode (default: auto, max from config, built-in default 10) |
| `--provider google\|openai\|azure\|openrouter\|dashscope\|zai\|minimax\|jimeng\|seedream\|replicate\|codex-cli\|agnes` | Force provider (default: auto-detect; `codex-cli` is never auto-selected — must be pinned via CLI or EXTEND.md) |
| `--model <id>`, `-m` | Model ID — see provider references for defaults and allowed values |
| `--ar <ratio>` | Aspect ratio (`16:9`, `1:1`, `4:3`, …) |
| `--size <WxH>` | Explicit size (e.g., `1024x1024`; for `gpt-image-2`, width/height must be multiples of 16, max edge 3840px, ratio no wider than 3:1) |
| `--quality normal\|2k` | Quality preset (default: `2k`) |
| `--imageSize 1K\|2K\|4K` | Image size for Google/OpenRouter (default: from quality) |
| `--imageApiDialect openai-native\|ratio-metadata` | OpenAI-compatible endpoint dialect — use `ratio-metadata` for gateways that expect aspect-ratio `size` plus `metadata.resolution` |
| `--ref <files...>` | Reference images. Supported by Google multimodal, OpenAI GPT Image edits, Azure OpenAI edits (PNG/JPG only), OpenRouter multimodal models, Replicate supported families, MiniMax subject-reference, Seedream 5.0/4.5/4.0, DashScope `wan2.7-image-pro`/`wan2.7-image`. Not supported by Jimeng, Seedream 3.0, SeedEdit 3.0, or any DashScope model outside the `wan2.7-image*` family |
| `--n <count>` | Number of images. Replicate requires `--n 1` (single-output save semantics) |
| `--json` | JSON output |

## Environment Variables

| Variable | Description |
|----------|-------------|
| `OPENAI_API_KEY` | OpenAI API key |
| `AZURE_OPENAI_API_KEY` | Azure OpenAI API key |
| `OPENROUTER_API_KEY` | OpenRouter API key |
| `GOOGLE_API_KEY` | Google API key |
| `DASHSCOPE_API_KEY` | DashScope API key |
| `ZAI_API_KEY` (alias `BIGMODEL_API_KEY`) | Z.AI API key |
| `MINIMAX_API_KEY` | MiniMax API key |
| `REPLICATE_API_TOKEN` | Replicate API token |
| `JIMENG_ACCESS_KEY_ID`, `JIMENG_SECRET_ACCESS_KEY` | Jimeng (即梦) Volcengine credentials |
| `ARK_API_KEY` | Seedream (豆包) Volcengine ARK API key |
| `<PROVIDER>_IMAGE_MODEL` | Per-provider model override (`OPENAI_IMAGE_MODEL`, `GOOGLE_IMAGE_MODEL`, `DASHSCOPE_IMAGE_MODEL`, `ZAI_IMAGE_MODEL`/`BIGMODEL_IMAGE_MODEL`, `MINIMAX_IMAGE_MODEL`, `OPENROUTER_IMAGE_MODEL`, `REPLICATE_IMAGE_MODEL`, `JIMENG_IMAGE_MODEL`, `SEEDREAM_IMAGE_MODEL`, `AGNES_IMAGE_MODEL`) |
| `AZURE_OPENAI_DEPLOYMENT` (alias `AZURE_OPENAI_IMAGE_MODEL`) | Azure default deployment |
| `<PROVIDER>_BASE_URL` | Per-provider endpoint override |
| `AZURE_API_VERSION` | Azure image API version (default `2025-04-01-preview`) |
| `JIMENG_REGION` | Jimeng region (default `cn-north-1`) |
| `OPENAI_IMAGE_API_DIALECT` | `openai-native` \| `ratio-metadata` |
| `OPENROUTER_HTTP_REFERER`, `OPENROUTER_TITLE` | Optional OpenRouter attribution |
| `BAOYU_IMAGE_GEN_MAX_WORKERS` | Override batch worker cap |
| `BAOYU_IMAGE_GEN_<PROVIDER>_CONCURRENCY` | Per-provider concurrency (e.g., `BAOYU_IMAGE_GEN_REPLICATE_CONCURRENCY`; for codex-cli use `BAOYU_IMAGE_GEN_CODEX_CLI_CONCURRENCY`) |
| `BAOYU_IMAGE_GEN_<PROVIDER>_START_INTERVAL_MS` | Per-provider start-gap |
| `BAOYU_CODEX_IMAGEGEN_BIN` | Override the codex-imagegen wrapper path for the `codex-cli` provider (default: bundled `scripts/codex-imagegen/main.ts`; accepts `.ts` or legacy `.sh`/binary) |
| `BAOYU_CODEX_IMAGEGEN_CACHE_DIR` | Enable idempotency cache for the `codex-cli` provider (off by default) |
| `BAOYU_CODEX_IMAGEGEN_TIMEOUT_MS` | Per-attempt `codex exec` timeout for the `codex-cli` provider (default: 300000 ms) |
| `BAOYU_CODEX_IMAGEGEN_RETRIES` | Wrapper-side retry attempts on retryable errors for the `codex-cli` provider (default: 2) |
| `BAOYU_CODEX_IMAGEGEN_LOG_FILE` | Append JSONL diagnostic log for the `codex-cli` provider |

**Load priority**: CLI args > EXTEND.md > env vars > `<cwd>/.baoyu-skills/.env` > `~/.baoyu-skills/.env`

### Codex/ChatGPT OAuth is not an OpenAI API key

`--provider openai --model gpt-image-2` uses the standard OpenAI Images API (`/v1/images/generations` or `/v1/images/edits`) and requires `OPENAI_API_KEY`. A Codex or ChatGPT desktop login is a different entitlement and is not a drop-in replacement for `OPENAI_API_KEY`; do not paste a Codex OAuth token into `OPENAI_API_KEY` or only set `OPENAI_BASE_URL` to a Codex backend.

If the user wants to use their Codex subscription / GPT Image 2 entitlement without an OpenAI API key, route through a Codex-native backend instead of this skill's `openai` provider:

- In Codex runtime: use the native `imagegen` skill/tool.
- In non-Codex runtimes with `codex` CLI installed and logged in: use `baoyu-image-gen --provider codex-cli` (preferred — it gives you the same retry / cache / batch flow as every other provider). The provider spawns the bundled `scripts/codex-imagegen/main.ts`; the same code lives upstream at `packages/baoyu-codex-imagegen/src/main.ts` for standalone callers.
- In Hermes runtimes with a native `image_generate` tool: use that tool as a fallback, and state whether reference images were passed directly or reconstructed from extracted traits.

Do not modify the existing `openai` provider to silently consume Codex OAuth. The first-class Codex-CLI path is the dedicated `codex-cli` provider, which has its own auth (Codex login), route (`codex exec`), request shape, and tests. See `references/codex-oauth-vs-openai-api-key.md`.

## Model Resolution

Priority (highest → lowest) applies to every provider:

1. CLI flag `--model <id>`
2. EXTEND.md `default_model.[provider]`
3. Env var `<PROVIDER>_IMAGE_MODEL`
4. Built-in default

For OpenAI, the built-in default is `gpt-image-2`. `gpt-image-1.5`, `gpt-image-1`, and GPT Image snapshots remain selectable with `--model` or `OPENAI_IMAGE_MODEL`.

For Azure, `--model` / `default_model.azure` is the Azure deployment name. `AZURE_OPENAI_DEPLOYMENT` is the preferred env var; `AZURE_OPENAI_IMAGE_MODEL` is kept as a backward-compatible alias. If your Azure deployment is named after the underlying model, use `gpt-image-2`; otherwise use the exact custom deployment name.

EXTEND.md overrides env vars: if EXTEND.md sets `default_model.google: "gemini-3-pro-image"` and the env var sets `GOOGLE_IMAGE_MODEL=gemini-3.1-flash-image`, EXTEND.md wins.

**Display model info before each generation**:

- `Using [provider] / [model]`
- `Switch model: --model <id> | EXTEND.md default_model.[provider] | env <PROVIDER>_IMAGE_MODEL`

## OpenAI-Compatible Gateway Dialects

`provider=openai` means the auth and routing entrypoint is OpenAI-compatible. It does **not** guarantee the upstream image API uses OpenAI native semantics. When a gateway expects a different wire format, set `default_image_api_dialect` in EXTEND.md, `OPENAI_IMAGE_API_DIALECT`, or `--imageApiDialect`:

- `openai-native`: pixel `size` (`1536x1024`) and native OpenAI quality fields
- `ratio-metadata`: aspect-ratio `size` (`16:9`) plus `metadata.resolution` (`1K|2K|4K`) and `metadata.orientation`

Use `openai-native` for the OpenAI native API or strict clones; try `ratio-metadata` for compatibility gateways in front of Gemini or similar models. Current limitation: `ratio-metadata` applies only to text-to-image; reference-image edits still need `openai-native` or a provider with first-class edit support.

## Provider-Specific Guides

Each provider has its own quirks (model families, size rules, ref support, limits). Read these when the user picks that provider or asks for non-default behavior:

| Provider | Reference |
|----------|-----------|
| DashScope (Qwen-Image families, custom sizes) | `references/providers/dashscope.md` |
| Z.AI (GLM-Image, cogview-4) | `references/providers/zai.md` |
| MiniMax (image-01, subject-reference) | `references/providers/minimax.md` |
| OpenRouter (multimodal models, `/chat/completions` flow) | `references/providers/openrouter.md` |
| Replicate (nano-banana, Seedream, Wan) | `references/providers/replicate.md` |
| Codex CLI (wraps bundled `scripts/codex-imagegen/`; Codex login, no `OPENAI_API_KEY`) | `references/providers/codex-cli.md` |
| Agnes (agnes-image-2.1-flash, reference-image support) | `references/providers/agnes.md` |

## Provider Selection

1. `--ref` provided + no `--provider` → auto-select Google → OpenAI → Azure → OpenRouter → Replicate → Seedream → MiniMax → Agnes (MiniMax's subject reference is more specialized toward character/portrait consistency)
2. `--provider` specified → use it (if `--ref`, must be google/openai/azure/openrouter/replicate/seedream/minimax/codex-cli/agnes)
3. Only one API key present → use that provider
4. Multiple keys → default priority: Google → OpenAI → Azure → OpenRouter → DashScope → Z.AI → MiniMax → Replicate → Jimeng → Seedream → Agnes
5. `codex-cli` is **never auto-selected** — set `default_provider: codex-cli` in EXTEND.md or pass `--provider codex-cli`. It spawns `codex exec` via the bundled `scripts/codex-imagegen/main.ts` TS entrypoint (run with `bun`) and uses the user's Codex subscription (no `OPENAI_API_KEY`). Requires `codex` on `PATH` with an active `codex login`.

## Quality Presets

| Preset | Google imageSize | OpenAI size | OpenRouter size | Replicate resolution | Use case |
|--------|------------------|-------------|-----------------|----------------------|----------|
| `normal` | 1K | 1024px target | 1K | 1K | Quick previews |
| `2k` (default) | 2K | 2048px target | 2K | 2K | Covers, illustrations, infographics |

Google/OpenRouter `imageSize` can be overridden with `--imageSize 1K|2K|4K`.

For OpenAI native `gpt-image-2`, `normal` maps to `quality=medium` and a low-latency valid size near the requested aspect ratio; `2k` maps to `quality=high` and 2048px-class sizes such as `2048x2048`, `2048x1152`, or `1152x2048`. Use explicit `--size` for valid custom or 4K outputs, e.g. `3840x2160`.

## Aspect Ratios

Supported: `1:1`, `16:9`, `9:16`, `4:3`, `3:4`, `2.35:1`.

- Google multimodal: `imageConfig.aspectRatio`
- OpenAI: `gpt-image-2` uses the closest valid custom size for the requested ratio; older GPT Image and DALL·E models use their closest supported fixed size
- OpenRouter: `imageGenerationOptions.aspect_ratio`; if only `--size <WxH>` is given, the ratio is inferred
- Replicate: behavior is model-specific — `google/nano-banana*` uses `aspect_ratio`, `bytedance/seedream-*` uses documented Replicate ratios, Wan 2.7 maps `--ar` to a concrete `size`
- MiniMax: official `aspect_ratio` values; if `--size <WxH>` is given without `--ar`, sends `width`/`height` for `image-01`

## Generation Mode

**Default**: sequential. **Batch parallel**: enabled automatically when `--batchfile` contains 2+ pending tasks.

| Situation | Prefer | Why |
|-----------|--------|-----|
| One image, or 1-2 simple images | Sequential | Lower coordination overhead, easier debugging |
| Multiple images with saved prompt files | Batch (`--batchfile`) | Reuses finalized prompts, applies shared throttling/retries, predictable throughput |
| Each image still needs its own reasoning / prompt writing / style exploration | Subagents | Work is still exploratory, each needs independent analysis |
| Input is `outline.md` + `prompts/` (e.g. from `baoyu-article-illustrator`) | Batch — use `{baseDir}/scripts/build-batch.ts` to assemble the payload | The outline + prompt files already contain everything needed |

Rule of thumb: once prompt files are saved and the task is "generate all of these", prefer batch over subagents. Use subagents only when generation is coupled with per-image thinking or divergent creative exploration.

**Parallel behavior**:

- Default worker count is automatic, capped by config, built-in default 10
- Provider-specific throttling applies only in batch mode; defaults are tuned for throughput while avoiding RPM bursts
- Override with `--jobs <count>`
- Each image retries up to 3 attempts
- Final output includes success count, failure count, and per-image failure reasons

## Error Handling

- Missing API key → error with setup instructions
- Generation failure → auto-retry up to 3 attempts per image
- Invalid aspect ratio → warning, proceed with default
- Reference images with unsupported provider/model → error with fix hint

### Codex image2 fallback

If `--provider openai --model gpt-image-2` fails because `OPENAI_API_KEY` is missing but the current runtime has a native image-generation backend or the repo-level `codex-imagegen` wrapper is available, use that path rather than leaving the user waiting. Be explicit about whether the fallback is true reference-image generation or only a text-prompt reconstruction from extracted visual traits. See `references/codex-image2-fallback.md`.

## References

| File | Content |
|------|---------|
| `references/usage-examples.md` | Extended CLI examples across providers and batch mode |
| `references/codex-oauth-vs-openai-api-key.md` | Why Codex/ChatGPT OAuth image2 entitlement is not usable through baoyu-image-gen's standard OpenAI API-key provider |
| `references/codex-image2-fallback.md` | Practical fallback behavior when OpenAI API credentials are absent but Codex/native image generation is available |
| `references/providers/dashscope.md` | DashScope families, sizes, limits |
| `references/providers/zai.md` | Z.AI GLM-image / cogview-4 |
| `references/providers/minimax.md` | MiniMax image-01 + subject reference |
| `references/providers/openrouter.md` | OpenRouter multimodal flow |
| `references/providers/replicate.md` | Replicate supported families + guardrails |
| `references/providers/agnes.md` | Agnes (agnes-image-2.1-flash) sizing, refs, and limits |
| `references/config/preferences-schema.md` | EXTEND.md schema |
| `references/config/first-time-setup.md` | First-time setup flow |

## Extension Support

Custom configurations via EXTEND.md. See Step 0 for paths and schema.
