---
name: codex-image2-fallback
description: Fallback behavior when baoyu-image-gen lacks OpenAI API credentials but Codex/native image generation is available
---

# Codex Image2 Fallback

When using `baoyu-image-gen` with `--provider openai --model gpt-image-2`, the CLI can fail with:

```text
OPENAI_API_KEY is required. Codex/ChatGPT desktop login does not automatically grant OpenAI Images API access to this script.
```

This is expected. The `openai` provider uses the public OpenAI Images API and needs `OPENAI_API_KEY`. Codex / ChatGPT image2 entitlement is a separate runtime-native path.

## Practical fallback pattern

1. Try `baoyu-image-gen` when provider credentials are available.
2. If it fails only because `OPENAI_API_KEY` is missing, do not leave the user waiting.
3. Prefer a Codex/native raster backend in this order:
   - Codex runtime native `imagegen` skill/tool, if available.
   - `baoyu-image-gen --provider codex-cli` (preferred — wraps the bundled `scripts/codex-imagegen/main.ts`; the underlying repo-level package lives at `packages/baoyu-codex-imagegen/src/main.ts` for standalone callers), if `codex` CLI is installed/logged in.
   - Hermes native `image_generate`, if available.
4. Be transparent about reference-image behavior:
   - If the fallback backend accepts references, pass the reference images.
   - If it does not, derive a concise identity-preserving prompt from the references and state that it is a text-description fallback, not strict reference-image editing.
5. Return the generated media path or structured backend error promptly.

## User-facing wording

Use concise wording such as:

> The OpenAI API path needs `OPENAI_API_KEY`; Codex login is a separate image2 backend. I used the available Codex/native image backend instead. Reference images were [passed directly / reconstructed from visual traits].

Avoid implying that `baoyu-image-gen --provider openai` can use Codex OAuth without a dedicated provider implementation.
