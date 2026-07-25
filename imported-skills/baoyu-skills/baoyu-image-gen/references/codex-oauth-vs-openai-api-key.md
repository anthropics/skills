# Codex OAuth vs OpenAI API key for baoyu-image-gen

`baoyu-image-gen --provider openai` uses the standard OpenAI Images API and requires `OPENAI_API_KEY`. It calls OpenAI-compatible image endpoints such as `/images/generations` and `/images/edits`.

Codex / ChatGPT login is different. Codex image generation is driven by Codex OAuth and the Codex runtime's `image_gen` capability, not by the public OpenAI Images API key path. A Codex OAuth token is not a drop-in replacement for `OPENAI_API_KEY`, and setting `OPENAI_BASE_URL` to a Codex backend will not make baoyu-image-gen's existing `openai` provider work because the auth, route, and payload shape differ.

## What to use instead

- If running inside Codex and the native `imagegen` skill/tool is available, use it directly.
- If running outside Codex but the `codex` CLI is installed and logged in, call `baoyu-image-gen --provider codex-cli` (preferred). It spawns the bundled `scripts/codex-imagegen/main.ts` and surfaces its retry/cache/log machinery through baoyu-image-gen's standard CLI + batch flow. Standalone callers outside this skill can run the same code at `packages/baoyu-codex-imagegen/src/main.ts`. Both invoke `codex exec` and the Codex `image_gen` tool; no `OPENAI_API_KEY` is required.
- If running inside Hermes and a native `image_generate` tool is available, use that as a runtime-native fallback. Be explicit about whether reference images are passed directly or only reconstructed from extracted traits.
- `baoyu-image-gen` already exposes a distinct `codex-cli` provider (wraps the bundled `scripts/codex-imagegen/`); do not modify the existing `openai` provider to add Codex OAuth.

## Reference-image prompting note

When using actual reference images for identity preservation, avoid long generic descriptions of the subject. Long descriptions can cause the model to synthesize a new similar-looking person/object. Prefer direct wording:

> Use the person/object in the reference image(s) as the same identity. Do not redesign it or create a similar-looking new subject. Only change scene, clothing, pose, lighting, rendering style, and composition.
