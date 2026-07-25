# Codex CLI (`--provider codex-cli`)

Read when the user picks `--provider codex-cli`, sets `default_provider: codex-cli`, or asks for "Codex image generation without an OpenAI API key". This provider is a thin baoyu-image-gen wrapper around the bundled `scripts/codex-imagegen/main.ts` (synced from `packages/baoyu-codex-imagegen`), which spawns `codex exec --json --sandbox danger-full-access` and routes the request to Codex CLI's built-in `image_gen` tool. The Codex CLI uses the **user's Codex / ChatGPT subscription** — no `OPENAI_API_KEY` is read or sent.

## Prerequisites

```bash
npm install -g @openai/codex
codex login            # signs in with the user's OpenAI / Codex account
codex --version        # confirm >= 0.130
```

`bun` is required for running the underlying wrapper (`scripts/codex-imagegen/main.ts`, carrying `#!/usr/bin/env bun`). If `bun` is missing from the runtime, `npx -y bun` works as a fallback.

## Selection

- **Never auto-selected.** `detectProvider` only picks `codex-cli` when it is pinned explicitly: pass `--provider codex-cli` or set `default_provider: codex-cli` in EXTEND.md.
- Choose this provider when:
  - The user has a Codex subscription and explicitly does **not** want to manage an OpenAI API key.
  - You need Codex's specific `image_gen` behavior or quality.
- Avoid this provider when latency matters — Codex CLI is typically 5–10× slower than direct OpenAI / Google API calls (except on cache hits).

## Supported flags

| Flag | Behavior |
|------|----------|
| `--prompt <text>` / `--promptfiles <files>` | Required. Written to a temp file and passed to the wrapper as `--prompt-file`. |
| `--image <path>` | Required. Final output PNG location. |
| `--ar <ratio>` | Mapped to wrapper's `--aspect`. Supported by Codex: `1:1` (default), `16:9`, `9:16`, `4:3`, `2.35:1`. |
| `--ref <files...>` | Mapped to wrapper's repeated `--ref`. Codex's `image_gen` accepts reference images for style/composition guidance. |
| `--n` | Must be `1`. `validateArgs` throws if `n > 1` because Codex `image_gen` returns a single image per call. |
| `--imageApiDialect` | Not applicable. Throws if set to a non-default value. |
| `--size`, `--imageSize`, `--quality` | Silently ignored — Codex picks pixel dimensions from the aspect ratio. |
| `--model`, `-m` | Logical label only. The wrapper does not forward a model selector to Codex; the underlying engine is whichever model Codex's `image_gen` currently uses. Default label: `codex-image-gen`. |

## Environment variables

| Variable | Effect |
|----------|--------|
| `BAOYU_CODEX_IMAGEGEN_BIN` | Override the wrapper path. Default: bundled `scripts/codex-imagegen/main.ts` resolved relative to this skill's installed location. Accepts a `.ts` file (spawned with `bun`) or a legacy `.sh`/binary (spawned directly). |
| `BAOYU_CODEX_IMAGEGEN_CACHE_DIR` | Enable the wrapper's idempotency cache. Disabled by default; set to e.g. `~/.cache/baoyu-codex-imagegen` for high-value reuse. |
| `BAOYU_CODEX_IMAGEGEN_TIMEOUT_MS` | Per-attempt `codex exec` timeout in ms. Default: `300000` (5 min). Raise for slow networks or large prompts. |
| `BAOYU_CODEX_IMAGEGEN_RETRIES` | Wrapper-side retry attempts on retryable errors. Default: `2` (3 total attempts). |
| `BAOYU_CODEX_IMAGEGEN_LOG_FILE` | Append a structured JSONL diagnostic log. Useful when triaging timeouts or `agent_refused` errors. |
| `BAOYU_IMAGE_GEN_CODEX_CLI_CONCURRENCY` | Batch-mode concurrency for the `codex-cli` provider. Default: `1` — Codex exec is a heavy single-process workflow; raising this rarely helps. |
| `BAOYU_IMAGE_GEN_CODEX_CLI_START_INTERVAL_MS` | Batch-mode minimum start-gap. Default: `2000` ms. |

## Error model

The wrapper emits a single JSON line on stdout. On failure:

```json
{"status":"error","path":"...","bytes":0,"error":"...","error_kind":"..."}
```

The provider re-throws each wrapper error as `Invalid codex-cli result (<error_kind>): <message>`. The `"Invalid "` prefix triggers `isRetryableGenerationError` to mark it **non-retryable** in baoyu-image-gen's outer retry loop — the wrapper has already retried internally per `BAOYU_CODEX_IMAGEGEN_RETRIES`, so re-spawning Codex from main.ts would only multiply latency without changing the outcome.

`error_kind` values to expect:

| Kind | Cause | Action |
|------|-------|--------|
| `codex_not_installed` | `codex` not on `PATH` or unreadable | `npm install -g @openai/codex`, then `codex login`. |
| `invalid_args` | Programmer error in the spawn invocation | Inspect provider source; usually a path-injection guard fired. |
| `prompt_file_missing` | Temp prompt file vanished mid-call | Retry once; check `$TMPDIR` permissions. |
| `spawn_failed` | OS / process-launch failure | Verify `bun` or `npx` is installed; check filesystem permissions. |
| `timeout` | `codex exec` exceeded `--timeout` | Raise `BAOYU_CODEX_IMAGEGEN_TIMEOUT_MS`; check network. |
| `no_image_gen_tool_use` | Codex agent answered without calling `image_gen` | Often transient — retry. If persistent, refine the prompt. |
| `output_missing` / `invalid_png` | Agent reported success but file is absent or not a valid PNG | Retry; check disk space. |
| `agent_refused` | Codex agent refused (policy or content) | Adjust the prompt; surface the refusal to the user. |
| `lock_busy` | Another `codex-imagegen` invocation holds the file lock | Wait or set a distinct `--cache-dir` per concurrent caller. |

## Trade-offs

- Slow: 5–10× direct OpenAI API latency (except cache hits).
- Subject to the same TOS as interactive `codex exec` use — programmatic invocation from baoyu-image-gen is the same usage class.
- Stateful: requires `codex login` to be live; an expired session manifests as `codex_not_installed` or `agent_refused`.

## See also

- `references/codex-oauth-vs-openai-api-key.md` — why Codex OAuth is not interchangeable with `OPENAI_API_KEY`.
- `references/codex-image2-fallback.md` — when to fall back to `codex-cli` from a failed `openai` provider call.
