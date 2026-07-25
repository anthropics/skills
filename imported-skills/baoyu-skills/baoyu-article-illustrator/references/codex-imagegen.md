# `codex-imagegen` Wrapper Invocation

Load this reference only when the [Image Generation Tools](../SKILL.md#image-generation-tools) rule has resolved to `codex-imagegen` — i.e., the current runtime exposes no native `imagegen` skill but `codex` CLI is on `PATH` with an active `codex login`.

## Preferred path: route through `baoyu-image-gen`

If the `baoyu-image-gen` skill is available in this runtime, **always** invoke through it rather than calling the wrapper directly. It handles retry/cache/batch/EXTEND.md preferences uniformly with every other provider.

```bash
${BUN_X} <baoyu-image-gen-base>/scripts/main.ts \
  --provider codex-cli \
  --image <ABSOLUTE_output> \
  --promptfiles <ABSOLUTE_prompts/NN-{type}-{slug}.md> \
  --ar <ratio> \
  [--ref <ABSOLUTE_file>]...
```

Resolve `<baoyu-image-gen-base>` the same way you resolve any sibling skill — through your runtime's skill registry (`Skill` tool, plugin marketplace, or `$HOME/.baoyu-skills/baoyu-image-gen/`).

## Fallback: spawn the wrapper directly

Only when `baoyu-image-gen` is NOT installed in the current runtime. Discover the wrapper's location at runtime — do NOT hard-code `../../packages/...` from this skill:

1. **Honor explicit override**: if `$BAOYU_CODEX_IMAGEGEN_BIN` is set and points to a real file, use that path. It may be `.ts` (spawn `bun <path>`) or `.sh`/binary (spawn directly).
2. **Search the plugin root**: walk up from this skill's directory looking for `packages/baoyu-codex-imagegen/src/main.ts`. If found, that is the wrapper. Spawn it with `bun`.
3. **Last resort**: tell the user that `codex-imagegen` is not available in this runtime and ask whether to install the `baoyu-skills` plugin (or set `BAOYU_CODEX_IMAGEGEN_BIN`) or pick another backend.

Once located, the invocation shape is:

```bash
bun <WRAPPER>/main.ts \
  --image <ABSOLUTE_output> \
  --prompt-file <ABSOLUTE_prompts/NN-{type}-{slug}.md> \
  --aspect <ratio> \
  [--ref <ABSOLUTE_file>]... \
  [--timeout <ms>] \
  [--cache-dir ~/.cache/baoyu-codex-imagegen] \
  [--log-file <ABSOLUTE_jsonl_log_path>]
```

If `bun` is missing, `npx -y bun <WRAPPER>/main.ts ...` works as a fallback.

## Parameter notes

- **All filesystem inputs** are auto-resolved against `process.cwd()` when relative, but agents should pass absolute paths to be robust against cwd drift.
- **`--timeout`** defaults to `300000` (5 min) per `codex exec` attempt. Raise (e.g. `--timeout 600000` for 10 min) on slow networks or large prompts.
- **`--cache-dir`** is off by default. Enable for repeatable runs to skip redundant generations of the same prompt+aspect+refs.
- **Authentication**: the wrapper uses the user's Codex subscription — no `OPENAI_API_KEY` is read or sent.

## Stdout contract

Single JSON line:

- Success: `{"status":"ok","path":"...","bytes":N,"elapsed_seconds":N,"thread_id":"...","attempts":N,"cached":bool,...}`
- Failure: `{"status":"error","path":"...","bytes":0,"error":"...","error_kind":"..."}`

`error_kind` values: `codex_not_installed`, `invalid_args`, `prompt_file_missing`, `spawn_failed`, `timeout`, `no_image_gen_tool_use`, `output_missing`, `invalid_png`, `agent_refused`, `lock_busy`.

On retryable errors (timeout, spawn_failed, no_image_gen_tool_use, output_missing, invalid_png, agent_refused), ask the user whether to retry or fall back to another backend.

## Batch semantics

- Codex `image_gen` returns **one image per call** (`n=1` only). Multi-image jobs must dispatch one wrapper call per image.
- The wrapper does NOT accept a `--sessionId` flag. Chain/scene consistency must come from `--ref` reference images.
- `--size` and `--quality` are silently ignored — Codex picks pixel dimensions from `--aspect`.
