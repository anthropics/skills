# Model Migration Guide

> **If you arrived via `/claude-api migrate`:** this is the right file. Execute the steps below in order — do not summarize them back to the user. Start with Step 0 (confirm scope) before touching any file.

How to move existing code to newer Claude models. Covers breaking changes, deprecated parameters, and drop-in replacements for retired models.

For the latest, authoritative version (with code samples in every supported language), WebFetch the **Migration Guide** URL from `shared/live-sources.md`. Use this file for the consolidated, skill-resident reference; fall back to the live docs whenever a model launch or breaking change may have shifted the picture.

**This file is large.** Use the section names below to jump (or `Grep` this file for the heading text). Read Step 0 and Step 1 first — they apply to every migration. Then read only the per-target section for the model you are migrating to.

| Section | When you need it |
|---|---|
| Step 0: Confirm the migration scope | Always — before any edits |
| Step 1: Classify each file | Always — decides whether to swap, add-alongside, or skip |
| Per-SDK Syntax Reference | Translate the Python examples in this guide to TypeScript / Go / Ruby / Java / C# / PHP |
| Destination Models / Retired Model Replacements | Picking a target model |
| Breaking Changes by Source Model | Migrating to Opus 4.6 / Sonnet 4.6 |
| Migrating to Opus 4.7 | Migrating to Opus 4.7 (breaking changes, silent defaults, behavioral shifts) |
| Opus 4.7 Migration Checklist | The required vs optional items for 4.7, tagged `[BLOCKS]` / `[TUNE]` |
| Migrating to Opus 4.8 | Migrating to Opus 4.8 (no new breaking changes; mid-session system prompts; behavioral re-tuning) |
| Opus 4.8 Migration Checklist | The required vs optional items for 4.8, tagged `[BLOCKS]` / `[TUNE]` |
| Migrating to Claude Sonnet 5 | Migrating Sonnet 4.6 → Claude Sonnet 5 (adaptive thinking on by default; non-default sampling params 400; new tokenizer; `xhigh` effort for coding/agentic; high-res vision; behavioral re-tuning) |
| Claude Sonnet 5 Migration Checklist | The required vs optional items, tagged `[BLOCKS]` / `[TUNE]` |
| Migrating to Claude Fable 5 | Migrating to Claude Fable 5 or Claude Mythos 5 (always-on thinking, raw chain of thought never returned, refusal handling, data retention, behavioral shifts + prompting guidance) |
| Claude Fable 5 Migration Checklist | The required vs optional items for Claude Fable 5, tagged `[BLOCKS]` / `[TUNE]` |
| Verify the Migration | After edits — runtime spot-check |

**TL;DR:** Change the model ID string. If you were using `budget_tokens`, switch to `thinking: {type: "adaptive"}`. If you were using assistant prefills, they 400 on both Opus 4.6 and Sonnet 4.6 — switch to one of the prefill replacements (most often `output_config.format`; see the table in Breaking Changes by Source Model). If you're moving from Sonnet 4.5 to Sonnet 4.6, set `effort` explicitly — 4.6 defaults to `high`. Remove the `effort-2025-11-24` and `fine-grained-tool-streaming-2025-05-14` beta headers (GA on 4.6); remove `interleaved-thinking-2025-05-14` once you're on adaptive thinking (keep it only while using the transitional `budget_tokens` escape hatch). Then drop back from `client.beta.messages.create` to `client.messages.create`. Dial back any aggressive "CRITICAL: YOU MUST" tool instructions; 4.6 follows the system prompt much more closely.

---

## Step 0: Confirm the migration scope

**Before any Write, Edit, or MultiEdit call, confirm the scope.** If the user's request does not explicitly name a single file, a specific directory, or an explicit file list, **ask first — do not start editing**. This is non-negotiable: even imperative-sounding requests like "migrate my codebase", "move my project to X", "upgrade to Sonnet 4.6", or bare "migrate to Opus 4.7" leave the scope ambiguous and require a clarifying question. Phrases like "my project", "my code", "my codebase", "the whole thing", "everywhere", or "across the repo" are **ambiguous, not directive** — they tell you *what* to do but not *where*. Ask before doing.

Offer the common scopes explicitly and wait for the answer before touching any file:

1. The entire working directory
2. A specific subdirectory (e.g. `src/`, `app/`, `services/billing/`)
3. A specific file or a list of files

Surface this as a single clarifying question so the user can answer in one turn. **Proceed without asking only when the scope is already unambiguous** — the user named an exact file ("migrate `extract.py` to Sonnet 4.6"), pointed at a specific directory ("migrate everything under `services/billing/` to Opus 4.6"), listed specific files ("update `a.py` and `b.py`"), or already answered the scope question in an earlier turn. If you can answer the question "which files is this change going to touch?" with a precise list from the prompt alone, proceed. If not, ask.

**Worked example.** If the user says *"Move my project to Opus 4.6. I want adaptive thinking everywhere it makes sense."* you do not know whether "my project" means the whole working directory, just `src/`, just the production code, or something else — the `everywhere` makes the intent clear (update every call site *within scope*) but the scope itself is still not defined. Do not start editing. Respond with:

> Before I start editing, can you confirm the scope? I can migrate:
> 1. Every `.py` file in the working directory
> 2. Just the files under `src/` (production code)
> 3. A specific subdirectory or list of files you name
>
> Which one?

Then wait for the answer. The same applies to *"Migrate to Opus 4.7"* and bare *"Help me upgrade to Sonnet 4.6"* — ask before editing.

**Sizing the scope question (large repos).** Before asking, get a per-directory count so the user can pick concretely:

```sh
rg -l "<old-model-id>" --type-not md | cut -d/ -f1 | sort | uniq -c | sort -rn
```

Present the breakdown in your scope question (e.g. *"Found 217 references across 3 directories: api/ (130), api-go/ (62), routing/ (25). Which to migrate?"*). Also confirm `git status` is clean before surveying — unexpected modifications mean a concurrent process; stop and investigate before proceeding.

---

## Step 1: Classify each file

Not every file that contains the old model ID is a **caller** of the API. Before editing, classify each file into one of these buckets — the right action differs:

| # | Bucket | What it looks like | Action |
|---|---|---|---|
| 1 | **Calls the API/SDK** | `client.messages.create(model=…)`, `anthropic.Anthropic()`, request payloads | Swap the model ID **and** apply the breaking-change checklist for the target version (below). |
| 2 | **Defines or serves the model** | Model registries, OpenAPI specs, routing/queue configs, model-policy enums, generated catalogs | The old entry **stays** (the model is still served). Ask whether to (a) add the new model alongside, (b) leave alone, or (c) retire the old model — never blind-replace. **If you can't ask, default to (a): add the new model alongside and flag it** — replacing would de-register a model that's still in production. |
| 3 | **References the ID as an opaque string** | UI fallback constants, capability-gate substring checks, generic test fixtures, label parsers, env defaults | Usually swap the string and verify any parser/regex/substring match handles the new ID — but check the sub-cases below first. |
| 4 | **Suffixed variant ID** | `claude-<model>-<suffix>` like `-fast`, `-1024k`, `-200k`, `[1m]`, dated snapshots | These are deployment/routing identifiers, not the public model ID. **Do not assume a new-model equivalent exists.** Verify in the registry first; if absent, leave the string alone and flag it. **Exception: `-fast` strings (e.g. `claude-opus-4-6-fast`) are handled by the Fast Mode section below**, which rewrites them to Opus 4.8 plus `speed="fast"` and the `fast-mode-2026-02-01` beta rather than leaving them in place. |

**Bucket 3 sub-cases — before swapping a string reference, check:**

- **Capability gate** (e.g. `if 'opus-4-6' in model_id:` enables a feature) → **add the new ID alongside**, don't replace. The old model is still served and still has the capability, so replacing would silently disable the feature for any old-model traffic that still flows through. If you know no old-model traffic will hit this gate (single-caller codebase fully migrating), replacing is fine; if unsure, add alongside.
- **Registry-assert test** (e.g. `assert "claude-X" in supported_models`, `test_X_has_N_clusters`) → **add an assertion for the new model alongside; keep the old one.** The old model is still served, so its assertion stays valid — but the registry should also include the new model, so assert that too. Heuristic: if the test references multiple model versions in a list, it's a registry test; if one model in a struct compared only to itself, it's a generic fixture.
- **Frozen / generated snapshot** → **regenerate**, don't hand-edit.
- **Coupled to a definer** (e.g. an integration test that passes model authorization via a shared `conftest` seed list, or asserts on a billing-tier / rate-limit-group enum or a generated SKU/pricing catalog) → **verify the definer has a new-model entry first.** If not, add a seed entry (reusing the nearest existing tier as a placeholder); if you can't confidently do that, ask the user how to populate the definer. **Do not skip the test.** Swapping without populating the definer will make the test fail at runtime.

When migrating tests specifically: breaking parameters (`temperature`, `top_p`, `budget_tokens`) are usually absent — test fixtures rarely set sampling params on placeholder models. The breaking-change scan is still required, but expect mostly clean results.

**Find intentionally-flagged sync points first.** Many codebases tag spots that must change at every model launch with comment markers like `MODEL LAUNCH`, `KEEP IN SYNC`, `@model-update`, or similar. Grep for whatever convention the repo uses *before* the broad model-ID grep — those markers point at the load-bearing changes.

---

## Per-SDK Syntax Reference

Code examples in this guide are Python. **The same fields exist in every official Anthropic SDK** — Stainless generates all 7 from the same OpenAPI spec, so JSON field names map 1:1 with only case-convention differences. Use the rows below to translate the Python examples to the SDK you are migrating.

> **Verify type and method names against the SDK source before writing them into customer code.** WebFetch the relevant repository from the SDK source-code table in `shared/live-sources.md` (one row per SDK) and confirm the exact symbol — particularly for typed SDKs (Go, Java, C#) where union/builder names can differ from the JSON shape. Do not guess type names that aren't in the table below or in `<lang>/claude-api/README.md`.

<!-- The rows below were verified against each SDK's `synced/model-launch-april` branch. -->

### `thinking` — `budget_tokens` → adaptive

| SDK | Before | After |
|---|---|---|
| Python | `thinking={"type": "enabled", "budget_tokens": N}` | `thinking={"type": "adaptive"}` |
| TypeScript | `thinking: { type: 'enabled', budget_tokens: N }` | `thinking: { type: 'adaptive' }` |
| Go | `Thinking: anthropic.ThinkingConfigParamOfEnabled(N)` | `Thinking: anthropic.ThinkingConfigParamUnion{OfAdaptive: &anthropic.ThinkingConfigAdaptiveParam{}}` |
| Ruby | `thinking: { type: "enabled", budget_tokens: N }` | `thinking: { type: "adaptive" }` |
| Java | `.thinking(ThinkingConfigEnabled.builder().budgetTokens(N).build())` | `.thinking(ThinkingConfigAdaptive.builder().build())` |
| C# | `Thinking = new ThinkingConfigEnabled { BudgetTokens = N }` | `Thinking = new ThinkingConfigAdaptive()` |
| PHP | `thinking: ['type' => 'enabled', 'budget_tokens' => N]` | `thinking: ['type' => 'adaptive']` |

### Sampling parameters — `temperature` / `top_p` / `top_k`

(Remove the field entirely on Opus 4.7; on Claude 4.x keep at most one of `temperature` or `top_p`.)

| SDK | Field(s) to remove |
|---|---|
| Python | `temperature=…`, `top_p=…`, `top_k=…` |
| TypeScript | `temperature: …`, `top_p: …`, `top_k: …` |
| Go | `Temperature: anthropic.Float(…)`, `TopP: anthropic.Float(…)`, `TopK: anthropic.Int(…)` |
| Ruby | `temperature: …`, `top_p: …`, `top_k: …` |
| Java | `.temperature(…)`, `.topP(…)`, `.topK(…)` |
| C# | `Temperature = …`, `TopP = …`, `TopK = …` |
| PHP | `temperature: …`, `topP: …`, `topK: …` |

### Prefill replacement — structured outputs via `output_config.format`

| SDK | Remove (last assistant turn) | Add |
|---|---|---|
| Python | `{"role": "assistant", "content": "…"}` | `output_config={"format": {"type": "json_schema", "schema": SCHEMA}}` |
| TypeScript | `{ role: 'assistant', content: '…' }` | `output_config: { format: { type: 'json_schema', schema: SCHEMA } }` |
| Go | trailing `anthropic.MessageParam{Role: "assistant", …}` | `OutputConfig: anthropic.OutputConfigParam{Format: anthropic.JSONOutputFormatParam{…}}` |
| Ruby | `{ role: "assistant", content: "…" }` | `output_config: { format: { type: "json_schema", schema: SCHEMA } }` |
| Java | trailing `Message.builder().role(ASSISTANT)…` | `.outputConfig(OutputConfig.builder().format(JsonOutputFormat.builder()…build()).build())` |
| C# | trailing `new Message { Role = "assistant", … }` | `OutputConfig = new OutputConfig { Format = new JsonOutputFormat { … } }` |
| PHP | trailing `['role' => 'assistant', 'content' => '…']` | `outputConfig: ['format' => ['type' => 'json_schema', 'schema' => $SCHEMA]]` |

### `thinking.display` — opt back into summarized reasoning (Opus 4.7)

| SDK | Add |
|---|---|
| Python | `thinking={"type": "adaptive", "display": "summarized"}` |
| TypeScript | `thinking: { type: 'adaptive', display: 'summarized' }` |
| Go | `Thinking: anthropic.ThinkingConfigParamUnion{OfAdaptive: &anthropic.ThinkingConfigAdaptiveParam{Display: anthropic.ThinkingConfigAdaptiveDisplaySummarized}}` |
| Ruby | `thinking: { type: "adaptive", display: "summarized" }` (or `display_:` when constructing the model class directly) |
| Java | `.thinking(ThinkingConfigAdaptive.builder().display(ThinkingConfigAdaptive.Display.SUMMARIZED).build())` |
| C# | `Thinking = new ThinkingConfigAdaptive { Display = Display.Summarized }` |
| PHP | `thinking: ['type' => 'adaptive', 'display' => 'summarized']` |

For any field not in these tables, the JSON key in the Python example translates directly: `snake_case` for Python/TypeScript/Ruby, `camelCase` named args for PHP, `PascalCase` struct fields for Go/C#, `camelCase` builder methods for Java.

---

## Explain every change you make

Migration edits often look arbitrary to a user who hasn't read the release notes — a removed `temperature`, a deleted prefill, a rewritten system-prompt sentence. **For each edit, tell the user what you changed and why**, tied to the specific API or behavioral change that motivates it. Do this in your summary as you work, not just at the end.

Be especially explicit about **system-prompt edits**. Users are rightly protective of their prompts, and prompt-tuning changes are judgment calls (not hard API requirements). For any prompt edit:

- Quote the before and after text.
- State the behavioral shift that motivates it (e.g. *"Opus 4.7 calibrates response length to task complexity, so I added an explicit length instruction"*, or *"4.6 follows instructions more literally, so 'CRITICAL: YOU MUST use the search tool' will now overtrigger — softened to 'Use the search tool when…'"*).
- Make clear which prompt edits are **optional tuning** (tone, length, subagent guidance) versus which code edits are **required to avoid a 400** (sampling params, `budget_tokens`, prefills). Never present an optional prompt change as mandatory.

If you're applying several prompt-tuning edits at once, offer them as a short list the user can accept or decline item-by-item rather than silently rewriting their system prompt.

---

## Before You Migrate

1. **Confirm the target model ID.** Use only the exact strings from `shared/models.md` — do not append date suffixes to aliases (`claude-opus-4-6`, not `claude-opus-4-6-20251101`). Guessing an ID will 404.
2. **Check which features your code uses** with this checklist:
   - `thinking: {type: "enabled", budget_tokens: N}` → migrate to adaptive thinking on Opus 4.6 / Sonnet 4.6 (still functional but deprecated)
   - Assistant-turn prefills (`messages` ending with `role: "assistant"`) → must change on Opus 4.6 / Sonnet 4.6 (returns 400)
   - `output_format` parameter on `messages.create()` → must change on all models (deprecated API-wide)
   - `max_tokens > ~16000` → must stream on any model (above ~16K risks SDK HTTP timeouts). When streaming, every current model reaches 128K except Haiku 4.5, which caps at 64K
   - Beta headers `effort-2025-11-24`, `fine-grained-tool-streaming-2025-05-14`, `interleaved-thinking-2025-05-14` → GA on 4.6, remove them and switch from `client.beta.messages.create` to `client.messages.create`
   - Moving Sonnet 4.5 → Sonnet 4.6 with no `effort` set → 4.6 defaults to `high`, which may change your latency/cost profile
   - System prompts with `CRITICAL`, `MUST`, `If in doubt, use X` language → likely to overtrigger on 4.6 (see Prompt-Behavior Changes)
   - Coming from 3.x / 4.0 / 4.1: also check sampling params (`temperature` + `top_p`), tool versions (`text_editor_20250728`), `refusal` + `model_context_window_exceeded` stop reasons, trailing-newline tool-param handling
3. **Test on a single request first.** Run one call against the new model, inspect the response, then roll out.

---

## Destination Models (recommended targets)

| If you're on…                         | Migrate to         | Why                                               |
| ------------------------------------- | ------------------ | ------------------------------------------------- |
| Claude Mythos Preview (`claude-mythos-preview`) | `claude-mythos-5` (Project Glasswing successor) or `claude-fable-5` (GA) | Same tokenizer family — mostly a model-ID swap; remove `thinking` config and prefill; see Migrating to Claude Fable 5 |
| Opus 4.7                              | `claude-opus-4-8`  | Most capable Opus-tier model; same API surface as 4.7 (no new breaking changes) — mostly prompt re-tuning; see Migrating to Opus 4.8 |
| Opus 4.6                              | `claude-opus-4-8`  | Apply the Opus 4.7 breaking changes, then the 4.8 re-tuning |
| Opus 4.0 / 4.1 / 4.5 / Opus 3         | `claude-opus-4-8`  | Apply 4.6 → 4.7 → 4.8 in order (adaptive thinking, drop sampling params, then re-tune) |
| Sonnet 4.6                            | `claude-sonnet-5` | Near-Opus quality on agentic and coding work at Sonnet cost; adaptive thinking on by default; see Migrating to Claude Sonnet 5 |
| Sonnet 4.0 / 4.5 / 3.7 / 3.5          | `claude-sonnet-5` | Apply the Sonnet 4.6 changes first, then the Claude Sonnet 5 section |
| Haiku 3 / 3.5                         | `claude-haiku-4-5` | Fastest and most cost-effective                   |

Default to the latest Opus for the caller's tier unless they explicitly chose otherwise. The Opus migrations layer: if you're on Opus 4.6 or older, apply each version's section in order up to your target (e.g. 4.5 → 4.8 means the 4.6, 4.7, and 4.8 sections in sequence). A 4.7 → 4.8 move has no new breaking changes — see Migrating to Opus 4.8 below.

---

## Retired Model Replacements

These models return 404 — update immediately:

| Retired model                 | Retired       | Drop-in replacement  |
| ----------------------------- | ------------- | -------------------- |
| `claude-3-7-sonnet-20250219`  | Feb 19, 2026  | `claude-sonnet-5` |
| `claude-3-5-haiku-20241022`   | Feb 19, 2026  | `claude-haiku-4-5`   |
| `claude-3-opus-20240229`      | Jan 5, 2026   | `claude-opus-4-8`    |
| `claude-3-5-sonnet-20241022`  | Oct 28, 2025  | `claude-sonnet-5` |
| `claude-3-5-sonnet-20240620`  | Oct 28, 2025  | `claude-sonnet-5` |
| `claude-3-sonnet-20240229`    | Jul 21, 2025  | `claude-sonnet-5` |
| `claude-2.1`, `claude-2.0`    | Jul 21, 2025  | `claude-sonnet-5` |

## Deprecated Models (retiring soon)

| Model                         | Retires       | Replacement          |
| ----------------------------- | ------------- | -------------------- |
| `claude-3-haiku-20240307`     | Apr 19, 2026  | `claude-haiku-4-5`   |
| `claude-opus-4-20250514`      | June 15, 2026 | `claude-opus-4-8`    |
| `claude-sonnet-4-20250514`    | June 15, 2026 | `claude-sonnet-5` |

---

## Breaking Changes by Source Model

### Migrating from Sonnet 4.5 to Sonnet 4.6 (effort default change)

Sonnet 4.5 had no `effort` parameter; Sonnet 4.6 defaults to `high`. If you just switch the model string and do nothing else, you may see noticeably higher latency and token usage. Set `effort` explicitly.

**Recommended starting points:**

| Workload                                          | Start at       | Notes                                                                                                    |
| ------------------------------------------------- | -------------- | -------------------------------------------------------------------------------------------------------- |
| Chat, classification, content generation          | `low`          | With `thinking: {"type": "disabled"}` you'll see similar or better performance vs. Sonnet 4.5 no-thinking |
| Most applications (balanced)                      | `medium`       | The default sweet spot for quality vs. cost                                                              |
| Agentic coding, tool-heavy workflows              | `medium`       | Pair with adaptive thinking and a generous `max_tokens` (up to 128K with streaming — Sonnet 4.6's ceiling) |
| Autonomous multi-step agents, long-horizon loops  | `high`         | Scale down to `medium` if latency/tokens become a concern                                                 |
| Computer-use agents                               | `high` + adaptive | Sonnet 4.6's best computer-use accuracy is on adaptive + high                                          |

For non-thinking chat workloads specifically:

```python
client.messages.create(
    model="claude-sonnet-4-6",
    max_tokens=8192,
    thinking={"type": "disabled"},
    output_config={"effort": "low"},
    messages=[{"role": "user", "content": "..."}],
)
```

**When to use Opus 4.6 instead:** hardest and longest-horizon problems — large code migrations, deep research, extended autonomous work. Sonnet 4.6 wins on fast turnaround and cost efficiency.

### Migrating to Opus 4.6 / Sonnet 4.6 (from any older model)

**1. Manual extended thinking is deprecated — use adaptive thinking.**

`thinking: {type: "enabled", budget_tokens: N}` (manual extended thinking with a fixed token budget) is deprecated on Opus 4.6 and Sonnet 4.6. Replace it with `thinking: {type: "adaptive"}`, which lets Claude decide when and how much to think. Adaptive thinking also enables interleaved thinking automatically (no beta header needed).

```python
# Old (still works on older models, deprecated on 4.6)
response = client.messages.create(
    model="claude-sonnet-4-5",
    max_tokens=16000,
    thinking={"type": "enabled", "budget_tokens": 8000},
    messages=[...]
)

# New (Opus 4.6 / Sonnet 4.6)
response = client.messages.create(
    model="claude-opus-4-6",  # or "claude-sonnet-4-6"
    max_tokens=16000,
    thinking={"type": "adaptive"},
    output_config={"effort": "high"},  # optional: low | medium | high | max
    messages=[...]
)
```

Adaptive thinking is the long-term target, and on internal evaluations it outperforms manual extended thinking. Move when you can.

**Transitional escape hatch:** manual extended thinking is still *functional* on Opus 4.6 and Sonnet 4.6 (deprecated, will be removed in a future release). If you need a hard ceiling while migrating — for example, to bound token spend on a runaway workload before you've tuned `effort` — you can keep `budget_tokens` around alongside an explicit `effort` value, then remove it in a follow-up. `budget_tokens` must be strictly less than `max_tokens`:

```python
# Transitional only — deprecated, plan to remove
client.messages.create(
    model="claude-sonnet-4-6",
    max_tokens=16384,
    thinking={"type": "enabled", "budget_tokens": 8192},  # must be < max_tokens
    output_config={"effort": "medium"},
    messages=[...],
)
```

If the user asks for a "thinking budget" on 4.6, the preferred answer is `effort` — use `low`, `medium`, `high`, or `max` rather than a token count.

**2. Effort parameter (Opus 4.5, Opus 4.6, Sonnet 4.6 only).**

Controls thinking depth and overall token spend. Goes inside `output_config`, not top-level. Default is `high`. `max` is supported on Fable 5, Opus 4.6 and later, Sonnet 5, and Sonnet 4.6 — it errors on Sonnet 4.5 and Haiku 4.5.

```python
output_config={"effort": "medium"}  # often the best cost / quality balance
```

### Migrating to the 4.6 family (Opus 4.6 and Sonnet 4.6)

**3. Assistant-turn prefills return 400 (Opus 4.6 and Sonnet 4.6).**

Prefilled responses on the final assistant turn are no longer supported on either Opus 4.6 or Sonnet 4.6 — both return a 400. Adding assistant messages *elsewhere* in the conversation (e.g., for few-shot examples) still works. Pick the replacement that matches what the prefill was doing:

| Prefill was used for                               | Replacement                                                                                                                               |
| -------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------- |
| Forcing JSON / YAML / schema output                | `output_config.format` with a `json_schema` — see example below                                                                           |
| Forcing a classification label                     | Tool with an enum field containing valid labels, or structured outputs                                                                    |
| Skipping preambles (`Here is the summary:\n`)      | System prompt instruction: *"Respond directly without preamble. Do not start with phrases like 'Here is...' or 'Based on...'."*           |
| Steering around bad refusals                       | Usually no longer needed — 4.6 refuses far more appropriately. Plain user-turn prompting is sufficient.                                   |
| Continuing an interrupted response                 | Move continuation into the user turn: *"Your previous response was interrupted and ended with `[last text]`. Continue from there."*     |
| Injecting reminders / context hydration            | Inject into the user turn instead. For complex agent harnesses, expose context via a tool call or during compaction.                      |

```python
# Old (fails on Opus 4.6 / Sonnet 4.6) — prefill forcing JSON shape
messages=[
    {"role": "user", "content": "Extract the name."},
    {"role": "assistant", "content": "{\"name\": \""},
]

# New — structured outputs replace the prefill
response = client.messages.create(
    model="claude-opus-4-6",
    max_tokens=1024,
    output_config={"format": {"type": "json_schema", "schema": {...}}},
    messages=[{"role": "user", "content": "Extract the name."}],
)
```

**4. Stream for `max_tokens > ~16K` (all models); only Haiku 4.5 caps lower, at 64K.**

Non-streaming requests hit SDK HTTP timeouts at high `max_tokens`, regardless of model — stream for anything above ~16K output. The streamable ceiling is 128K for every current model except Haiku 4.5, which caps at 64K.

```python
with client.messages.stream(model="claude-opus-4-6", max_tokens=64000, ...) as stream:
    message = stream.get_final_message()
```

**5. Tool-call JSON escaping may differ (Opus 4.6 and Sonnet 4.6).**

Both 4.6 models can produce tool call `input` fields with Unicode or forward-slash escaping. Always parse with `json.loads()` / `JSON.parse()` — never raw-string-match the serialized input.

### All models

**6. `output_format` → `output_config.format` (API-wide).**

The old top-level `output_format` parameter on `messages.create()` is deprecated. Use `output_config.format` instead. This is not 4.6-specific — applies to every model.

---

## Beta Headers to Remove on 4.6

Several beta headers that were required on 4.5 are now GA on 4.6 and should be removed. Leaving them in is harmless but misleading; removing them also lets you move from `client.beta.messages.create(...)` back to `client.messages.create(...)`.

| Header                                    | Status on 4.6                                              | Action                                                  |
| ----------------------------------------- | ---------------------------------------------------------- | ------------------------------------------------------- |
| `effort-2025-11-24`                       | Effort parameter is GA                                     | Remove                                                  |
| `fine-grained-tool-streaming-2025-05-14`  | GA                                                         | Remove                                                  |
| `interleaved-thinking-2025-05-14`         | Adaptive thinking enables interleaved thinking automatically | Remove when using adaptive thinking; still functional on Sonnet 4.6 *with* manual extended thinking, but that path is deprecated |
| `token-efficient-tools-2025-02-19`        | Built in to all Claude 4+ models                           | Remove (no effect)                                      |
| `output-128k-2025-02-19`                  | Built in to Claude 4+ models                               | Remove (no effect)                                      |

Once you remove all of these and finish moving to adaptive thinking, you can switch the SDK call site from the beta namespace back to the regular one:

```python
# Before
response = client.beta.messages.create(
    model="claude-opus-4-5",
    betas=["interleaved-thinking-2025-05-14", "effort-2025-11-24"],
    ...
)

# After
response = client.messages.create(
    model="claude-opus-4-6",
    thinking={"type": "adaptive"},
    output_config={"effort": "high"},
    ...
)
```

---

## Additional Changes When Coming from 3.x / 4.0 / 4.1 → 4.6

If you're jumping from Opus 4.1, Sonnet 4, Sonnet 3.7, or an older Claude 3.x model directly to 4.6, apply everything above *plus* the items in this section. Users already on Opus 4.5 / Sonnet 4.5 can skip this.

**1. Sampling parameters: `temperature` OR `top_p`, not both.**

Passing both will error on every Claude 4+ model:

```python
# Old (3.x only — errors on 4+)
client.messages.create(temperature=0.7, top_p=0.9, ...)

# New
client.messages.create(temperature=0.7, ...)  # or top_p, not both
```

**2. Update tool versions.**

Legacy tool versions are not supported on 4+. **Both the `type` and the `name` field change** — `text_editor_20250728` and `str_replace_based_edit_tool` are a pair; updating one without the other 400s. Also remove the `undo_edit` command from your text-editor integration:

| Old                                               | New                                                     |
| ------------------------------------------------- | ------------------------------------------------------- |
| `text_editor_20250124` + `str_replace_editor`     | `text_editor_20250728` + `str_replace_based_edit_tool`  |
| `code_execution_*` (earlier versions)             | `code_execution_20260521`                               |
| `undo_edit` command                               | *(no longer supported — delete call sites)*             |

```python
# Before
tools = [{"type": "text_editor_20250124", "name": "str_replace_editor"}]

# After — BOTH fields change
tools = [{"type": "text_editor_20250728", "name": "str_replace_based_edit_tool"}]
```

**3. Handle the `refusal` stop reason.**

Claude 4+ can return `stop_reason: "refusal"` on the response. If your code only handles `end_turn` / `tool_use` / `max_tokens`, add a branch:

```python
if response.stop_reason == "refusal":
    # Surface the refusal to the user; do not retry with the same prompt
    ...
```

**4. Handle the `model_context_window_exceeded` stop reason (4.5+).**

Distinct from `max_tokens`: it means the model hit the *context window* limit, not the requested output cap. Handle both:

```python
if response.stop_reason == "model_context_window_exceeded":
    # Context window exhausted — compact or split the conversation
    ...
elif response.stop_reason == "max_tokens":
    # Requested output cap hit — retry with higher max_tokens or stream
    ...
```

**5. Trailing newlines preserved in tool call string parameters (4.5+).**

4.5 and 4.6 preserve trailing newlines that older models stripped. If your tool implementations do exact string matching against tool-call `input` values (e.g., `if name == "foo"`), verify they still match when the model sends `"foo\n"`. Normalizing with `.rstrip()` on the receiving side is usually the simplest fix.

**6. Haiku: rate limits reset between generations.**

Haiku 4.5 has its own rate-limit pool separate from Haiku 3 / 3.5. If you're ramping traffic as you migrate, check your tier's Haiku 4.5 limits at [API rate limits](https://platform.claude.com/docs/en/api/rate-limits) — a quota that comfortably served Haiku 3.5 traffic may need a tier bump for the same volume on 4.5.

---

## Prompt-Behavior Changes (Opus 4.5 / 4.6, Sonnet 4.6)

These don't break your code, but prompts that worked on 4.5-and-earlier may over- or under-trigger on 4.6. Tune as needed.

**1. Aggressive instructions cause overtriggering.** Opus 4.5 and 4.6 follow the system prompt much more closely than earlier models. Prompts written to *overcome* the old reluctance are now too aggressive:

| Before (worked on 4.0 / 4.5)                | After (use on 4.6)                        |
| ------------------------------------------- | ----------------------------------------- |
| `CRITICAL: You MUST use this tool when...`  | `Use this tool when...`                   |
| `Default to using [tool]`                   | `Use [tool] when it would improve X`      |
| `If in doubt, use [tool]`                   | *(delete — no longer needed)*             |

If the model is now overtriggering a tool or skill, the fix is almost always to dial back the language, not to add more guardrails.

**2. Overthinking and excessive exploration (Opus 4.6).** At higher `effort` settings, Opus 4.6 explores more before answering. If that burns too many thinking tokens, lower `effort` first (`medium` is often the sweet spot) before adding prose instructions to constrain reasoning.

**3. Overeager subagent spawning (Opus 4.6).** Opus 4.6 has a strong preference for delegating to subagents. If you see it spawning a subagent for something a direct `grep` or `read` would solve, add guidance: *"Use subagents only for parallel or independent workstreams. For single-file reads or sequential operations, work directly."*

**4. Overengineering (Opus 4.5 / 4.6).** Both models may add extra files, abstractions, or defensive error handling beyond what was asked. If you want minimal changes, prompt for it explicitly: *"Only make changes directly requested. Don't add helpers, abstractions, or error handling for scenarios that can't happen."*

**5. LaTeX math output (Opus 4.6).** Opus 4.6 defaults to LaTeX (`\frac{}{}`, `$...$`) for math and technical content. If you need plain text, instruct it explicitly: *"Format all math as plain text — no LaTeX, no `$`, no `\frac{}{}`. Use `/` for division and `^` for exponents."*

**6. Skipped verbal summaries (4.6 family).** The 4.6 models are more concise and may skip the summary paragraph after a tool call, jumping straight to the next action. If you rely on those summaries for visibility, add: *"After completing a task that involves tool use, provide a brief summary of what you did."*

**7. "Think" as a trigger word (Opus 4.5 with thinking disabled).** When `thinking` is off, Opus 4.5 is particularly sensitive to the word *think* and may reason more than you want. Use `consider`, `evaluate`, or `reason through` instead.

---

## Model-ID Rename Quick Reference

| Old string (migration source)  | New string         |
| ------------------------------ | ------------------ |
| `claude-opus-4-7`              | `claude-opus-4-8`  |
| `claude-opus-4-6`              | `claude-opus-4-8`  |
| `claude-opus-4-5`              | `claude-opus-4-8`  |
| `claude-opus-4-1`              | `claude-opus-4-8`  |
| `claude-opus-4-0`              | `claude-opus-4-8`  |
| `claude-mythos-preview`        | `claude-mythos-5` (Project Glasswing) or `claude-fable-5` |
| `claude-sonnet-4-6`            | `claude-sonnet-5`|
| `claude-sonnet-4-5`            | `claude-sonnet-5`|
| `claude-sonnet-4-0`            | `claude-sonnet-5`|

Older aliases (`claude-opus-4-7`, `claude-opus-4-6`, `claude-opus-4-5`, `claude-sonnet-4-6`, `claude-sonnet-4-5`, etc.) are still active and can be pinned if you need time before upgrading — see `shared/models.md` for the full legacy list.

### Amazon Bedrock model IDs

If the code uses the `AnthropicBedrockMantle` client (Python `anthropic[bedrock]`, TypeScript `@anthropic-ai/bedrock-sdk`, Java `BedrockMantleBackend`, Go `bedrock.NewMantleClient`, etc.) or targets `https://bedrock-mantle.{region}.api.aws/anthropic`, it is running on **Claude in Amazon Bedrock**. All breaking changes in this guide apply unchanged there — it serves the same Messages API shape — but model IDs carry an `anthropic.` provider prefix:

| First-party ID | Bedrock ID |
|---|---|
| `claude-opus-4-8` | `anthropic.claude-opus-4-8` |
| `claude-opus-4-7` | `anthropic.claude-opus-4-7` |
| `claude-sonnet-5` | `anthropic.claude-sonnet-5` |
| `claude-haiku-4-5` | `anthropic.claude-haiku-4-5` |

When migrating a Bedrock file, apply the same rename-table row as first-party, then keep/add the `anthropic.` prefix. Do **not** generate a first-party `claude-*` ID for a Bedrock client — it will 400.

**Skip for Bedrock:** the `code_execution_*` tool-version checklist item and the **Task Budgets** section — neither is available on Bedrock (see `shared/platform-availability.md` for the per-feature table). Everything else in this guide — `effort`, adaptive/extended thinking, `output_config.format`, `thinking.display`, fine-grained tool streaming, token counting — is available on Bedrock.

> **Out of scope:** the legacy Amazon Bedrock integration (`InvokeModel` / `Converse` APIs with ARN-versioned IDs like `anthropic.claude-3-5-sonnet-20241022-v2:0`) uses a different request shape and model-ID format. This guide does not cover it; WebFetch the Bedrock page in `shared/live-sources.md` if the user is migrating between the two Bedrock integrations.

### Claude Platform on AWS

If the code uses `AnthropicAWS` / `AnthropicAws` / `anthropicaws.NewClient` / `AnthropicAwsClient` (or targets `https://aws-external-anthropic.{region}.api.aws`), it is running on **Claude Platform on AWS** — Anthropic-operated, same-day API parity. Model IDs are **bare first-party** strings; apply the rename table above **verbatim** and every breaking-change section in this guide unchanged. There is nothing to skip. Do **not** add an `anthropic.` prefix (that's Amazon Bedrock, a separate offering). See `shared/claude-platform-on-aws.md` for client/auth details.

---

## Migration Checklist

Every item is tagged: **`[BLOCKS]`** items cause a 400 error, infinite loop, silent timeout, or wrong tool selection if missed — apply these as code edits, not as suggestions. **`[TUNE]`** items are quality/cost adjustments.

For each file that calls `messages.create()` / equivalent SDK method:

- [ ] **[BLOCKS]** Update the `model=` string to the new alias
- [ ] **[BLOCKS]** Replace `budget_tokens` with `thinking={"type": "adaptive"}` (deprecated on Opus 4.6 / Sonnet 4.6)
- [ ] **[BLOCKS]** Move `format` from top-level `output_format` into `output_config.format`
- [ ] **[BLOCKS]** Remove any assistant-turn prefills if targeting Opus 4.6 or Sonnet 4.6 (see the prefill replacement table)
- [ ] **[BLOCKS]** Switch to streaming if `max_tokens > ~16000` (otherwise SDK HTTP timeout)
- [ ] **[TUNE]** Verify tool-input handling parses JSON rather than raw-string-matching the serialized input (4.6 may escape Unicode / forward slashes differently; most SDKs already expose `block.input` as a parsed object)
- [ ] **[TUNE]** Set `output_config={"effort": "..."}` explicitly — especially when moving Sonnet 4.5 → Sonnet 4.6 (4.6 defaults to `high`)
- [ ] **[TUNE]** Remove GA beta headers: `effort-2025-11-24`, `fine-grained-tool-streaming-2025-05-14`, `token-efficient-tools-2025-02-19`, `output-128k-2025-02-19`; remove `interleaved-thinking-2025-05-14` once on adaptive thinking
- [ ] **[TUNE]** Switch `client.beta.messages.create(...)` → `client.messages.create(...)` once all betas are removed
- [ ] **[TUNE]** Review system prompt for aggressive tool language (`CRITICAL:`, `MUST`, `If in doubt`) and dial it back

**Extra items when coming from 3.x / 4.0 / 4.1:**
- [ ] **[BLOCKS]** Remove either `temperature` or `top_p` (passing both 400s on Claude 4+)
- [ ] **[BLOCKS]** Update text-editor tool `type` to `text_editor_20250728`
- [ ] **[BLOCKS]** Update text-editor tool `name` to `str_replace_based_edit_tool` — **changing only the `type` and keeping `name: "str_replace_editor"` returns a 400**
- [ ] **[BLOCKS]** Update code-execution tool to `code_execution_20260521`
- [ ] **[BLOCKS]** Delete any `undo_edit` command call sites
- [ ] **[TUNE]** Add handling for `stop_reason == "refusal"`
- [ ] **[TUNE]** Add handling for `stop_reason == "model_context_window_exceeded"` (4.5+)
- [ ] **[TUNE]** Verify tool-param string matching tolerates trailing newlines (preserved on 4.5+)
- [ ] **[TUNE]** If moving to Haiku 4.5: review rate-limit tier (separate pool from Haiku 3.x)

**Verification:**
- [ ] Run one test request and inspect `response.stop_reason`, `response.usage`, and whether tool-use / thinking behavior matches expectations

For cached prompts: the render order and hash inputs did not change, so existing `cache_control` breakpoints keep working. However, **changing the model string invalidates the existing cache** — the first request on the new model will write the cache fresh.

---

## Migrating to Opus 4.7

> **Model ID `claude-opus-4-7` is authoritative as written here.** When the user asks to migrate to Opus 4.7, write `model="claude-opus-4-7"` exactly. Do **not** WebFetch to verify — this guide is the source of truth for migration target IDs. The corresponding entry exists in `shared/models.md`.

Claude Opus 4.7 was Anthropic's most capable model at its launch and is now the previous-generation Opus (Opus 4.8 is current — see Migrating to Opus 4.8 below). It is highly autonomous and performs exceptionally well on long-horizon agentic work, knowledge work, vision tasks, and memory tasks. This section summarizes everything that was new at the 4.7 launch and remains the layered breaking-change path for callers coming from Opus 4.6 or older. It is layered on top of the 4.6 migration above — if the caller is jumping from Opus 4.5 or older, apply the 4.6 changes first, then this section, then the 4.8 section.

**TL;DR for someone already on Opus 4.6:** update the model ID to `claude-opus-4-7`, strip any remaining `budget_tokens` and sampling parameters (both 400 on Opus 4.7), give `max_tokens` extra headroom and re-baseline with `count_tokens()` against the new model, opt back into `thinking.display: "summarized"` if reasoning is surfaced to users, and re-tune `effort` — it matters more on 4.7 than on any prior Opus.

### Breaking changes (will 400 on Opus 4.7)

**Extended thinking removed.**

`thinking: {type: "enabled", budget_tokens: N}` is no longer supported on Claude Opus 4.7 or later models and returns a 400 error. Switch to adaptive thinking (`thinking: {type: "adaptive"}`) and use the effort parameter to control thinking depth. Adaptive thinking is **off by default** on Claude Opus 4.7: requests with no `thinking` field run without thinking, matching Opus 4.6 behavior. Set `thinking: {type: "adaptive"}` explicitly to enable it.

```python
# Before (Opus 4.6)
client.messages.create(
    model="claude-opus-4-6",
    max_tokens=64000,
    thinking={"type": "enabled", "budget_tokens": 32000},
    messages=[{"role": "user", "content": "..."}],
)

# After (Opus 4.7)
client.messages.create(
    model="claude-opus-4-7",
    max_tokens=64000,
    thinking={"type": "adaptive"},
    output_config={"effort": "high"},  # or "max", "xhigh", "medium", "low"
    messages=[{"role": "user", "content": "..."}],
)
```

If the caller wasn't using extended thinking, no change is required — thinking is off by default, or can be set explicitly with `thinking={"type": "disabled"}`.

Delete `budget_tokens` plumbing entirely. For the replacement `effort` value, see **Choosing an effort level on Opus 4.7** below — there is no exact 1:1 mapping from `budget_tokens`.

**Sampling parameters removed.**

The `temperature`, `top_p`, and `top_k` parameters are no longer accepted on Claude Opus 4.7. Requests that include them return a 400 error. Remove these fields from your request payloads. Prompting is the recommended way to guide model behavior on Claude Opus 4.7. If you were using `temperature = 0` for determinism, note that it never guaranteed identical outputs on prior models.

```python
# Before — errors on Opus 4.7
client.messages.create(temperature=0.7, top_p=0.9, ...)

# After
client.messages.create(...)  # no sampling params
```

- **If the intent was determinism** — use `effort: "low"` with a tighter prompt.
- **If the intent was creative variance** — the prompt replacement depends on the use case; **ask the user** how they want variance elicited. If you can't ask, add a use-case-appropriate instruction along the lines of *"choose something off-distribution and interesting"* — e.g. for text generation, *"Vary your phrasing and structure across responses"*; for frontend/design, use the propose-4-directions approach under **Design and frontend coding** below.

### Choosing an effort level on Opus 4.7

`budget_tokens` controlled how much to *think*; `effort` controls how much to think *and* act, so there is no exact 1:1 mapping. **Use `xhigh` for best results in coding and agentic use cases, and a minimum of `high` for most intelligence-sensitive use cases.** Experiment with other levels to further tune token usage and intelligence:

| Level | Use when | Notes |
| --- | --- | --- |
| `max` | Intelligence-demanding tasks worth testing at the ceiling | Can deliver gains in some use cases but may show diminishing returns from increased token usage; can be prone to overthinking |
| `xhigh` | **Most coding and agentic use cases** | The best setting for these; used as the default in Claude Code |
| `high` | Intelligence-sensitive use cases generally | Balances token usage and intelligence; recommended minimum for most intelligence-sensitive work |
| `medium` | Cost-sensitive use cases that need to reduce token usage while trading off intelligence | |
| `low` | Short, scoped tasks and latency-sensitive workloads that are not intelligence-sensitive | |

### Silent default changes (no error, but behavior differs)

**Thinking content omitted by default.**

Thinking blocks still appear in the response stream on Claude Opus 4.7, but their `thinking` field is empty unless you explicitly opt in. This is a silent change from Claude Opus 4.6, where the default was to return summarized thinking text. To restore summarized thinking content on Claude Opus 4.7, set `thinking.display` to `"summarized"`. **The block-field name is unchanged** — it is still `block.thinking` on a `thinking`-type block; do not rename it.

**Detect this:** any code that reads `block.thinking` (or equivalent) from a `thinking`-type block and renders it in a UI, log, or trace. **The fix is the request parameter, not the response handling** — add `display: "summarized"` to the `thinking` parameter:

```python
thinking={"type": "adaptive", "display": "summarized"}  # "display" is new on Opus 4.7; values: "omitted" (default) | "summarized"
```

The default is `"omitted"` on Claude Opus 4.7. If thinking content was never surfaced anywhere, no change needed. If your product streams reasoning to users, the new default appears as a long pause before output begins; set `display: "summarized"` to restore visible progress during thinking.

**Updated token counting.**

Claude Opus 4.7 and Claude Opus 4.6 count tokens differently. The same input text produces a higher token count on Claude Opus 4.7 than on Claude Opus 4.6, and `/v1/messages/count_tokens` will return a different number of tokens for Claude Opus 4.7 than it did for Claude Opus 4.6. The token efficiency of Claude Opus 4.7 can vary by workload shape. Prompting interventions, `task_budget`, and `effort` can help control costs and ensure appropriate token usage. Keep in mind that these controls may trade off model intelligence. **Update your `max_tokens` parameters to give additional headroom, including compaction triggers.** Claude Opus 4.7 provides a 1M context window at standard API pricing with no long-context premium.

What else to check:

- Client-side token estimators (tiktoken-style approximations) calibrated against 4.6
- Cost calculators that multiply tokens by a fixed per-token rate
- Rate-limit retry thresholds keyed to measured token counts

Re-baseline by re-running `client.messages.count_tokens()` against `claude-opus-4-7` on a representative sample of the caller's prompts. Do not apply a blanket multiplier. For cost-sensitive workloads, consider reducing `effort` by one level (e.g. `high` → `medium`). For agentic loops, consider adopting Task Budgets (below).

### New feature: Task Budgets (beta)

Opus 4.7 introduces **task budgets** — tell Claude how many tokens it has for a full agentic loop (thinking + tool calls + final output). The model sees a running countdown and uses it to prioritize work and wrap up gracefully as the budget is consumed.

This is a **suggestion the model is aware of**, not a hard cap. It is distinct from `max_tokens`, which remains the enforced per-response limit and is *not* surfaced to the model. Use `task_budget` when you want the model to self-moderate; use `max_tokens` as a hard ceiling to cap usage.

Requires beta header `task-budgets-2026-03-13`:

```python
client.beta.messages.create(
    betas=["task-budgets-2026-03-13"],
    model="claude-opus-4-7",
    max_tokens=64000,
    thinking={"type": "adaptive"},
    output_config={
        "effort": "high",
        "task_budget": {"type": "tokens", "total": 128000},
    },
    messages=[...],
)
```

Set a generous budget for open-ended agentic tasks and tighten it for latency-sensitive ones. **Minimum `task_budget.total` is 20,000 tokens.** If the budget is too restrictive for the task, the model may complete it less thoroughly, referencing its budget as the constraint. **Do not add `task_budget` during a migration unless you are sure the budget value is right** — if you can run the workload and measure, do so; otherwise ask the user for the value rather than guessing. This is the primary lever for offsetting the token-counting shift on agentic workloads.

### Capability improvements

**High-resolution vision.** Opus 4.7 is the first Claude model with high-resolution image support. Maximum image resolution is **2576 pixels on the long edge** (up from 1568px on Opus 4.6 and prior). This unlocks gains on vision-heavy workloads, especially computer use and screenshot/artifact/document understanding. Coordinates returned by the model now map 1:1 to actual image pixels, so no scale-factor math is needed.

High-res support is **automatic on Opus 4.7** — no beta header, no client-side opt-in required. The model accepts larger inputs and returns pixel-accurate coordinates out of the box.

**Token cost.** Full-resolution images on Opus 4.7 can use up to ~3× more image tokens than on prior models (up to ~4784 tokens per image, vs. the previous ~1,600-token cap). If the extra fidelity isn't needed, downsample client-side before sending to control cost — but **do not add downsampling by default during a migration**. If you're not sure whether the pipeline needs the fidelity, ask the user rather than guessing. Use `count_tokens()` on representative images on Opus 4.7 to re-baseline before reacting to any measured cost shift.

Beyond resolution, Opus 4.7 also improves on low-level perception (pointing, measuring, counting) and natural-image bounding-box localization and detection.

**Knowledge work.** Meaningful gains on tasks where the model visually verifies its own output — `.docx` redlining, `.pptx` editing, and programmatic chart/figure analysis (e.g. pixel-level data transcription via image-processing libraries). If prompts have scaffolding like *"double-check the slide layout before returning"*, try removing it and re-baselining.

**Memory.** Opus 4.7 is better at writing and using file-system-based memory. If an agent maintains a scratchpad, notes file, or structured memory store across turns, that agent should improve at jotting down notes to itself and leveraging its notes in future tasks.

**User-facing progress updates.** Opus 4.7 provides more regular, higher-quality interim updates during long agentic traces. If the system prompt has scaffolding like *"After every 3 tool calls, summarize progress"*, try removing it to avoid excessive user-facing text. If the length or contents of Opus 4.7's updates are not well-calibrated to your use case, explicitly describe what these updates should look like in the prompt and provide examples.

### Real-time cybersecurity safeguards

Requests that involve prohibited or high-risk topics may lead to refusals.

### Fast Mode: Opus 4.8 / 4.7 only

Fast mode is available on Opus 4.8 and Opus 4.7. Only surface this if the caller's code actually uses fast mode (e.g. `model="claude-opus-4-6-fast"`, or `speed="fast"` on an unsupported model); if the word "fast" does not appear in the code, say nothing about Fast Mode.

When you see `model="claude-opus-4-6-fast"` (or any retired `-fast` model string), **the migration edit is** to move the fast-mode traffic onto Opus 4.8, the durable fast-capable tier:

```python
# Request fast mode on Opus 4.8.
client.beta.messages.create(
    model="claude-opus-4-8", max_tokens=4096,
    speed="fast", betas=["fast-mode-2026-02-01"],
    messages=[...],
)
```

That is: switch the model to Opus 4.8 and request fast mode the supported way, using the beta `client.beta.messages.…` endpoint, the `fast-mode-2026-02-01` beta flag, and `speed="fast"` as a top-level request parameter (per-language form in SKILL.md § Fast Mode). Opus 4.7 also supports fast mode today, but it is itself being sunset (fast mode removed by default around Jul 25, 2026), so target Opus 4.8 as the durable choice rather than landing on a tier that is about to lose fast mode. Do **not** leave the code on a retired `-fast` model string — the failure mode differs by version: `claude-opus-4-6-fast` is already retired and the API **silently falls back** to standard Opus 4.6 (no error — the caller loses fast-mode speed without noticing); `claude-opus-4-7-fast`, once removed, will instead return an **API error** (hard failure — requests break outright rather than degrading). Either way, migrate to Opus 4.8 fast mode now.

### Behavioral shifts (prompt-tunable)

These don't break anything, but prompts tuned for Opus 4.6 may land differently. Opus 4.7 is more steerable than 4.6, so small prompt nudges usually close the gap.

**More literal instruction following.** Claude Opus 4.7 interprets prompts more literally and explicitly than Claude Opus 4.6, particularly at lower effort levels. It will not silently generalize an instruction from one item to another, and it will not infer requests you didn't make. The upside of this literalism is precision and less thrash. It generally performs better for API use cases with carefully tuned prompts, structured extraction, and pipelines where you want predictable behavior. A prompt and harness review may be especially helpful for migration to Claude Opus 4.7.

**Verbosity calibrates to task complexity.** Opus 4.7 scales response length to how complex it judges the task to be, rather than defaulting to a fixed verbosity — shorter answers on simple lookups, much longer on open-ended analysis. If the product depends on a particular length or style, tune the prompt explicitly. To reduce verbosity:

> *"Provide concise, focused responses. Skip non-essential context, and keep examples minimal."*

If you see specific kinds of over-verbosity (e.g. over-explaining), add instructions targeting those. Positive examples showing the desired level of concision tend to be more effective than negative examples or instructions telling the model what not to do. Do **not** assume existing "be concise" instructions should be removed — test first.

**Tone and writing style.** Opus 4.7 is more direct and opinionated, with less validation-forward phrasing and fewer emoji than Opus 4.6's warmer style. As with any new model, prose style on long-form writing may shift. If the product relies on a specific voice, re-evaluate style prompts against the new baseline. If a warmer or more conversational voice is wanted, specify it:

> *"Use a warm, collaborative tone. Acknowledge the user's framing before answering."*

**`effort` matters more than on any prior Opus.** Opus 4.7 respects `effort` levels more strictly, especially at the low end. At `low` and `medium` it scopes work to what was asked rather than going above and beyond — good for latency and cost, but on moderate tasks at `low` there is some risk of under-thinking.

- If shallow reasoning shows up on complex problems, raise `effort` to `high` or `xhigh` rather than prompting around it.
- If `effort` must stay `low` for latency, add targeted guidance: *"This task involves multi-step reasoning. Think carefully through the problem before responding."*
- **At `xhigh` or `max`, set a large `max_tokens`** so the model has room to think and act across tool calls and subagents. Start at 64K and tune from there. (`xhigh` is a new effort level on Opus 4.7, between `high` and `max`.)

Adaptive-thinking triggering is also steerable. If the model thinks more often than wanted — which can happen with large or complex system prompts — add: *"Thinking adds latency and should only be used when it will meaningfully improve answer quality — typically for problems that require multi-step reasoning. When in doubt, respond directly."*

**Uses tools less often by default.** Opus 4.7 tends to use tools less often than 4.6 and to use reasoning more. This produces better results in most cases, but for products that rely on tools (search/retrieval, function-calling, computer-use steps), it can drop tool-use rate. Two levers:

- **Raise `effort`** — `high` or `xhigh` show substantially more tool usage in agentic search and coding, and are especially useful for knowledge work.
- **Prompt for it** — be explicit in tool descriptions or the system prompt about when and how to use the tool, and encourage the model to err on the side of using it more often:

> *"When the answer depends on information not present in the conversation, you MUST call the `search` tool before answering — do not answer from prior knowledge."*

**Fewer subagents by default.** Opus 4.7 tends to spawn fewer subagents than 4.6. This is steerable — give explicit guidance on when delegation is desirable. For a coding agent, for example:

> *"Do NOT spawn a subagent for work you can complete directly in a single response (e.g. refactoring a function you can already see). Spawn multiple subagents in the same turn when fanning out across items or reading multiple files."*

**Design and frontend coding.** Opus 4.7 has stronger design instincts than 4.6, with a consistent default house style: warm cream/off-white backgrounds (around `#F4F1EA`), serif display type (Georgia, Fraunces, Playfair), italic word-accents, and a terracotta/amber accent. This reads well for editorial, hospitality, and portfolio briefs, but will feel off for dashboards, dev tools, fintech, healthcare, or enterprise apps — and it appears in slide decks as well as web UIs.

The default is persistent. Generic instructions ("don't use cream," "make it clean and minimal") tend to shift the model to a different fixed palette rather than producing variety. Two approaches work reliably:

1. **Specify a concrete alternative.** The model follows explicit specs precisely — give exact hex values, typefaces, and layout constraints.
2. **Have the model propose options before building.** This breaks the default and gives the user control:

   > *"Before building, propose 4 distinct visual directions tailored to this brief (each as: bg hex / accent hex / typeface — one-line rationale). Ask the user to pick one, then implement only that direction."*

If the caller previously relied on `temperature` for design variety, use approach (2) — it produces meaningfully different directions across runs.

Opus 4.7 also requires less frontend-design prompting than previous models to avoid generic "AI slop" aesthetics. Where earlier models needed a lengthy anti-slop snippet, Opus 4.7 generates distinctive, creative frontends with a much shorter nudge. This snippet works well alongside the variety approaches above:

> *"NEVER use generic AI-generated aesthetics like overused font families (Inter, Roboto, Arial, system fonts), cliched color schemes (particularly purple gradients on white or dark backgrounds), predictable layouts and component patterns, and cookie-cutter design that lacks context-specific character. Use unique fonts, cohesive colors and themes, and animations for effects and micro-interactions."*

**Interactive coding products.** Opus 4.7's token usage and behavior can differ between autonomous, asynchronous coding agents with a single user turn and interactive, synchronous coding agents with multiple user turns. Specifically, it tends to use more tokens in interactive settings, primarily because it reasons more after user turns. This can improve long-horizon coherence, instruction following, and coding capabilities in long interactive coding sessions, but also comes with more token usage. To maximize both performance and token efficiency in coding products, use `effort: "xhigh"` or `"high"`, add autonomous features (like an auto mode), and reduce the number of human interactions required from users.

When limiting required user interactions, specify the task, intent, and relevant constraints upfront in the first human turn. Well-specified, clear, and accurate task descriptions upfront help maximize autonomy and intelligence while minimizing extra token usage after user turns — because Opus 4.7 is more autonomous than prior models, this usage pattern helps to maximize performance. In contrast, ambiguous or underspecified prompts conveyed progressively over multiple user turns tend to reduce token efficiency and sometimes performance.

**Code review.** Opus 4.7 is meaningfully better at finding bugs than prior models, with both higher recall and precision. However, if a code-review harness was tuned for an earlier model, it may initially show *lower* recall — this is likely a harness effect, not a capability regression. When a review prompt says "only report high-severity issues," "be conservative," or "don't nitpick," Opus 4.7 follows that instruction more faithfully than earlier models did: it investigates just as thoroughly, identifies the bugs, and then declines to report findings it judges to be below the stated bar. Precision rises, but measured recall can fall even though underlying bug-finding has improved.

Recommended prompt language:

> *"Report every issue you find, including ones you are uncertain about or consider low-severity. Do not filter for importance or confidence at this stage — a separate verification step will do that. Your goal here is coverage: it is better to surface a finding that later gets filtered out than to silently drop a bug. For each finding, include your confidence level and an estimated severity so a downstream filter can rank them."*

This can be used without an actual second step, but moving confidence filtering out of the finding step often helps. If the harness has a separate verification/dedup/ranking stage, tell the model explicitly that its job at the finding stage is coverage, not filtering. If single-pass self-filtering is wanted, be concrete about the bar rather than using qualitative terms like "important" — e.g. *"report any bugs that could cause incorrect behavior, a test failure, or a misleading result; only omit nits like pure style or naming preferences."* Iterate on prompts against a subset of evals to validate recall or F1 gains.

**Computer use.** Computer use works across resolutions up to the new 2576px / 3.75MP maximum. Sending images at **1080p** provides a good balance of performance and cost. For particularly cost-sensitive workloads, **720p** or **1366×768** are lower-cost options with strong performance. Test to find the ideal settings for the use case; experimenting with `effort` can also help tune behavior.

---

## Opus 4.7 Migration Checklist

Every item is tagged: **`[BLOCKS]`** items cause a 400 error, infinite loop, silent truncation, or empty output if missed — apply these as code edits, not as suggestions. **`[TUNE]`** items are quality/cost adjustments — surface them to the user as recommendations.

`[BLOCKS]` items prefixed with **"If…"** or **"At…"** are conditional. Before working through the list, **scan the file** for the conditions: does it surface thinking text to a UI/log? Does it set `output_config.effort` to `"x-high"` or `"max"`? Is it a security workload? Is it a multi-turn agentic loop? Apply only the items whose condition matches.

- [ ] **[BLOCKS]** Replace `thinking: {type: "enabled", budget_tokens: N}` with `thinking: {type: "adaptive"}` + `output_config.effort`; delete `budget_tokens` plumbing entirely
- [ ] **[BLOCKS]** Strip `temperature`, `top_p`, `top_k` from request construction
- [ ] **[BLOCKS]** If thinking content is surfaced to users or stored in logs: add `thinking.display: "summarized"` (otherwise the rendered text is empty)
- [ ] **[BLOCKS]** At `output_config.effort` of `xhigh` or `max`: set `max_tokens` ≥ 64000 (otherwise output truncates mid-thought)
- [ ] **[TUNE]** Give `max_tokens` and compaction triggers extra headroom; re-run `count_tokens()` against `claude-opus-4-7` on representative prompts to re-baseline (no blanket multiplier)
- [ ] **[TUNE]** Re-baseline cost and rate-limit dashboards *before* reacting to measured shifts
- [ ] **[TUNE]** Re-evaluate `effort` per route — use `xhigh` for coding/agentic and a minimum of `high` for most intelligence-sensitive work; it matters more on 4.7 than any prior Opus
- [ ] **[TUNE]** Multi-turn agentic loops: adopt the API-native Task Budgets (`output_config.task_budget`, beta `task-budgets-2026-03-13`, minimum 20k tokens) — this is for capping *cumulative* spend across a loop; per-turn depth is `effort`
- [ ] **[TUNE]** Check for ambiguous or underspecified instructions that relied on 4.6 generalizing intent, and update them to be clearer or more precise — 4.7 follows them literally
- [ ] **[TUNE]** Tool-use workloads: add explicit when/how-to-use guidance to tool descriptions (4.7 reaches for tools less often)
- [ ] **[TUNE]** Verbosity: test existing length instructions before changing them — 4.7 calibrates length to task complexity, so tune for the desired output rather than assuming a direction
- [ ] **[TUNE]** Remove forced-progress-update scaffolding (*"after every N tool calls…"*)
- [ ] **[TUNE]** Remove knowledge-work verification scaffolding (*"double-check the slide layout…"*) and re-baseline
- [ ] **[TUNE]** Add tone instruction if a warmer / more conversational voice is needed; re-evaluate style prompts on writing-heavy routes
- [ ] **[TUNE]** Subagent tool present: add explicit spawn / don't-spawn guidance
- [ ] **[TUNE]** Frontend/design output: specify a concrete palette/typeface, or have the model propose 4 visual directions before building (the default cream/serif house style is persistent)
- [ ] **[TUNE]** Interactive coding products: use `effort: "xhigh"` or `"high"`, add autonomous features (e.g. an auto mode) to reduce human interactions, and specify task/intent/constraints upfront in the first turn
- [ ] **[TUNE]** Code-review harnesses: remove or loosen "only report high-severity" / "be conservative" filters and have the model report every finding with confidence + severity; move filtering to a downstream step (4.7 follows severity filters more literally, which can depress measured recall)
- [ ] **[TUNE]** Vision-heavy pipelines (screenshots, charts, document understanding): leave images at native resolution up to 2576px long edge for the accuracy gain; remove any scale-factor math from coordinate handling (coords are now 1:1 with pixels). No beta header / opt-in needed — high-res is automatic on Opus 4.7.
- [ ] **[TUNE]** Computer-use pipelines: send screenshots at 1080p for a good performance/cost balance (720p or 1366×768 for cost-sensitive workloads); experiment with `effort` to tune behavior
- [ ] **[TUNE]** Cost-sensitive image pipelines: full-res images on 4.7 use up to ~4784 tokens vs ~1,600 on prior models (~3×). Downsampling client-side before upload avoids the increase, but **do not downsample by default** — if you're unsure whether fidelity is needed, ask the user. Re-baseline with `count_tokens()` on representative images before reacting to cost shifts.

---

## Migrating to Opus 4.8

> **Model ID `claude-opus-4-8` is authoritative as written here.** When the user asks to migrate to Opus 4.8, write `model="claude-opus-4-8"` exactly. Do **not** WebFetch to verify — this guide is the source of truth for migration target IDs. The corresponding entry exists in `shared/models.md`.

Claude Opus 4.8 is our most capable Opus-tier model — highly autonomous, with state-of-the-art long-horizon agentic execution, knowledge work, and memory. It is layered on top of the Opus 4.7 migration above. If the caller is jumping from Opus 4.6 or older, apply the 4.6 and 4.7 sections first, then this one.

**No new breaking changes.** Opus 4.8 keeps the same request surface as Opus 4.7. The same calls that already work on 4.7 work unchanged on 4.8 — adaptive thinking only (`thinking: {type: "enabled", budget_tokens: N}` still 400s; use `{type: "adaptive"}`), sampling parameters (`temperature`, `top_p`, `top_k`) still rejected, last-assistant-turn prefills still 400, `thinking.display` still defaults to `"omitted"`, and the `low`/`medium`/`high`/`xhigh`/`max` effort levels, Task Budgets (beta), and high-resolution vision all behave as on 4.7. A 4.7 → 4.8 migration is therefore **the model-ID swap plus prompt re-tuning** — there is no required code edit beyond the model string.

**TL;DR for someone already on Opus 4.7:** swap the model ID to `claude-opus-4-8`. Nothing else is required to avoid an error. Then re-tune prompts for the behavioral shifts: 4.8 narrates *more* than 4.7 (add a silence-default if you want 4.7-like terseness), writes in a warmer, less hedged voice, is more deliberate and asks more often (add autonomy guidance to claw back ask-rate), and is more conservative about reaching for search, subagents, file-based memory, and custom tools (add explicit "when to use this" triggering). For long-horizon agentic work, give the full task specification up front in one well-specified turn and run at high effort.

### No new API breaking changes (inherited from 4.7)

These all carry over from Opus 4.7 unchanged — apply them only if the caller is coming from Opus 4.6 or earlier (see the **Migrating to Opus 4.7** section above for the before/after and the SDK-specific syntax):

- `thinking: {type: "enabled", budget_tokens: N}` → 400. Use `thinking: {type: "adaptive"}` + `output_config.effort`.
- `temperature`, `top_p`, `top_k` → 400. Remove them; steer with prompting.
- Last-assistant-turn prefills → 400. Use `output_config.format` (structured outputs) or a system-prompt instruction.
- `thinking.display` defaults to `"omitted"`; set `"summarized"` if you surface reasoning to users.

If the caller is already on Opus 4.7 and these are clean, there is nothing to change here.

### New API feature: mid-session system prompts

You can deliver trusted instructions partway through a session by placing `{"role": "system", ...}` entries directly in the `messages` array — without editing the top-level system prompt and invalidating your prompt cache. Use it for things the application learns mid-session: the user delivered async context, a mode toggled (auto-approve enabled), files changed on disk, the remaining token budget dropped.

```python
messages=[
    {"role": "user", "content": [{"type": "tool_result", "tool_use_id": "...", "content": "..."}]},
    {"role": "system", "content": "This project's codebase is Go. Write code in Go."},
]
```

Phrase these as **context, not commands**. State the fact and let Claude act on it; avoid override-style language ("ignore what the user said", "regardless of the user's request", "disregard the previous instruction"). Claude is trained to protect users from instructions that appear to work against them, and that protection applies to the system role too. No beta header is required; available on Claude Opus 4.8. For cache-placement details and the older-model `<system-reminder>` fallback, see `shared/prompt-caching.md` and `shared/agent-design.md`.

### Capability improvements

**Long-horizon agentic execution.** Opus 4.8 is state-of-the-art at long, autonomous agentic work — complex refactors and overnight coding runs that complete without human correction. To get the most out of it, **give the full task specification up front in a single well-specified initial turn and run at high effort** (`effort: "high"` or `"xhigh"`). Its long-horizon coherence comes partly from reasoning more at each step; combined with a clear up-front goal, that more-intelligent planning often produces more efficient *and* more accurate output than prior frontier models. The "clear goal up front" principle maps to two product surfaces: in Claude Code, `/goal` sets direction for the run; with **Managed Agents (CMA)**, state what "done" looks like via an **Outcome** (`user.define_outcome` with a gradeable rubric — the harness runs an iterate → grade → revise loop), see `shared/managed-agents-outcomes.md`.

**Effort is a dimension to test, not a fixed setting.** On prior models many reached for `xhigh` reflexively to maximize intelligence. Opus 4.8 has a higher intelligence ceiling, so **start at `high` as the default and iterate** rather than defaulting to `xhigh`. Sweep `medium`, `high`, and `xhigh` on your own eval set and weigh the intelligence ↔ latency ↔ cost tradeoff per route — the relationship isn't monotonic: higher effort up front often *reduces* turn count and total cost on agentic work, while for some tasks `medium` delivers equally good results in less time. Reserve `max` for extremely hard, latency-insensitive cases. The per-level effort table in the **Migrating to Opus 4.7** section above applies unchanged on 4.8.

**Writing voice and clarity.** Testers consistently describe 4.8's prose as clearer, warmer, and less hedged than prior models, with fewer measurable AI vocal tics — especially at higher effort, where it approaches expert-level prose and structure. This is roughly the **opposite** direction from the 4.7 shift (4.7 was more clipped, direct, and less validation-forward). If you added style prompts to counter 4.7's terseness or to inject warmth, re-evaluate them against the new baseline before keeping them — they may now overcorrect. 4.8 is also a stronger thought partner: more thoughtful, more willing to push back, and more likely to infer the right answer from context.

**Code review and debugging.** Stronger real-bug finding and clearer explanations than 4.7 — one-shot fixes where 4.7 needed more, and correctly identifying intermittent flakes rather than declaring "fixed" after one clean run. The 4.7 caveat still applies: if a review harness says "only report high-severity issues" or "be conservative", 4.8 follows it literally and measured recall can drop even though underlying bug-finding improved. Tell the model to report everything and filter downstream (or review a second time) — see the **Code review** guidance in the 4.7 section for the recommended prompt.

### Behavioral shifts (prompt-tunable)

None of these break code, but prompts tuned for Opus 4.7 may land differently. 4.8 follows instructions well, so small, explicit nudges close the gap.

**Tool triggering is surface-dependent (search & knowledge).** 4.8's tool-triggering is more surface-dependent than in prior models: with a system prompt present it is high-precision / low-recall — web search triggers slightly more often but runs fewer rounds per trigger, while knowledge-retrieval tools (Drive, project knowledge, connected files) trigger *less* often. It searches when it's confident search is needed and otherwise answers from context, which can lower research depth on tasks that need it. Recover should-search rate with an explicit search-first instruction:

> ```
> <search_first>
> For questions where current information would change the answer (recent events, current roles or prices, version-specific behavior, or anything the user flags as time-sensitive) search before answering rather than answering from memory. For open-ended research requests, begin searching immediately; do not ask a scoping question first unless the request is genuinely ambiguous about what to research.
> </search_first>
> ```

**Under-utilization of subagents, memory, and custom tools.** Separately from search, 4.8 is conservative about reaching for capabilities that need an explicit "decide to use this" step — file-based memory, subagent delegation, custom tools. It won't reach for complex or expensive capabilities unless reasonably sure they're needed. This is steerable since 4.8 follows instructions well — say *when* each capability applies, not just that it exists:

> *"Before any task longer than a few turns, check your memory file for relevant prior context and write new findings to it as you go. When a task fans out across independent items (many files to read, many tests to run, many candidates to check), delegate to subagents rather than iterating serially."*

The same lever works at the **tool-description** level, not just the system prompt: prescriptive descriptions that state *when* to call a tool (e.g. "Call this when the user asks about current prices or recent events") give meaningful lift on 4.8 over descriptions that only state what the tool does. Make the trigger condition part of each capability's own `description`.

**More user-facing narration.** 4.8 narrates more than 4.7 — more text between tool calls in long tool-calling sessions, and longer, more detailed end-of-task wrap-ups by default. If you previously added scaffolding to force interim status ("after every 3 tool calls, summarize progress"), **remove it** — 4.8 does this on its own. If the narration is too verbose for a coding agent, an explicit silence-default makes it behave like 4.7 with no loss of quality:

> *"Default to silence between tool calls. Only write text when you find something, change direction, or hit a blocker — one sentence each. Do not narrate routine actions ('Now I'll...', 'Let me check...', 'Looking at...'). When done: one or two sentences on the outcome. Do not recap every file or test — the user has been following along."*

For knowledge-work deliverables (reports, analysis readouts), verbosity responds very well to instructions in user preferences or the user turn — expose a verbosity preference rather than hard-coding a length.

**More deliberate — asks more often.** 4.8 is more deliberate than prior Opus models. On minor decisions it would previously just make (a variable name, a default value, which of two equivalent approaches), it tends to pause and ask, and it often closes a completed task with "Want me to also…?" rather than doing the obvious next step or stopping cleanly. This is preferred for high-stakes or unfamiliar codebases, but bugs users when uncalibrated. Grant autonomy on the small stuff while keeping caution where it matters (in Claude Code testing this cut ask-rate by ~12 percentage points with no increase in over-reach):

> *"For minor choices (naming, formatting, default values, which approach among equivalents), pick a reasonable option and note it rather than asking. For scope changes or destructive actions, still ask first."*

**Verbose reasoning when thinking is disabled.** With `thinking: {type: "disabled"}`, 4.8 occasionally writes longer explanations of its reasoning into the visible response, which reads as verbose when the user wants a fast, quick answer. The simplest fix is to leave adaptive thinking on — set `thinking: {type: "adaptive"}` (the recommended setting; it adjusts how much to think per task). Note adaptive is **not** on when the field is omitted — like Opus 4.7, a request with no `thinking` field runs without thinking, so set it explicitly. If you need thinking off for latency or cost, scope it in the system prompt:

> *"Respond only with your final answer. Do not include exploratory reasoning, intermediate drafts, diffs you considered but rejected, or meta-commentary about your process."*

### Opus 4.8 Migration Checklist

Every item is tagged: **`[BLOCKS]`** items cause a 400 error if missed; **`[TUNE]`** items are quality/cost adjustments — surface them to the user as recommendations.

For a caller **already on Opus 4.7**, only the first item is required; everything else is `[TUNE]`. The conditional `[BLOCKS]` item applies only when coming from Opus 4.6 or earlier.

- [ ] **[BLOCKS]** Update the `model=` string to `claude-opus-4-8`
- [ ] **[BLOCKS]** *(only if coming from Opus 4.6 or earlier)* Apply the **Migrating to Opus 4.7** breaking changes first — `budget_tokens` → adaptive thinking, strip `temperature`/`top_p`/`top_k`, remove last-assistant-turn prefills. These already 400 on 4.7 and continue to 400 on 4.8.
- [ ] **[TUNE]** Long-horizon / agentic work: put the full task spec in one well-specified first turn and run at `high` or `xhigh` effort (Claude Code: `/goal`; Managed Agents: an Outcome with a gradeable rubric)
- [ ] **[TUNE]** Effort: sweep `medium` / `high` / `xhigh` on your eval set and pick per route by the intelligence ↔ latency ↔ cost tradeoff (default `high`, `xhigh` for coding/agentic)
- [ ] **[TUNE]** Research depth & tool use: add a search-first instruction; add explicit triggering guidance for subagents, file-based memory, and custom tools (4.8 under-reaches for these by default) — in the system prompt *and* in each tool's own `description` (prescriptive "call this when…" descriptions give measurable lift)
- [ ] **[TUNE]** Narration: remove forced-progress scaffolding (*"after every N tool calls…"*); add a silence-default if a coding agent is too chatty
- [ ] **[TUNE]** Autonomy: add small-decisions-don't-ask guidance to cut ask-rate, while keeping caution on scope changes / destructive actions
- [ ] **[TUNE]** Writing voice: re-evaluate style prompts added to counter 4.7's directness — 4.8 is warmer and less hedged by default; re-baseline before keeping them
- [ ] **[TUNE]** Code-review harnesses: keep the report-everything-filter-downstream pattern (4.8 follows "only high-severity" / "be conservative" filters literally, which can depress measured recall)
- [ ] **[TUNE]** Thinking-disabled paths: add a final-answer-only instruction if reasoning leaks into the visible response
- [ ] **[TUNE]** Consider mid-session system messages (`role:"system"` in `messages`; no beta header) for context the app learns mid-session, instead of rebuilding the top-level system prompt and invalidating the cache

---

## Migrating to Claude Sonnet 5

> **Model ID `claude-sonnet-5` is authoritative as written here.** When the user asks to migrate to Claude Sonnet 5, write `model="claude-sonnet-5"` exactly. Do **not** WebFetch to verify — this guide is the source of truth for migration target IDs. The corresponding entry exists in `shared/models.md`.

Claude Sonnet 5 substantially improves on Sonnet 4.6 for coding and agentic work, reaching what was previously Opus-tier quality on many tasks. Its API surface aligns with Opus 4.7/4.8: manual extended thinking is removed (adaptive or disabled only, adaptive is the default), and non-default sampling parameters are rejected. This section is layered on top of the Sonnet 4.6 migration above — if the caller is jumping from Sonnet 4.5 or older, apply the 4.6 changes first, then this one.

**TL;DR for someone already on Sonnet 4.6:** swap the model ID to `claude-sonnet-5`. Replace any remaining `thinking: {type: "enabled", budget_tokens: N}` with `thinking: {type: "adaptive"}` (the transitional escape hatch is gone — it now 400s), and note that omitting `thinking` now runs adaptive (4.6 ran thinking-off). Strip non-default `temperature`/`top_p`/`top_k`. Re-run `count_tokens()` against `claude-sonnet-5` — the new tokenizer produces ~30% more tokens for the same text, so token-budgeted limits and cost baselines shift even though per-token pricing is unchanged. `effort` defaults to `high`, the same as Sonnet 4.6 — raise to `xhigh` for the hardest coding and agentic tasks (Claude Sonnet 5 supports the full `low`/`medium`/`high`/`xhigh`/`max` range), and give `max_tokens` headroom at `xhigh`/`max` (the new tokenizer means a Sonnet-4.6-tuned `max_tokens` may truncate equivalent output). Then re-tune prompts: Claude Sonnet 5 interprets instructions more literally than 4.6 — holdover style/tone directives now apply at face value; it is more agentic by default and reaches for tools and self-verification loops more readily (with thinking disabled it is less tool-eager — add an explicit nudge); it gives better in-progress updates by default (drop forced "summarize every N tool calls" scaffolding); and code-review harnesses with conservative-reporting instructions may see lower recall (tell it to report everything and filter downstream).

### Breaking changes (will 400 on Claude Sonnet 5)

These bring the Sonnet line onto the same request surface as Opus 4.7/4.8. See the **Per-SDK Syntax Reference** above for the language-specific spelling of each.

**1. Extended thinking removed — adaptive only.** `thinking: {type: "enabled", budget_tokens: N}` returns a 400. The transitional escape hatch that still worked on Sonnet 4.6 is gone. Use adaptive thinking with an effort hint:

```python
# Before — deprecated on Sonnet 4.6, now errors on Claude Sonnet 5
thinking={"type": "enabled", "budget_tokens": 10000}

# After
thinking={"type": "adaptive"},
output_config={"effort": "high"},  # or "xhigh" for the hardest coding/agentic tasks
```

To turn thinking off entirely, set `thinking: {type: "disabled"}` — but see *Adaptive vs. disabled* below before doing so.

**2. Sampling parameters rejected.** Setting `temperature`, `top_p`, or `top_k` to a non-default value returns a 400; omitting the parameter, or passing its default, is still accepted. The safest migration is to omit them entirely and steer with prompting. If the caller was relying on `temperature=0` for determinism, note in the migration comment that it never guaranteed identical outputs.

```python
# Before
client.messages.create(model="claude-sonnet-4-6", temperature=0.2, ...)

# After — omit entirely
client.messages.create(model="claude-sonnet-5", ...)
```

**3. Bedrock only: forced `tool_choice` requires `thinking: {type: "disabled"}`.** On Amazon Bedrock, pass `thinking: {type: "disabled"}` alongside `tool_choice: {type: "tool", name: ...}` or `tool_choice: {type: "any"}`. The Claude API and Vertex AI do not require this.

**Not a request-shape error, but handle it: cybersecurity safeguards.** Claude Sonnet 5 is substantially more cyber-capable than Sonnet 4.6, so — like Opus 4.7/4.8 — requests touching prohibited or high-risk topics may be refused. Handle it as a content outcome (see the `refusal` stop-reason guidance in the Claude Fable 5 section if the caller needs a fallback path).

**Unchanged from Sonnet 4.6:** assistant-turn prefills still return a 400 (use `output_config.format` or a system-prompt instruction); the 1M-token context window, the 128k max-output ceiling, prompt caching, batch processing, the Files API, PDF support, vision, and the full server- and client-side tool set all carry over.

### Silent default change: adaptive thinking on when `thinking` is omitted

On Sonnet 4.6, a request with no `thinking` field runs **without** thinking. On Claude Sonnet 5, the same request runs with **adaptive thinking**. This is not an error — but callers who never set `thinking` will now see thinking output (and spend thinking tokens) where they didn't before. `max_tokens` is a hard limit on total output (thinking + response text), so a workload that ran thinking-off on Sonnet 4.6 by omission may now truncate. Either set `thinking: {type: "disabled"}` explicitly to keep the old behavior, or revisit `max_tokens` to leave room for thinking.

### Silent default change: `thinking.display` defaults to `"omitted"`

`thinking.display` defaults to `"omitted"` on Claude Sonnet 5 (matching Opus 4.7/4.8 and Claude Fable 5); on Sonnet 4.6 it defaulted to `"summarized"`. With the default, `thinking` blocks stream with empty text — to a streaming UI this looks like a long pause before output. Combined with the adaptive-on-by-default change above, a Sonnet 4.6 caller who omits `thinking` entirely now gets adaptive thinking *and* empty-text thinking blocks. If you stream reasoning to users, set `thinking: {type: "adaptive", display: "summarized"}` explicitly. `display` controls visibility only — thinking happens and is billed the same under every setting.

### New tokenizer (~30% more tokens)

Claude Sonnet 5 uses the same new tokenizer as Opus 4.7/4.8. The same input text produces approximately 30% more tokens than on Sonnet 4.6. No request/response shape changes and no code edits are required, but **everything measured or budgeted in tokens shifts**: `usage` fields and `count_tokens()` results for the same text are higher, the 1M context window holds less text, and a `max_tokens` limit tuned for Sonnet 4.6 may truncate equivalent output. Per-token pricing is unchanged at the $3/$15 sticker (introductory $2/$10 per MTok applies through 2026-08-31), so the cost of an equivalent request can differ. Re-run `count_tokens()` against `claude-sonnet-5` rather than reusing counts measured against earlier models, and re-baseline cost dashboards before reacting to measured shifts.

### Choosing an effort level on Claude Sonnet 5

`effort` defaults to `high` when not set (same as Sonnet 4.6 and Opus 4.8). Claude Sonnet 5 supports the full `low`/`medium`/`high`/`xhigh`/`max` range — the first Sonnet-tier model with `xhigh`. **Keep the `high` default for most work and raise to `xhigh` for the hardest coding and agentic tasks**:

| Level    | When to use on Claude Sonnet 5 |
| -------- | ----- |
| `max`    | Tasks needing the absolute highest capability with no token constraint. Can deliver gains in some use cases but may show diminishing returns and is sometimes prone to overthinking — test before committing |
| `xhigh`  | The hardest coding and agentic use cases — the recommended setting for those |
| `high`   | The default; balances token usage and intelligence for most use cases |
| `medium` | Cost-saving step-down from the default — comparable to Sonnet 4.6 at `high` |
| `low`    | Short, scoped tasks and latency-sensitive workloads that aren't intelligence-sensitive (chat, simple lookups) |

As a rough cross-model mapping when migrating: Claude Sonnet 5 at `medium` is comparable in intelligence to Sonnet 4.6 at `high`, and Claude Sonnet 5 at `high` is comparable to Sonnet 4.6 at `max`. When benchmarking, match by observed thinking length rather than effort name.

Claude Sonnet 5 **respects effort levels strictly, especially at the low end**. At `low` and `medium` it scopes its work to what was asked rather than going above and beyond — good for latency and cost, but on moderately complex tasks at `low` there is some risk of under-thinking. If you observe shallow reasoning on complex problems, **raise effort to `high` or `xhigh` rather than prompting around it**. If you must keep effort at `low` for latency, add targeted guidance:

> *"This task involves multi-step reasoning. Think carefully through the problem before responding."*

**Leave `max_tokens` headroom at `xhigh`/`max`.** Set a large output token budget (up to the 128k cap, unchanged from Sonnet 4.6) so the model has room for thinking and tool calls. On long tasks, adaptive thinking can use a large share of the budget; if the budget is tight you may see a response that is almost entirely thinking followed by a truncated answer and `stop_reason: "max_tokens"` — raise `max_tokens` or drop to `medium`. Because Claude Sonnet 5 uses the new tokenizer (~30% more tokens for the same text), `max_tokens` limits tuned for Sonnet 4.6 may truncate equivalent output.

### Adaptive vs. disabled thinking

Leave adaptive thinking on. Claude Sonnet 5 calibrates thinking spend to task complexity; the small added latency is usually worth the quality gain. If the caller was running Sonnet 4.6 with thinking off, **try adaptive + `effort: "low"` first** rather than `thinking: {type: "disabled"}`.

The triggering behavior for adaptive thinking is steerable. If the model emits thinking blocks more often than wanted (which can happen with large or complex system prompts), prompt it directly — and measure the effect on quality:

> *"Thinking adds latency and should only be used when it will meaningfully improve answer quality, typically for problems that require multi-step reasoning. When in doubt, respond directly."*

Conversely, if you're running hard workloads at `medium` and seeing under-thinking, the first lever is to raise effort; if you need finer control, prompt for it directly.

### Capability improvements

**Coding and agentic tasks.** The largest gains over Sonnet 4.6 are in coding and agentic tasks. Claude Sonnet 5 performs well out of the box on existing Sonnet 4.6 prompts.

**High-resolution vision.** Claude Sonnet 5 is the first Sonnet-tier model with high-resolution image support: maximum **2576 pixels on the long edge** (up from 1568px on Sonnet 4.6). High-res images can use up to ~3× more image tokens than on Sonnet 4.6 (4784 vs 1568 tokens per image at the limit) — if the added fidelity isn't needed, downsample before sending to control token costs. No beta header or opt-in required.

**Computer use.** Supports the `computer_20251124` tool version (beta header `computer-use-2025-11-24`). Capability works across resolutions up to the 2576px / 3.75MP maximum; sending screenshots at **1080p** provides a good balance of performance and cost. For particularly cost-sensitive workloads, **720p** or **1366×768** are lower-cost options with strong performance. Test to find the ideal settings for the use case; experimenting with `effort` can also help tune behavior.

### Behavioral shifts (prompt-tunable)

None of these break code, but prompts tuned for Sonnet 4.6 may land differently. Claude Sonnet 5 follows instructions closely, so small explicit directives close the gap.

**Response length and verbosity.** Claude Sonnet 5 calibrates response length to task complexity rather than defaulting to a fixed verbosity — usually shorter on simple lookups, longer on open-ended analysis. If a product depends on a particular verbosity, tune the prompt. To decrease verbosity:

> *"Provide concise, focused responses. Skip non-essential context, and keep examples minimal."*

If you see specific kinds of verbosity (e.g. over-explaining), add targeted instructions to prevent them. Positive examples showing the desired concision tend to be more effective than telling the model what not to do.

**Tool use triggering.** Claude Sonnet 5 is more agentic than Sonnet 4.6 by default and will reach for tools and run self-verification loops more readily. **With thinking disabled**, the model is less likely to reach for tools or consider searching — if the harness relies on tool calls with thinking off, add an explicit nudge in the system prompt. `effort` is also a lever: `high` and `xhigh` show substantially more tool usage in agentic search and coding. For scenarios where you want more tool use, also explicitly instruct when and how to use the tools (e.g. if web-search is under-used, describe in the prompt why and how it should be called).

**User-facing progress updates.** Claude Sonnet 5 provides regular, higher-quality updates to the user throughout long agentic traces by default. If the harness has scaffolding to force interim status messages ("After every 3 tool calls, summarize progress"), **try removing it**. If the length or content of the updates isn't well-calibrated to the use case, describe what they should look like in the prompt and provide an example.

**More literal instruction following.** Claude Sonnet 5 interprets prompts literally and explicitly, particularly at lower effort levels. It does not silently generalize an instruction from one item to another, and it does not infer requests that weren't made. The upside is precision — better for carefully tuned prompts, structured extraction, and pipelines that need predictable behavior. If an instruction should apply broadly, **state the scope explicitly** ("Apply this formatting to every section, not just the first one"). The same literalism means style/tone directives carried over from Sonnet 4.6 may now over-apply — re-baseline holdover lines like "be concise" before keeping them.

**Tone and writing style.** Prose style on long-form writing may shift. If a product relies on a specific voice, re-evaluate style prompts against the new baseline. For a warmer or more conversational voice:

> *"Use a warm, collaborative tone. Acknowledge the user's framing before answering."*

Because `temperature`/`top_p`/`top_k` are not accepted on Claude Sonnet 5, callers who previously relied on `temperature` for stylistic variety must use system-prompt instructions instead.

**Code review harnesses.** A review harness tuned for an earlier model may initially see lower recall on Claude Sonnet 5. This is likely a harness effect, not a capability regression: when a review prompt says "only report high-severity issues" / "be conservative" / "don't nitpick," Claude Sonnet 5 follows that instruction more faithfully than earlier models did — it investigates just as thoroughly, identifies the bugs, and then doesn't report findings it judges below the stated bar. Precision typically rises, but measured recall can fall even though underlying bug-finding ability has improved. Recommended prompt language:

> *"Report every issue you find, including ones you are uncertain about or consider low-severity. Do not filter for importance or confidence at this stage — a separate verification step will do that. Your goal here is coverage: it is better to surface a finding that later gets filtered out than to silently drop a real bug. For each finding, include your confidence level and an estimated severity so a downstream filter can rank them."*

This works even without an actual second step, but moving confidence filtering out of the finding stage often helps. If you do want single-pass self-filtering, be concrete about where the bar is rather than using qualitative terms like "important" — e.g. "report any bugs that could cause incorrect behavior, a test failure, or a misleading result; only omit nits like pure style or naming preferences." Iterate against a subset of evals to validate recall/F1 gains.

**Design and frontend defaults.** Claude Sonnet 5 may settle into a consistent default visual style on open-ended frontend and design briefs. Generic instructions ("don't use that color," "make it clean and minimal") tend to shift it to a different fixed palette rather than producing variety. Two approaches work reliably: **specify a concrete alternative** (the model follows explicit specs precisely — give the palette, typography, layout, and spacing), or **have the model propose options before building** (e.g. "Before building, propose 4 distinct visual directions tailored to this brief — bg hex / accent hex / typeface plus a one-line rationale — ask the user to pick one, then implement only that direction"). Because `temperature` isn't accepted on Claude Sonnet 5, the propose-then-pick approach is the recommended way to get meaningfully different design directions across runs. To steer away from generic AI-aesthetic patterns, a short directive in the system prompt also helps:

> *"NEVER use generic AI-generated aesthetics like overused font families (Inter, Roboto, Arial, system fonts), cliched color schemes (particularly purple gradients on white or dark backgrounds), predictable layouts and component patterns, and cookie-cutter design that lacks context-specific character. Use unique fonts, cohesive colors and themes, and animations for effects and micro-interactions."*

**Interactive coding products.** Token usage and behavior can differ between autonomous, asynchronous coding agents (single user turn) and interactive, synchronous coding agents (multiple user turns). To maximize both performance and token efficiency, use `effort: "xhigh"` or `"high"`, add autonomous features like an auto mode, and reduce the number of human interactions required. Specify task, intent, and constraints upfront in the first turn — well-specified initial prompts maximize autonomy and intelligence while minimizing extra token usage after user turns; ambiguous or progressively-revealed prompts tend to reduce token efficiency and sometimes performance.

### Claude Sonnet 5 Migration Checklist

Every item is tagged: **`[BLOCKS]`** items cause a 400 error or truncated output if missed; **`[TUNE]`** items are quality/cost adjustments — surface them to the user as recommendations.

- [ ] **[BLOCKS]** Update the `model=` string to `claude-sonnet-5`
- [ ] **[BLOCKS]** Replace `thinking: {type: "enabled", budget_tokens: N}` with `thinking: {type: "adaptive"}` + `output_config.effort` — the Sonnet 4.6 transitional escape hatch is gone
- [ ] **[BLOCKS]** Strip `temperature`, `top_p`, `top_k` from request construction (use system-prompt instructions for tone/variety instead)
- [ ] **[BLOCKS]** Bedrock only: pass `thinking: {type: "disabled"}` alongside forced `tool_choice` (`{type: "tool"}` / `{type: "any"}`) — not required on the Claude API or Vertex AI
- [ ] **[BLOCKS]** At `effort: "xhigh"` or `"max"`: set a large `max_tokens` (up to 128k, unchanged from Sonnet 4.6) so the model has room for thinking and tool calls — Sonnet-4.6-tuned limits may truncate equivalent output under the new tokenizer (symptom: `stop_reason: "max_tokens"`)
- [ ] **[TUNE]** Thinking-field omitted: adaptive is now the default (4.6 ran thinking-off) — either set `thinking: {type: "disabled"}` to preserve the old behavior, or revisit `max_tokens` for the added thinking spend
- [ ] **[TUNE]** `thinking.display` defaults to `"omitted"` (4.6 defaulted to `"summarized"`): if you stream reasoning to users, set `thinking: {type: "adaptive", display: "summarized"}` explicitly — the default streams empty-text thinking blocks (long pause before output)
- [ ] **[TUNE]** New tokenizer: re-run `count_tokens()` against `claude-sonnet-5` (~30% more tokens for the same text); revisit `max_tokens` and compaction triggers sized close to expected output length; re-baseline cost dashboards before reacting (per-token pricing unchanged)
- [ ] **[TUNE]** Effort: keep the `high` default; raise to `xhigh` for the hardest coding/agentic tasks; `medium` is a cost-saving step-down (≈ Sonnet 4.6 at `high`); reserve `low` for short, latency-sensitive, non-intelligence-sensitive tasks. If shallow reasoning shows up at `low`/`medium`, raise effort rather than prompting around it
- [ ] **[TUNE]** Thinking-off callers: try `thinking: {type: "adaptive"}` + `effort: "low"` instead of `disabled`; if `disabled` must stay, add an explicit tool-triggering nudge (the model is less tool-eager with thinking off)
- [ ] **[TUNE]** Tool usage: more agentic than 4.6 by default (reaches for tools and self-verification more readily) — `effort` is a lever (`high`/`xhigh` for more tool use); add explicit when/how triggering instructions for under-used tools
- [ ] **[TUNE]** Drop forced progress-update scaffolding ("after every N tool calls, summarize") — the default updates are higher quality; describe the desired update shape if it still needs tuning
- [ ] **[TUNE]** Re-baseline holdover style/tone/scope directives — instructions are followed literally; state the scope explicitly when one should apply broadly
- [ ] **[TUNE]** Verbosity-sensitive routes: tune response length via prompt (positive examples > "don't" instructions)
- [ ] **[TUNE]** Code-review harnesses with conservative-reporting instructions ("only high-severity", "don't nitpick"): switch to a coverage-first prompt (report everything with confidence + severity) and filter downstream — measured recall can otherwise fall even though bug-finding improved
- [ ] **[TUNE]** Open-ended frontend/design briefs: specify a concrete spec, or have the model propose 3–4 visual directions and pick one (the recommended substitute for `temperature`-driven variety)
- [ ] **[TUNE]** Interactive coding products: use `effort: "xhigh"`/`"high"`, add autonomous features (e.g. auto mode), and put task/intent/constraints in the first turn
- [ ] **[TUNE]** Vision-heavy / computer-use pipelines: leave images at native resolution up to 2576px long edge for the accuracy gain (downsample to control image-token cost if fidelity isn't needed); for computer use, 1080p screenshots are a good performance/cost balance with `computer_20251124`
- [ ] **[TUNE]** Security workloads: add handling for safeguard refusals (cyber-capable topics may now be declined where Sonnet 4.6 answered)

---

## Migrating to Claude Fable 5

> **Model IDs `claude-fable-5` and `claude-mythos-5` are authoritative as written here.** When the user asks to migrate to Claude Fable 5, write `model="claude-fable-5"` exactly; a Mythos Preview migrator in Project Glasswing writes `model="claude-mythos-5"` (everyone else: `claude-fable-5`). Do **not** WebFetch to verify — this guide is the source of truth for migration target IDs. The corresponding entries exist in `shared/models.md`.

Claude Fable 5 is Anthropic's most capable widely released model — for the most demanding reasoning and long-horizon agentic work. **Claude Mythos 5** (`claude-mythos-5`) offers the same capabilities, pricing, and API behavior through Project Glasswing (participation is the only way to access it), and succeeds the invitation-only **Claude Mythos Preview** (`claude-mythos-preview`). Everything in this section applies to both models — only the ID differs. Mythos Preview migrators in Project Glasswing target `claude-mythos-5`; everyone else targets `claude-fable-5`. 1M token context window by default (the maximum is also the default), up to 128K output tokens per request.

**Migrate to Claude Fable 5 only when the user explicitly chose it.** It is not the default Opus upgrade path — pricing is above Opus-tier. For "upgrade to the latest model" requests, the target remains `claude-opus-4-8`.

### Breaking changes (vs Opus-tier and Mythos Preview)

1. **Thinking is always on — remove all `thinking` configuration.** Adaptive thinking applies automatically whenever the `thinking` parameter is unset (an explicit `{type: "adaptive"}` is also accepted). Any other configuration is rejected: `thinking: {type: "disabled"}` and `{type: "enabled", budget_tokens: N}` both return a 400. `budget_tokens` has no replacement — the `output_config.effort` parameter is a separate output-level control, not a thinking budget.

   ```python
   # Before (Mythos Preview / older models)
   client.messages.create(
       model="claude-mythos-preview",
       max_tokens=16000,
       thinking={"type": "enabled", "budget_tokens": 10000},
       messages=[...],
   )

   # After (Claude Fable 5) — no thinking field at all
   client.messages.create(
       model="claude-fable-5",
       max_tokens=16000,
       output_config={"effort": "high"},
       messages=[...],
   )
   ```

2. **Assistant prefill is not supported.** Replace last-assistant-turn prefills with structured outputs (`output_config.format`) or system prompt instructions — same replacement patterns as the 4.6-family prefill removal above. (One exception: the fallback-credit prefill claim — the server accepts the echoed assistant message when redeeming a credit; see the refusal section below.)

3. **Interleaved scratchpad is not supported** (Mythos Preview migrators only). Inter-tool reasoning is returned in thinking blocks instead, which adaptive thinking produces automatically between tool calls.

### Thinking output on Claude Fable 5 and Claude Mythos 5

On Claude Fable 5 and Claude Mythos 5, the raw chain of thought is never returned. What you receive are **regular `thinking` blocks**, not encrypted blobs or `redacted_thinking`: `display: "summarized"` returns a readable summary of the reasoning, and with `"omitted"` — the default, same as Opus 4.8/4.7 — responses still include `thinking` blocks but the `thinking` field is an empty string. `display` controls visibility only; thinking happens and is billed the same under every setting. When continuing a conversation on the same model, pass thinking blocks back to the API **unchanged** (the standard multi-turn pattern; dropping or editing them breaks the turn).

When continuing on the same model, pass each thinking block back **exactly as received — including blocks whose `thinking` text is empty**. The API rejects blocks whose content has been *modified*, not blocks you have read; displaying the summary is fine, editing or reconstructing blocks is not.

Regular thinking blocks aren't origin-locked — they replay across models fine (the server renders them into the target model's prompt). Claude Fable 5/Claude Mythos 5 thinking is the exception: a thinking block from these models replayed to a different model is **dropped from the prompt** rather than rendered — typically silently (early-access builds hard-rejected with `invalid_request_error`; that broke workflows and was reverted before launch, but the new behavior is still rolling out, so don't build logic that depends on either outcome). The drop happens before the prompt is priced, so a dropped block **lowers `usage.input_tokens`** — you aren't billed for it, and there's nothing to strip for cost. Don't strip *regular* thinking blocks either: removing them can trigger ordering/signature 400s. Two rules for replay bodies stand regardless: fallback-credit retries must echo the refused body **unchanged**, and `fallback` blocks from a mid-output fallback stay where they appeared.

Related: a request that tries to elicit the model's internal reasoning *in the response text* can be refused with `stop_details.category: "reasoning_extraction"` — applications needing reasoning visibility should read the summarized `thinking` blocks instead of prompting for reasoning.

### Tokenizer — unchanged from Opus 4.8

Claude Fable 5 uses the **same tokenizer as Claude Opus 4.8** (the tokenizer introduced with Opus 4.7). Token counts are roughly unchanged when migrating from Opus 4.7/4.8 or from `claude-mythos-preview`; per-token pricing differs.

- Coming **from Opus 4.7/4.8 or `claude-mythos-preview`**: token counts are roughly unchanged. Re-baseline cost and latency on your own workloads for the per-token price difference.
- Coming **from Opus 4.6, Sonnet, Haiku, or older**: the Opus 4.7 tokenizer tokenizes the same content to roughly 1×–1.35× as many tokens (varies by content and workload shape). Do not reuse token counts, context-window budgets, or `max_tokens` settings measured on the old model; re-baseline with `count_tokens`.

To measure the difference on your own prompts, call `count_tokens` once with your current model and once with `model: "claude-fable-5"`, and compare the two `input_tokens` values.

### `refusal` stop reason — handle before reading content

Claude Fable 5 runs safety classifiers on incoming requests, targeting research biology and most cybersecurity content (Claude Fable 5 is not intended for those domains); benign adjacent work — security tooling, life-sciences tasks — can occasionally trigger false positives, which is why the fallback patterns below matter even for legitimate workloads. (Most Claude consumer surfaces ship with built-in Opus 4.8 fallbacks; API callers configure their own.) A declined request returns a **successful HTTP 200** with `stop_reason: "refusal"`, plus a `stop_details` object with the policy category (values such as `"cyber"`, `"bio"`, `"reasoning_extraction"`, `"frontier_llm"`, or `null` — treat `null` as a permanent valid state; see the refusal category table in the public docs for the full set). **Branch on `stop_reason`, never on `stop_details`** — `stop_details` is informational and can be `null` even on a refusal, and `explanation` is not guaranteed present. Note that classifier blocks and ordinary model refusals (the model itself declining) both surface as `stop_reason: "refusal"`; `stop_details.category` tells you which class you're handling, and therefore whether retrying on a fallback model is the right response. The classifier can fire **before any output** (empty `content` array; not billed at all — no input or output tokens, no rate-limit consumption) or **mid-stream** after partial output (already-streamed output is billed at normal rates — discard the partial output rather than treating it as complete). Code that reads `response.content[0]` unconditionally will break — check `stop_reason` first:

```python
response = client.messages.create(model="claude-fable-5", max_tokens=1024, messages=[...])
if response.stop_reason == "refusal":
    # classifiers declined; content is empty (pre-output) or partial (mid-stream)
    handle_refusal()
else:
    print(response.content[0].text)
```

**Default to opting in.** Fallbacks are not automatic on the API — a request without them simply stops on a refusal. Migrated and new Claude Fable 5 code should ship with pattern 1 below (pattern 2 on providers without server-side support) from day one, not as a later hardening step: emit the opt-in in the code, tell the user it's there, and remove it only if they decline.

Three ways to retry a refused request on another model, in order of preference:

**1. Server-side `fallbacks` parameter (beta: Claude API and Claude Platform on AWS) — preferred.** One round trip, a plain client, no client-side logic. Name substitute models (the only supported fallback target at launch is `claude-opus-4-8`, expansion expected); on a policy decline the API runs the next model on the same request and returns its answer, with credit-style repricing applied automatically. A `stop_reason: "refusal"` on the final response means the whole chain refused.

```python
response = client.beta.messages.create(
    model="claude-fable-5",
    max_tokens=1024,
    betas=["server-side-fallback-2026-06-01"],
    fallbacks=[{"model": "claude-opus-4-8"}],
    messages=[{"role": "user", "content": "Hello, Claude"}],
)

# Switch points: one fallback block per model that ran and declined this turn
for block in response.content:
    if block.type == "fallback":
        print(f"{block.from_.model} declined; {block.to.model} continued")

# Served-by signal: a fallback_message in usage.iterations means a fallback model
# ran; pair it with stop_reason to confirm the fallback served the response
# (a fallback model can also refuse). Covers sticky turns too.
fallback_ran = any(
    entry.type == "fallback_message" for entry in response.usage.iterations or []
)
if fallback_ran and response.stop_reason != "refusal":
    print(f"Served by {response.model}")
```

Key semantics:

- **Header must be exactly `server-side-fallback-2026-06-01`** — other `server-side-fallback-*` values reject the `fallbacks` param with a 400. The current header carries the *earliest* date of the series (`-2026-06-09` and `-2026-06-02` were earlier previews) — do not "correct" it to a newer-looking date. Rejected on the Batches API; not available on Amazon Bedrock, Vertex AI, or Microsoft Foundry (use pattern 2 there — the SDK middleware). Entries may override `max_tokens` per hop (bounding that attempt's own output independently of the top-level `max_tokens`); `thinking`, `output_config`, and `speed` overrides are rolling out (`speed` additionally requires its beta) — until your requests accept them, include only `model` and `max_tokens` in each entry. Entries must be distinct and must be in the requested model's `allowed_fallback_models` (published on `/v1/models` when the `server-side-fallback-2026-06-01` beta header is set — not yet visible under the `fallback-credit-*` header alone, and not exposed on Amazon Bedrock, Vertex AI, or Microsoft Foundry). The request *with an entry's overrides merged in* must be valid as a direct request to that entry's model.
- **Triggers on policy declines only** — rate limits, overloads, and server errors on the requested model are returned as-is, never falling back.
- **Reading the response:** a `fallback` content block (`{"type": "fallback", "from": {"model": ...}, "to": {"model": ...}}`) marks each switch point in `content`; the served-by signal is a `fallback_message` entry in `usage.iterations` (don't rely on the block — sticky-served turns have none). Top-level `model` names the model that produced the message.
- **Billing:** `usage.iterations` is the per-attempt source of truth; top-level `usage` covers only the attempt that produced the returned message. Declined-before-output attempts are reported but not billed; fallback attempts bill at the fallback model's rates. Each attempt claims the rate limits of the model that ran it — if the fallback model is rate-limited or overloaded, the fallback attempt is not made and the preceding refusal is returned instead with `stop_details.recommended_model` naming a model to retry directly (the recommendation is a hint, not a guarantee, and is `null` when no recommendation is available) — size fallback-model limits for expected refusal volume.
- **Sticky routing:** once a conversation falls back, later non-streaming requests with `fallbacks` are served directly by the fallback model for ~1 hour (best-effort; org-scoped content-hash record, not message content; not recorded for ZDR orgs). Handle the requested model being tried again at any time.
- **Echoing fallback turns back:** after a mid-output fallback, omit `thinking`, `redacted_thinking`, and `tool_use` blocks — plus any `server_tool_use` block without its matching `server_tool_result`, and any other unrecognized model-internal block type — that appear *before* the final `fallback` block; text blocks, paired server-tool blocks, and everything after the boundary echo normally. The `fallback` block itself is an ignored audit marker (keep or drop). Streaming: the retry happens on the same stream and already-received content is never invalidated — a pre-output block is seamless (`message_start` names the fallback model; the `fallback` block arrives as an ordinary `content_block_start`, first in `content` — there is no special SSE event type; note `message_start` arrives only after the declined attempt, so time-to-first-byte includes it), and a mid-stream block keeps the partial, marks the boundary with the block, and continues — only the partial's `text` blocks are passed to the fallback model as continuation context (other block types stay in `content` but aren't part of it). Sticky routing is **not consulted on streaming requests** in the initial release, so on streams the `fallback` block check is the complete signal; non-streaming mid-output declines omit the declined partial entirely.

**2. SDK client-side middleware — for providers without server-side fallbacks (Amazon Bedrock, Vertex AI, Microsoft Foundry).** Register it on the client and every `client.beta.messages` request (streaming included) retries refusals automatically, splicing the fallback model's events onto the open stream in the same wire shape as pattern 1 (a `fallback` content block at each boundary, per-hop `usage.iterations`). It is also a beta surface: the middleware sends the `fallback-credit-2026-06-01` header by default so retries are repriced via credit tokens (override with its `betas` option). `BetaFallbackState` pins follow-up turns to the model that accepted (the client-side analog of sticky routing) — reuse one state object per conversation:

```python
from anthropic import Anthropic, BetaFallbackState, BetaRefusalFallbackMiddleware

client = Anthropic(middleware=[BetaRefusalFallbackMiddleware([{"model": "claude-opus-4-8"}])])
state = BetaFallbackState()  # pins follow-ups to the model that accepted
with state:
    response = client.beta.messages.create(model="claude-fable-5", max_tokens=1024, messages=messages)
```

Create **one state per conversation** — it is the pinning scope; sharing one across conversations pins unrelated threads together, and a conversation without a state is never pinned. Per-language naming (from the GA SDK examples — don't improvise):

- **TypeScript**: `betaRefusalFallbackMiddleware([...])` in the client's `middleware` array; pass `{ fallbackState: state }` (a `BetaFallbackState`) as a request option.
- **Go**: `option.WithMiddleware(betafallback.BetaRefusalFallbackMiddleware([]anthropic.BetaFallbackParam{{Model: ...}}))` (package `lib/betafallback`); state via `betafallback.WithBetaFallbackState(&betafallback.BetaFallbackState{})` passed as a request option. Server-side equivalents: `Fallbacks: []anthropic.BetaFallbackParam{...}` + `anthropic.AnthropicBetaServerSideFallback2026_06_01`.
- **C#**: it's a *handler* — `new AnthropicClient { Handlers = [new BetaRefusalFallbackHandler { Fallbacks = [new(Model.ClaudeOpus4_8)] }] }` (namespace `Anthropic.Helpers`); state via `BetaFallbackState.Create()` scoped per call with `using (fallbackState.Use()) { ... }`. Server-side equivalents: `Fallbacks = [new(Model.ClaudeOpus4_8)]` + `AnthropicBeta.ServerSideFallback2026_06_01`.

For languages not listed (Java, Ruby, PHP) — or for a full runnable program in any language — each public SDK repo ships a fallbacks example under `examples/` (e.g. `examples/fallbacks.py`, `examples/refusal-fallback/`): WebFetch the repo from `shared/live-sources.md` § SDK Repositories rather than improvising the binding.

**3. Hand-rolled retry + fallback credit (raw HTTP, or SDKs without the middleware).** Detect the refusal via `stop_reason` and re-send the conversation as-is on a model with broader availability such as `claude-opus-4-8` (Claude Fable 5's thinking blocks are silently ignored by other models — no stripping required); keep using the fallback model for subsequent turns. **Fallback credit** (beta: Claude API, Claude Platform on AWS, Amazon Bedrock, Vertex AI, and Microsoft Foundry) makes those retries cheaper. Prompt caches are per-model, so a plain retry pays cold cache-writes on the new model. With the `fallback-credit-2026-06-01` beta header (send it on both the original request and the retry), a refusal's `stop_details` carries `fallback_credit_token` (opaque; `null` when unavailable) and `fallback_has_prefill_claim`. Echo the token as the top-level `fallback_credit_token` request parameter on the retry (typed in the GA SDKs; on a pre-GA SDK pass it via `extra_body`) and the previously-cached span bills at cache-read rates — the retry costs what it would have if the conversation had been on that model all along. Rules: the retry body must match the refused request **exactly** in every prompt-shaping field (`system`, `messages`, `tools`, `tool_choice`, `thinking` — do **not** strip thinking blocks when redeeming a credit — the server handles them); the retry model must be in the refused model's `allowed_fallback_models`; the token expires in 5 minutes; Batches results carry no tokens. If `fallback_has_prefill_claim` is `true`, append one assistant message echoing the refused response's `content` — the retry model continues from where the refused model stopped (and completed server-tool work isn't re-run). When echoing, strip trailing whitespace from a final `text` block (the prefill validator rejects it; the credit match tolerates that edit), after omitting any unpaired `tool_use` blocks. On a 400, fall back to the unchanged body with the token; on a 400 naming `fallback_credit_token`, retry without it (credit forfeited).

**Migrating code built on the v1 preview.** If the code you're editing carries any of these markers, it targets the discontinued early-access surface — migrate it to the v2 shapes above, and ship the header and parameter changes together (the v1 parameter shape under the v2 header is a 400):

| v1 marker (replace) | v2 |
|---|---|
| `server-side-fallback-2026-06-09` / `-2026-06-02` header | `server-side-fallback-2026-06-01` |
| `fallback: {model, on_partial}` single object | `fallbacks: [{model, ...}]` array (1–3); `on_partial` no longer exists — partial-output behavior is fixed (streams keep the partial; non-streaming omits it). Unknown keys in an entry are a 400 |
| Top-level `response.fallback` object (`from_model`, `reason`) | Never emitted — read `fallback` content blocks (switch points, no `reason` field) and `usage.iterations` (served-by) |
| `event: fallback` SSE with discard indices | No dedicated event; streamed content is never invalidated — the switch arrives as an ordinary `content_block_start`/`stop` pair of type `fallback` |
| `fallback_primary` / `fallback_retry` iteration types | Blocked attempts are plain `message` entries; the serving attempt is `fallback_message` |
| `reason: "sticky"` | No reason field — sticky turns carry no block; detect via `fallback_message` in `usage.iterations` + `response.model` |
| `recommended_model` meaning "primary served the refusal" | Now populated only when the fallback attempt *couldn't run* (rate-limited/overloaded) — its presence means a direct retry on that model may succeed, not that it refused too |

### Data retention requirement

Claude Fable 5 requires **30-day data retention** and is not available under zero data retention. Requests from an organization whose data-retention configuration doesn't meet the requirement return `400 invalid_request_error` — if a migration suddenly 400s with no obvious request problem, check the org's retention configuration before debugging the payload. On Amazon Bedrock, Google Vertex AI, and Microsoft Foundry, data-retention requirements are set by each platform.

### What carries over unchanged

Same Messages API and tool-use patterns as Opus-tier and Mythos Preview. Supported at launch: `output_config.effort` (`low`/`medium`/`high`/`xhigh`/`max`), Task Budgets (beta, `task-budgets-2026-03-13` header), compaction (beta, `compact-2026-01-12` header), the memory tool, tool-call clearing via context editing, and high-resolution vision (no downscaling cap, as on Opus 4.7+).

### Behavioral shifts (prompt-tunable)

None of these are API-breaking, but they're where migrated workloads feel different. Claude Fable 5's biggest gains are on work *above* what prior models could do (long-horizon autonomous runs, first-shot implementations of well-specified systems, end-to-end enterprise deliverables — financial analysis, spreadsheets, slides, docs — code review/debugging and repository-history search, vision on dense or degraded images — it's explicitly trained to use bash and crop tools on flipped/blurry/noisy inputs — navigating ambiguity, parallel sub-agent delegation and collaboration — it reliably sustains ongoing communications with long-running sub-agents and peer agents; note bug-finding gains exclude security-focused analysis, where the cyber classifiers apply) — don't evaluate it only on workloads older models already handled.

**Longer turns by default — the biggest structural shift.** Individual requests on hard tasks can run many minutes at higher effort (a 15-minute single request is normal when the task involves gathering context, building, and self-verifying). Before migrating, plan timeouts, streaming, and user-facing progress indicators; structure work so callers check in on runs asynchronously rather than blocking inside one request. On ambiguous tasks Claude Fable 5 may need a small nudge to avoid overplanning:

> When you have enough information to act, act. Do not re-derive facts already established in the conversation, re-litigate a decision the user has already made, or narrate options you will not pursue in user-facing messages. If you are weighing a choice, give a recommendation, not an exhaustive survey. This does not apply to thinking blocks.

**Consider all effort levels.** `output_config.effort` is the primary intelligence/latency/cost control. Recommended defaults: `high` for most tasks, `xhigh` for the most capability-sensitive workloads, `medium`/`low` for routine work. Lower effort settings — including `low` — still perform very well on Claude Fable 5, often exceeding the `xhigh` or even `max` performance of previous models. Reduce effort if a task completes correctly but takes longer than necessary, or for a quicker interactive working style. At higher effort on routine work, Claude Fable 5 can gather context and deliberate beyond what the task needs (the flip side: higher effort buys excellent verification behavior and the most rigorous outputs). To prevent unrequested tidying or refactoring at higher effort:

> Don't add features, refactor, or introduce abstractions beyond what the task requires. A bug fix doesn't need surrounding cleanup and a one-shot operation usually doesn't need a helper. Don't design for hypothetical future requirements - do the simplest thing that works well. Avoid premature abstraction. Avoid half-finished implementations either. Don't add error handling, fallbacks, or validation for scenarios that cannot happen. Trust internal code and framework guarantees. Only validate at system boundaries (user input, external APIs). Don't use feature flags or backwards-compatibility shims when you can just change the code.

**Instruction following is strong — use it.** Claude Fable 5 is very responsive to explicit communication-style sections in system prompts; invest in them rather than fighting output style downstream. Un-steered — especially at higher effort — it can elaborate beyond what the task needs: heavily-structured PR descriptions, sections on alternatives that weren't chosen, comments narrating what the next line does. You don't need to enumerate these behaviors by name; a brief instruction is just as effective:

> Lead with the outcome. Your first sentence after finishing should answer "what happened" or "what did you find" — the thing the user would ask for if they said "just give me the TLDR." Supporting detail and reasoning come after. Being readable and being concise are different things, and readability matters more. The way to keep output short is to be selective about what you include (drop details that don't change what the reader would do next), not to compress the writing into fragments, abbreviations, arrow chains like A → B → fails, or jargon.

**Ground progress claims on long runs.** Require progress claims to be audited against tool results — in testing this nearly eliminated fabricated status reports on tasks designed to elicit them:

> Before reporting progress, audit each claim against a tool result from this session. Only report work you can point to evidence for; if something is not yet verified, say so explicitly. Report outcomes faithfully: if tests fail, say so with the output; if a step was skipped, say that; when something is done and verified, state it plainly without hedging.

**State boundaries explicitly.** Claude Fable 5 sometimes takes unrequested-but-adjacent actions (e.g. composing an email straight to drafts, creating backup git branches). Define what it should *not* do:

> When the user is describing a problem, asking a question, or thinking out loud rather than requesting a change, the deliverable is your assessment. Report your findings and stop. Don't apply a fix until they ask for one. Before running a command that changes system state — restarts, deletes, config edits — check that the evidence actually supports that specific action. A signal that pattern-matches to a known failure may have a different cause.

**Let it delegate — asynchronously.** Parallel sub-agents are dependable on Claude Fable 5 — instead of suppressing delegation (a common prior-model guardrail), use sub-agents frequently and give explicit guidance on *when* delegation is desirable. Sub-agents that communicate **asynchronously** with the orchestrator outperform spawn-and-block: long-lived agents keep their context instead of re-establishing it per subtask (cache-read savings), the orchestrator isn't bottlenecked on the slowest sub-agent, and context persists across subtasks.

> Delegate independent subtasks to sub-agents and keep working while they run. Intervene if a sub-agent goes off track or is missing relevant context.

**Give it a memory surface.** Claude Fable 5 performs notably better when it can write learnings somewhere for future reference — even a plain `.md` file. Tell it where, tell it to consult that file in future sessions, and give it a format:

> Store one lesson per file with a one-line summary at the top. Record corrections and confirmed approaches alike, including why they mattered. Don't save what the repo or chat history already records; update an existing note rather than creating a duplicate; delete notes that turn out to be wrong.

**Rare: early stopping.** Deep into long sessions it can occasionally end a turn with a text-only statement of intent ("I'll now run X") without the tool call, or ask permission it doesn't need. A "continue" recovers it interactively; for autonomous pipelines add a system reminder:

> You are operating autonomously. The user is not watching in real time and cannot answer questions mid-task, so asking 'Want me to…?' or 'Shall I…?' will block the work. For reversible actions that follow from the original request, proceed without asking. Offering follow-ups after the task is done is fine; asking permission after already discussing with the user before doing the work is not. Before ending your turn, check your last paragraph. If it is a plan, an analysis, a question, a list of next steps, or a promise about work you have not done ('I'll…', 'let me know when…'), do that work now with tool calls. End your turn only when the task is complete or you are blocked on input only the user can provide.

**Rare: context anxiety.** In very long sessions it can worry about running out of context — suggesting a new session or trimming its own work — most often when the harness surfaces a remaining-token countdown. Avoid showing explicit context-budget counts; if you must:

> You have ample context remaining. Do not stop, summarize, or suggest a new session on account of context limits – continue the work.

**Give the reason, not just the request.** Claude Fable 5 performs better when it understands the intent behind a request — it connects the task to relevant information rather than inferring intent on its own. This matters most for long-running agents juggling context from disparate workstreams:

> I'm working on [the larger task] for [who it's for]. They need [what the output enables]. With that in mind: [request].

**Readability in long agentic sessions.** Deep into extended conversations (many tool calls, large working context) Claude Fable 5 can produce text users find hard to follow — dense arrow-chain shorthand, implementation-level detail, references to thinking the user never saw. A communication-style addendum strongly mitigates this; adapt:

> Terse shorthand is fine between tool calls (that's you thinking out loud, and brevity there is good). Your final summary is different: it's for a reader who didn't see any of that. If you've been working for a while without the user watching - overnight, across many tool calls, since they last spoke - your final message is their first look at any of it. Write it as a re-grounding, not a continuation of your working thread: the outcome first, then the one or two things you need from them, each explained as if new. The vocabulary you built up while working is yours, not theirs; leave it behind unless you re-introduce it. When you write the summary at the end, drop the working shorthand. Write complete sentences. Spell out terms instead of abbreviating them. Don't use arrow chains, hyphen-stacked compounds, or labels you made up earlier — the reader doesn't have the context to decode them. When you mention files, commits, flags, or other identifiers, give each one its own plain-language clause saying what it is or what changed — never pack several into one parenthesized run or slash-separated list. Open with the outcome: one sentence on what happened or what you found. Then the supporting detail. If you have to choose between short and clear, choose clear.

### Long-running agent recommendations

- **Make self-verification explicit.** For long-running builds, instruct it to establish and run its own checking harness on a cadence ("Establish a method for checking your own work as you build; run it every [interval], verifying against the specification with sub-agents"). Separate fresh-context verifier sub-agents tend to outperform self-critique.
- **De-prescribe migrated prompts and skills.** Prompts and skills written for prior models are often too prescriptive for Claude Fable 5 and *reduce* output quality. After migrating, A/B the workload with older step-by-step scaffolding removed — prefer stating the goal and constraints over enumerating the steps. Claude Fable 5 is also good at updating skills on the fly from what it learns mid-task — let it.
- **Start at the top of your difficulty range.** The teams with the best early-access outcomes gave it their hardest unsolved problems first — have it scope the problem, ask questions, then execute.
- **Add a `send_to_user` tool for verbatim mid-task delivery.** When an asynchronous agent must deliver something the user sees *exactly as written* mid-run (a deliverable, a progress update with specific numbers, a direct answer), give it a client-side tool whose input you render directly in the UI — tool inputs are never summarized, so content arrives intact. Return a simple acknowledgement as the tool result:

```json
{
  "name": "send_to_user",
  "description": "Display a message directly to the user. Use this for progress updates, partial results, or content the user must see exactly as written before the task finishes.",
  "input_schema": {
    "type": "object",
    "properties": {
      "message": { "type": "string", "description": "The content to display to the user." }
    },
    "required": ["message"]
  }
}
```

For agents that only narrate routine progress, the model's default progress narration is typically adequate without this tool.

### Claude Fable 5 Migration Checklist

- [ ] **[BLOCKS]** Update the `model=` string to `claude-fable-5` (`claude-mythos-5` for Mythos Preview migrators in Project Glasswing)
- [ ] **[BLOCKS]** Remove `thinking: {type: "disabled"}` (errors on Claude Fable 5)
- [ ] **[BLOCKS]** Replace assistant prefill with structured outputs or system prompt instructions
- [ ] **[BLOCKS]** Confirm the org meets the 30-day data-retention requirement (ZDR orgs get `400 invalid_request_error` on every request)
- [ ] **[BLOCKS]** Remove all other `thinking` configuration (`{type: "enabled", budget_tokens: N}` returns a 400, same as on Opus 4.7/4.8); control depth with `output_config.effort` instead
- [ ] **[BLOCKS]** If thinking content is surfaced to users or stored in logs: add `thinking: {type: "adaptive", display: "summarized"}` (the default is `"omitted"` — otherwise the rendered text is empty)
- [ ] **[TUNE]** Re-baseline cost and latency on your own workloads — token counts are roughly unchanged from Opus 4.7/4.8 and Mythos Preview (same tokenizer); per-token pricing differs. Coming from Opus 4.6, Sonnet, Haiku, or older, token counts differ — use `count_tokens` with each model to compare
- [ ] **[TUNE]** Add `stop_reason == "refusal"` handling before reading `response.content` (pre-output: empty + unbilled; mid-stream: partial output billed — discard); opt into a fallback by default — server-side `fallbacks` (`server-side-fallback-2026-06-01`, Claude API and Claude Platform on AWS) where available, otherwise the SDK middleware or fallback credit (`fallback-credit-2026-06-01`, exact body); a bare client-side replay (history as-is; other models drop Fable's thinking blocks) is the floor, not the recommendation
- [ ] **[TUNE]** If you surfaced thinking text to users, plan for the thinking output change — the raw chain of thought is never returned; render the `display: "summarized"` summary (per the [BLOCKS] item above); pass blocks back unchanged on the same model; other models drop them from the prompt (unbilled)
- [ ] **[TUNE]** Plan for minutes-long turns: timeouts, streaming, async check-ins, progress UX (see Behavior changes above)
- [ ] **[TUNE]** Run an effort sweep including low/medium for routine workloads; add the no-tidying instruction if higher effort produces unrequested refactors
- [ ] **[TUNE]** A/B with prior-model scaffolding removed — over-prescriptive prompts/skills reduce Claude Fable 5 output quality

---

## Verify the Migration

After updating, spot-check that the new model is actually being used. Replace `YOUR_TARGET_MODEL` with the model string you migrated to (e.g. `claude-fable-5`, `claude-opus-4-8`, `claude-opus-4-7`, `claude-sonnet-5`, `claude-sonnet-4-6`, `claude-haiku-4-5`) and keep the assertion prefix in sync:

```python
YOUR_TARGET_MODEL = "claude-opus-4-8"  # or "claude-opus-4-7", "claude-sonnet-5", "claude-sonnet-4-6", "claude-haiku-4-5"
response = client.messages.create(model=YOUR_TARGET_MODEL, max_tokens=64, messages=[...])
assert response.model.startswith(YOUR_TARGET_MODEL), response.model
```

For rate-limit headroom changes, pricing, or capability deltas (vision, structured outputs, effort support), query the Models API:

```python
m = client.models.retrieve(YOUR_TARGET_MODEL)
m.max_input_tokens, m.max_tokens
m.capabilities["effort"]["max"]["supported"]
```

See `shared/models.md` for the full capability lookup pattern.
