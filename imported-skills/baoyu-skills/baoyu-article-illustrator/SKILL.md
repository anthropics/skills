---
name: baoyu-article-illustrator
description: Analyzes article structure, identifies positions requiring visual aids, generates illustrations with Type × Style × Palette three-dimension approach. Use when user asks to "illustrate article", "add images", "generate images for article", or "为文章配图".
version: 1.117.4
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-article-illustrator
---

# Article Illustrator

Analyze articles, identify illustration positions, generate images with Type × Style × Palette consistency.

## User Input Tools

When this skill prompts the user, follow this tool-selection rule (priority order):

1. **Prefer built-in user-input tools** exposed by the current agent runtime — e.g., `AskUserQuestion`, `request_user_input`, `clarify`, `ask_user`, or any equivalent.
2. **Fallback**: if no such tool exists, emit a numbered plain-text message and ask the user to reply with the chosen number/answer for each question.
3. **Batching**: if the tool supports multiple questions per call, combine all applicable questions into a single call; if only single-question, ask them one at a time in priority order.

Concrete `AskUserQuestion` references below are examples — substitute the local equivalent in other runtimes.

## Image Generation Tools

When this skill needs to render an image, resolve the backend in this order:

1. **Current-request override** — if the user names a specific backend in the current message, use it.
2. **Saved preference** — if `EXTEND.md` sets `preferred_image_backend` to a backend available right now, use it.
3. **Auto-select** (when the preference is `auto`, unset, or the pinned backend isn't available):
   - **Codex (`imagegen`)** — first, inspect your available-skills / tool inventory. If a skill named `imagegen` is listed, you are running inside Codex and MUST use it: invoke via the `Skill` tool with `skill: "imagegen"`, passing the saved prompt file's content (plus output path and aspect ratio per Codex `imagegen`'s own args). Codex `imagegen` is the official raster backend in that runtime and outranks any non-native skill (e.g., `baoyu-image-gen`) unless the user has explicitly pinned a different `preferred_image_backend`.
   - **Codex via `codex exec` (`codex-imagegen`)** — if the current runtime exposes no native `imagegen` skill but the `codex` CLI is on `PATH` with an active `codex login`, route through `baoyu-image-gen --provider codex-cli` (preferred), or — if baoyu-image-gen is unavailable — invoke the bundled wrapper directly. Details, parameters, and the runtime-discovery procedure live in [references/codex-imagegen.md](references/codex-imagegen.md) — load that file only when this branch is selected.
   - **Cursor (`GenerateImage`)** — if the runtime exposes a native `GenerateImage` tool, you are running inside Cursor and it outranks any non-native skill the same way Codex `imagegen` does. Two hard caveats: (a) it has no aspect-ratio parameter — state the target aspect ratio / dimensions explicitly in the prompt text passed as `description`; (b) it does not accept an output directory — it saves to a tool-managed location, so after generation copy/move the file to the skill's expected output path (e.g., `outputs/.../NN-xxx.png`). Reference images go in `reference_image_paths`.
   - **Other runtime-native tools** — if the runtime exposes a different native image tool (e.g., Hermes `image_generate`), use it the same way.
   - Otherwise, if exactly one non-native backend is installed (e.g., `baoyu-image-gen`), use it.
   - Otherwise (multiple non-native backends with no runtime-native tool), ask the user once — batch with any other initial questions.
4. **If none are available**, tell the user and ask how to proceed.

**⛔ Never substitute SVG, HTML, canvas, or other code-based rendering for raster image generation.** Codex `imagegen`'s own description says it should be used "when the output should be a bitmap asset rather than repo-native code or vector." If you cannot resolve a raster backend via step 3, fall through to step 4 and ask the user — do **not** silently emit SVG, write inline `<svg>` markup, or produce HTML/CSS art as a substitute. This applies even if the article/section seems "diagram-like": the consumer skill calling this rule has already decided that a raster image is what it needs.

**⛔ Never repair rendered text by painting over a generated bitmap.** Do not use ImageMagick, Pillow, Canvas, SVG, HTML/CSS, OCR scripts, or any other programmatic overlay to cover, rewrite, erase, stroke, or replace labels, captions, or any other text inside an already generated illustration. If text is wrong or unclear, regenerate from a corrected prompt, redraw with less or no on-image text, or ask the user which imperfect candidate to keep.

Setting `preferred_image_backend: ask` forces the step-3 prompt every run regardless of available backends. Users change the pinned backend via the `## Changing Preferences` section below.

**Prompt file requirement (hard)**: write each image's full, final prompt to a standalone file under `prompts/` (naming: `NN-{type}-[slug].md`) BEFORE invoking any backend. The backend receives the prompt file (or its content); the file is the reproducibility record and lets you switch backends without regenerating prompts.

Concrete tool names (`imagegen`, `GenerateImage`, `image_generate`, `baoyu-image-gen`) above are examples — substitute the local equivalents under the same rule.

## Batch Generation Policy

After every prompt file for the run has been saved and verified, generate images in batches by default.

Priority order:

1. Use the chosen backend's native batch / multi-task interface if it exists. Each task must keep its own prompt file, output path, aspect ratio, and direct reference images.
2. If no native batch interface exists but the runtime can issue parallel tool calls, dispatch up to `generation_batch_size` images at a time. Default: `4`. An explicit user request in the current message, such as `--batch-size 4` or "并行4张一起生成", overrides EXTEND.md.
3. If neither native batch nor parallel tool calls are available, generate sequentially.

Rules:

- Never start the first batch until all prompt files for that batch exist on disk.
- Retry failed items once without regenerating successful items.
- Do not use subagents merely to parallelize image rendering. Use subagents only for separate prompt iteration or creative exploration.

## Confirmation Policy

Default behavior: **confirm before generation**.

- Treat explicit skill invocation, a file path, matched signals/presets, and `EXTEND.md` defaults as **recommendation inputs only**. None of them authorizes skipping confirmation.
- Do **not** start Step 4 or later until the user completes Step 3.
- Skip confirmation only when the current request explicitly says to do so, for example: "直接生成", "不用确认", "跳过确认", "按默认出图", or equivalent wording.
- If confirmation is skipped explicitly, state the assumed type / density / style / palette / language / backend in the next user-facing update before generating.

## Reference Images

Users may supply reference images via `--ref <files...>` or by providing file paths / pasting images in conversation. Refs guide style, palette, composition, or subject for specific illustrations.

Full detection, storage, and processing rules are in [references/workflow.md](references/workflow.md) (Step 1.0 saves to `references/NN-ref-{slug}.{ext}`; Step 5.3 processes per-illustration usage `direct | style | palette`). When the chosen backend supports batch input, `direct`-usage entries in each prompt file's `references:` frontmatter should be propagated into its batch payload so backends can pass them through (e.g. `baoyu-image-gen` accepts `ref` per task).

## Three Dimensions

| Dimension | Controls | Examples |
|-----------|----------|----------|
| **Type** | Information structure | infographic, scene, flowchart, comparison, framework, timeline |
| **Style** | Rendering approach | notion, warm, minimal, blueprint, watercolor, elegant |
| **Palette** | Color scheme (optional) | macaron, warm, neon — overrides style's default colors |

Combine freely: `--type infographic --style vector-illustration --palette macaron`

Or use presets: `--preset edu-visual` → type + style + palette in one flag. See [Style Presets](references/style-presets.md).

## Types

| Type | Best For |
|------|----------|
| `infographic` | Data, metrics, technical |
| `scene` | Narratives, emotional |
| `flowchart` | Processes, workflows |
| `comparison` | Side-by-side, options |
| `framework` | Models, architecture |
| `timeline` | History, evolution |

## Styles

See [references/styles.md](references/styles.md) for Core Styles, full gallery, and Type × Style compatibility.

## Workflow

```
- [ ] Step 1: Pre-check (EXTEND.md, references, config)
- [ ] Step 2: Analyze content
- [ ] Step 3: Confirm settings (AskUserQuestion)
- [ ] Step 4: Generate outline
- [ ] Step 5: Generate images
- [ ] Step 6: Finalize
```

### Step 1: Pre-check

**1.5 Load Preferences (EXTEND.md) ⛔ BLOCKING**

Check EXTEND.md in priority order — the first one found wins:

| Priority | Path | Scope |
|----------|------|-------|
| 1 | `.baoyu-skills/baoyu-article-illustrator/EXTEND.md` | Project |
| 2 | `${XDG_CONFIG_HOME:-$HOME/.config}/baoyu-skills/baoyu-article-illustrator/EXTEND.md` | XDG |
| 3 | `$HOME/.baoyu-skills/baoyu-article-illustrator/EXTEND.md` | User home |

| Result | Action |
|--------|--------|
| Found | Read, parse, display summary |
| Not found | ⛔ Run [first-time-setup](references/config/first-time-setup.md) |

Full procedures: [references/workflow.md](references/workflow.md#step-1-pre-check)

### Step 2: Analyze

| Analysis | Output |
|----------|--------|
| Content type | Technical / Tutorial / Methodology / Narrative |
| Purpose | information / visualization / imagination |
| Core arguments | 2-5 main points |
| Positions | Where illustrations add value |

**CRITICAL**: Metaphors → visualize underlying concept, NOT literal image.

Full procedures: [references/workflow.md](references/workflow.md#step-2-setup--analyze)

### Step 3: Confirm Settings ⚠️

**Hard gate**: this step is mandatory per the [Confirmation Policy](#confirmation-policy) — Steps 4+ cannot start until the user confirms here (or explicitly opts out with "直接生成" / equivalent wording in the current request).

**ONE AskUserQuestion, max 4 Qs. Q1-Q2 REQUIRED. Q3 required unless preset chosen.**

| Q | Options |
|---|---------|
| **Q1: Preset or Type** | [Recommended preset], [alt preset], or manual: infographic, scene, flowchart, comparison, framework, timeline, mixed |
| **Q2: Density** | minimal (1-2), balanced (3-5), per-section (Recommended), rich (6+) |
| **Q3: Style** | [Recommended], minimal-flat, sci-fi, hand-drawn, editorial, scene, poster, Other — **skip if preset chosen** |
| Q4: Palette | Default (style colors), macaron, warm, neon — **skip if preset includes palette or preferred_palette set** |
| Q5: Language | When article language ≠ EXTEND.md setting |

Full procedures: [references/workflow.md](references/workflow.md#step-3-confirm-settings-)

### Step 4: Generate Outline

Save `outline.md` with frontmatter (type, density, style, palette, image_count) and entries:

```yaml
## Illustration 1
**Position**: [section/paragraph]
**Purpose**: [why]
**Visual Content**: [what]
**Filename**: 01-infographic-concept-name.png
```

Full template: [references/workflow.md](references/workflow.md#step-4-generate-outline)

### Step 5: Generate Images

⛔ **BLOCKING: Prompt files MUST be saved before ANY image generation.** This is a hard requirement regardless of which backend is chosen — the prompt file is the reproducibility record.

1. For each illustration, create a prompt file per [references/prompt-construction.md](references/prompt-construction.md)
2. Save to `prompts/NN-{type}-{slug}.md` with YAML frontmatter
3. Prompts **MUST** use type-specific templates with structured sections (ZONES / LABELS / COLORS / STYLE / ASPECT)
4. LABELS **MUST** include article-specific data: actual numbers, terms, metrics, quotes
5. **DO NOT** pass ad-hoc inline prompts to `--prompt` without saving prompt files first
6. Select the backend via the `## Image Generation Tools` rule at the top: use whatever is available; if multiple, ask the user once. Do this once per session before any generation.
   - **`codex-imagegen` invocation**: when the rule resolves to `codex-imagegen`, see [references/codex-imagegen.md](references/codex-imagegen.md) for the invocation contract (preferred `baoyu-image-gen --provider codex-cli` path, runtime wrapper discovery, parameter notes, stdout schema, batch semantics).
7. **Execution strategy**: Generate in batches per the `## Batch Generation Policy`: backend native batch first, runtime parallel tool calls second, sequential only as fallback. Default batch size is 4 unless EXTEND.md or the current request overrides it.
8. Process references (`direct`/`style`/`palette`) per prompt frontmatter
9. Apply watermark if EXTEND.md enabled
10. Generate from saved prompt files; retry once on failure

Full procedures: [references/workflow.md](references/workflow.md#step-5-generate-images)

### Step 6: Finalize

Insert `![description]({relative-path}/NN-{type}-{slug}.png)` after paragraphs. Path computed relative to article file based on output directory setting.

```
Article Illustration Complete!
Article: [path] | Type: [type] | Density: [level] | Style: [style] | Palette: [palette or default]
Images: X/N generated
```

## Output Directory

Output directory is determined by `default_output_dir` in EXTEND.md (set during first-time setup):

| `default_output_dir` | Output Path | Markdown Insert Path |
|----------------------|-------------|----------------------|
| `imgs-subdir` (default) | `{article-dir}/imgs/` | `imgs/NN-{type}-{slug}.png` |
| `same-dir` | `{article-dir}/` | `NN-{type}-{slug}.png` |
| `illustrations-subdir` | `{article-dir}/illustrations/` | `illustrations/NN-{type}-{slug}.png` |
| `independent` | `illustrations/{topic-slug}/` | `illustrations/{topic-slug}/NN-{type}-{slug}.png` (relative to cwd) |

All auxiliary files (outline, prompts) are saved inside the output directory:

```
{output-dir}/
├── outline.md
├── prompts/
│   └── NN-{type}-{slug}.md
└── NN-{type}-{slug}.png
```

When input is **pasted content** (no file path), always uses `illustrations/{topic-slug}/` with `source-{slug}.{ext}` saved alongside.

**Slug**: 2-4 words, kebab-case. **Conflict**: append `-YYYYMMDD-HHMMSS`.

## Modification

| Action | Steps |
|--------|-------|
| Edit | Update prompt → Regenerate → Update reference |
| Add | Position → Prompt → Generate → Update outline → Insert |
| Delete | Delete files → Remove reference → Update outline |

Text correction policy:

- If any rendered text (labels, captions, etc.) is misspelled, garbled, hard to read, or visually weak, do not patch the bitmap with code.
- For text-correction regenerations, write a new prompt file and a new output path so the flawed candidate is preserved for comparison.
- Post-processing is limited to crop, resize, compression, or format conversion that does not alter text or the main composition.

## References

| File | Content |
|------|---------|
| [references/workflow.md](references/workflow.md) | Detailed procedures |
| [references/usage.md](references/usage.md) | Command syntax |
| [references/styles.md](references/styles.md) | Style gallery + Palette gallery |
| [references/style-presets.md](references/style-presets.md) | Preset shortcuts (type + style + palette) |
| [references/prompt-construction.md](references/prompt-construction.md) | Prompt templates |
| [references/config/first-time-setup.md](references/config/first-time-setup.md) | First-time setup |

## Changing Preferences

EXTEND.md lives at the first matching path listed in Step 1.5. Three ways to change it:

- **Edit directly** — open EXTEND.md and change fields. Full schema: `references/config/preferences-schema.md`.
- **Reconfigure interactively** — delete EXTEND.md (or ask "reconfigure baoyu-article-illustrator preferences" / "重新配置"). The next run re-triggers first-time setup.
- **Common one-line edits**:
  - `preferred_image_backend: auto` — default; runtime-native tool wins, falls back to the only installed backend, asks only if multiple non-native are present.
  - `preferred_image_backend: codex-imagegen` — pin to Codex's built-in.
  - `preferred_image_backend: baoyu-image-gen` — pin to the baoyu-image-gen skill.
  - `preferred_image_backend: ask` — confirm backend every run.
  - `generation_batch_size: 4` — default number of images to render concurrently when the runtime supports parallel generation calls.
  - `preferred_type: infographic`, `preferred_style: notion`, `preferred_palette: macaron`, `language: zh`.
  - `default_output_dir: imgs-subdir` — where to write generated images relative to the article.
