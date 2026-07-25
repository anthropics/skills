---
name: baoyu-slide-deck
description: Generates professional slide deck images from content. Creates outlines with style instructions, then generates individual slide images. Use when user asks to "create slides", "make a presentation", "generate deck", "slide deck", or "PPT".
version: 1.117.4
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-slide-deck
    requires:
      anyBins:
        - bun
        - npx
---

# Slide Deck Generator

Transform content into professional slide deck images. The deck is designed for **reading and sharing** (self-explanatory slides, logical scroll flow, social-media-friendly) rather than live presentation — that assumption drives every layout and density decision below.

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

**⛔ Never repair rendered text by painting over a generated bitmap.** Do not use ImageMagick, Pillow, Canvas, SVG, HTML/CSS, OCR scripts, or any other programmatic overlay to cover, rewrite, erase, stroke, or replace slide titles, bullets, or any other text inside an already generated slide image. If text is wrong or unclear, regenerate from a corrected prompt, simplify the slide's on-image text, or ask the user which imperfect candidate to keep.

Setting `preferred_image_backend: ask` forces the step-3 prompt every run regardless of available backends. Users change the pinned backend via the `## Changing Preferences` section below.

**Prompt file requirement (hard)**: write each image's full, final prompt to a standalone file under `prompts/` (naming: `NN-slide-[slug].md`) BEFORE invoking any backend. The file is the reproducibility record and lets you switch backends without regenerating prompts.

Concrete tool names (`imagegen`, `GenerateImage`, `image_generate`, `baoyu-image-gen`) above are examples — substitute the local equivalents under the same rule.

## Batch Generation Policy

After every prompt file for the current generation group has been saved and verified, generate slide images in batches by default.

Priority order:

1. Use the chosen backend's native batch / multi-task interface if it exists. Each task must keep its own prompt file, output path, aspect ratio, session ID, and direct reference images.
2. If no native batch interface exists but the runtime can issue parallel tool calls, dispatch up to `generation_batch_size` slide images at a time. Default: `4`. An explicit user request in the current message, such as `--batch-size 4` or "并行4张一起生成", overrides EXTEND.md.
3. If neither native batch nor parallel tool calls are available, generate sequentially.

Rules:

- Never start the first batch until all selected slide prompt files exist on disk.
- Retry failed items once without regenerating successful items.
- Do not use subagents merely to parallelize image rendering. Use subagents only for separate prompt iteration or creative exploration.
- Merge PPTX/PDF only after all selected slide images are generated.

## Confirmation Policy

Default behavior: **confirm before generation**.

- Treat explicit skill invocation, a file path, matched signals/presets, and `EXTEND.md` defaults as **recommendation inputs only**. None of them authorizes skipping confirmation.
- Do **not** start Step 3 or later until the user completes Step 2.
- Skip confirmation only when the current request explicitly says to do so, for example: "直接生成", "不用确认", "跳过确认", "按默认出幻灯片", or equivalent wording.
- If confirmation is skipped explicitly, state the assumed style / audience / slide-count / language / backend in the next user-facing update before generating.

## Language

Respond in the user's language across questions, progress reports, error messages, and the completion summary. Keep technical tokens (style names, file paths, code) in English.

## Script Directory

`{baseDir}` = this SKILL.md's directory. Resolve `${BUN_X}`: prefer `bun`; else `npx -y bun`; else suggest `brew install oven-sh/bun/bun`.

| Script | Purpose |
|--------|---------|
| `scripts/merge-to-pptx.ts` | Merge slides into PowerPoint |
| `scripts/merge-to-pdf.ts` | Merge slides into PDF |

## Options

| Option | Description |
|--------|-------------|
| `--style <name>` | Preset (see Presets below), `custom`, or custom style name |
| `--audience <type>` | beginners / intermediate / experts / executives / general |
| `--lang <code>` | Output language (en, zh, ja, ...) |
| `--slides <N>` | Target slide count (8-25 recommended, max 30) |
| `--ref <files...>` | Reference images applied per slide (style / palette / composition / subject) |
| `--batch-size <n>` | Temporary slide image generation batch size for this run. Default: `generation_batch_size` from EXTEND.md, otherwise 4. Clamp to 1-8. |
| `--outline-only` | Stop after outline |
| `--prompts-only` | Stop after prompts (skip image generation) |
| `--images-only` | Skip to Step 7; requires existing `prompts/` |
| `--regenerate <N>` | Regenerate specific slide(s): `3` or `2,5,8` |

## Style System

17 presets covering technical / educational / lifestyle / editorial use cases. Every preset is a combination of four dimensions (texture / mood / typography / density). If the user picks "Custom dimensions" in Round 1, Round 2 of the confirmation asks one question per dimension — options and verbatim copy live in `references/confirmation.md`.

### Presets (17)

| Preset | Dimensions | Best For |
|--------|------------|----------|
| `blueprint` (Default) | grid + cool + technical + balanced | Architecture, system design |
| `chalkboard` | organic + warm + handwritten + balanced | Education, tutorials |
| `corporate` | clean + professional + geometric + balanced | Investor decks, proposals |
| `minimal` | clean + neutral + geometric + minimal | Executive briefings |
| `sketch-notes` | organic + warm + handwritten + balanced | Educational, tutorials |
| `hand-drawn-edu` | organic + macaron + handwritten + balanced | Educational diagrams, process explainers |
| `watercolor` | organic + warm + humanist + minimal | Lifestyle, wellness |
| `dark-atmospheric` | clean + dark + editorial + balanced | Entertainment, gaming |
| `notion` | clean + neutral + geometric + dense | Product demos, SaaS |
| `bold-editorial` | clean + vibrant + editorial + balanced | Product launches, keynotes |
| `editorial-infographic` | clean + cool + editorial + dense | Tech explainers, research |
| `fantasy-animation` | organic + vibrant + handwritten + minimal | Educational storytelling |
| `intuition-machine` | clean + cool + technical + dense | Technical docs, academic |
| `pixel-art` | pixel + vibrant + technical + balanced | Gaming, developer talks |
| `scientific` | clean + cool + technical + dense | Biology, chemistry, medical |
| `vector-illustration` | clean + vibrant + humanist + balanced | Creative, children's content |
| `vintage` | paper + warm + editorial + balanced | Historical, heritage |

Per-preset specs: `references/styles/<preset>.md`. Preset → dimension mapping: `references/dimensions/presets.md`.

### Dimensions (when "Custom dimensions" picked)

| Dimension | Options | Purpose |
|-----------|---------|---------|
| **Texture** | clean, grid, organic, pixel, paper | Background treatment |
| **Mood** | professional, warm, cool, vibrant, dark, neutral, macaron | Color temperature |
| **Typography** | geometric, humanist, handwritten, editorial, technical | Headline/body styling |
| **Density** | minimal, balanced, dense | Information per slide |

Full per-dimension specs: `references/dimensions/*.md`.

### Auto-Selection

Match content signals to a preset. Pick the first row whose signal keywords appear in the source; fall back to `blueprint` if nothing matches.

| Signals in source | Preset |
|-------------------|--------|
| tutorial, learn, education, guide, beginner | `sketch-notes` |
| hand-drawn, infographic, diagram, process, onboarding | `hand-drawn-edu` |
| classroom, teaching, school, chalkboard | `chalkboard` |
| architecture, system, data, analysis, technical | `blueprint` |
| creative, children, kids, cute | `vector-illustration` |
| briefing, academic, research, bilingual | `intuition-machine` |
| executive, minimal, clean, simple | `minimal` |
| saas, product, dashboard, metrics | `notion` |
| investor, quarterly, business, corporate | `corporate` |
| launch, marketing, keynote, magazine | `bold-editorial` |
| entertainment, music, gaming, atmospheric | `dark-atmospheric` |
| explainer, journalism, science communication | `editorial-infographic` |
| story, fantasy, animation, magical | `fantasy-animation` |
| gaming, retro, pixel, developer | `pixel-art` |
| biology, chemistry, medical, scientific | `scientific` |
| history, heritage, vintage, expedition | `vintage` |
| lifestyle, wellness, travel, artistic | `watercolor` |

### Slide Count Heuristic

| Source length | Recommended slides |
|---------------|--------------------|
| < 1000 words | 5-10 |
| 1000-3000 words | 10-18 |
| 3000-5000 words | 15-25 |
| > 5000 words | 20-30 (consider splitting) |

## Reference Images

Users may supply reference images to guide style, palette, layout, or subject.

**Intake**: Accept via `--ref <files...>` or when the user provides file paths / pastes images in conversation.
- File path → copy to `{slide-deck-dir}/refs/NN-ref-{slug}.{ext}`
- Pasted image with no path → ask for the path, or extract style traits verbally as a text fallback

**Usage modes** (per reference):

| Usage | Effect |
|-------|--------|
| `direct` | Pass the file to the backend as a reference image for each slide |
| `style` | Extract style traits (line treatment, texture, mood) and append to every slide's prompt body |
| `palette` | Extract hex colors and append to every slide's prompt body |

Record refs in each slide's prompt frontmatter:

```yaml
references:
  - ref_id: 01
    filename: 01-ref-brand.png
    usage: direct
```

At generation time, verify files exist. If `usage: direct` and the backend accepts refs (e.g., `baoyu-image-gen --ref`), pass the file on every slide. Otherwise embed extracted `style`/`palette` traits in the prompt text.

## File Layout

```
slide-deck/{topic-slug}/
├── source-{slug}.{ext}
├── outline.md
├── prompts/NN-slide-{slug}.md
├── NN-slide-{slug}.png
├── {topic-slug}.pptx
└── {topic-slug}.pdf
```

**Slug**: 2-4 words, kebab-case, extracted from topic. "Introduction to Machine Learning" → `intro-machine-learning`.

**Backup rule** (applies across steps): if a file about to be written already exists, rename it to `<name>-backup-YYYYMMDD-HHMMSS.<ext>` before writing the new one. This protects user edits and enables rollback.

## Workflow

Copy this checklist and check off items as you complete them:

```
- [ ] Step 1: Setup & analyze
- [ ] Step 2: Confirmation ⚠️ REQUIRED (Round 1; Round 2 only if "Custom dimensions")
- [ ] Step 3: Generate outline
- [ ] Step 4: Review outline (conditional)
- [ ] Step 5: Generate prompts
- [ ] Step 6: Review prompts (conditional)
- [ ] Step 7: Generate images
- [ ] Step 8: Merge to PPTX/PDF
- [ ] Step 9: Output summary
```

### Step 1: Setup & Analyze

**1.1 Load EXTEND.md** — check these paths in order; first hit wins:

| Path | Scope |
|------|-------|
| `.baoyu-skills/baoyu-slide-deck/EXTEND.md` | Project |
| `${XDG_CONFIG_HOME:-$HOME/.config}/baoyu-skills/baoyu-slide-deck/EXTEND.md` | XDG |
| `$HOME/.baoyu-skills/baoyu-slide-deck/EXTEND.md` | User home |

If found, read, parse, and print a summary (style / audience / language / review / generation batch size). If not, proceed with defaults — first-time setup is not blocking for this skill. Schema: `references/config/preferences-schema.md`.

**1.2 Analyze content** — follow `references/analysis-framework.md`: classify content, detect language, note signals for style selection, estimate slide count from length (see the **Slide Count Heuristic** in Style System above), generate topic slug. Save source as `source.md` (honor backup rule if one exists).

**1.3 Check existing output** ⚠️ REQUIRED before Step 2. If `slide-deck/{topic-slug}/` exists, ask how to proceed — four options (regenerate outline / regenerate images / backup and regenerate / exit), verbatim copy in `references/confirmation.md`.

Save findings to `analysis.md`: topic, audience, signals, recommended style and slide count, language detection.

### Step 2: Confirmation ⚠️ REQUIRED

**Hard gate**: this step is mandatory per the [Confirmation Policy](#confirmation-policy) — Steps 3+ cannot start until the user confirms here (or explicitly opts out with "直接生成" / equivalent wording in the current request).

**Round 1 (always)** — batch five questions in one `AskUserQuestion` call: style, audience, slide count, review-outline?, review-prompts?. Verbatim options in `references/confirmation.md`.

Summary displayed before the questions:
- Content type + topic
- Detected language
- Recommended style (based on signals)
- Recommended slide count (based on length)

**Round 2 (only if "Custom dimensions" in Round 1)** — batch four questions: texture, mood, typography, density. Verbatim options in `references/confirmation.md`. The four answers replace the preset.

**After confirmation**: update `analysis.md` with final choices and store `skip_outline_review` / `skip_prompt_review` flags from Q4/Q5.

### Step 3: Generate Outline

Resolve style: preset → `references/styles/{preset}.md`; custom dimensions → combine files in `references/dimensions/`. Build `STYLE_INSTRUCTIONS` from the resolved style, apply confirmed audience + language + slide count, follow `references/outline-template.md`, and save as `outline.md`.

Stop here if `--outline-only`. Skip Step 4 if `skip_outline_review`.

### Step 4: Review Outline (Conditional)

Display a slide-by-slide table (`# | Title | Type | Layout`) along with total count and resolved style. Ask: proceed / edit outline first / regenerate — verbatim in `references/confirmation.md`.

On "Edit outline first", tell the user to edit `outline.md` and ask again when ready. On "Regenerate outline", return to Step 3.

### Step 5: Generate Prompts

For each slide in outline:
1. Read `references/base-prompt.md`
2. Extract `STYLE_INSTRUCTIONS` from the outline (don't re-read the style file)
3. Add the slide's content
4. If a `Layout:` is specified, include guidance from `references/layouts.md`
5. Save to `prompts/NN-slide-{slug}.md` (backup rule applies)

Stop here if `--prompts-only`. Skip Step 6 if `skip_prompt_review`.

### Step 6: Review Prompts (Conditional)

Display the prompts index (`# | Filename | Slide Title`) and ask: proceed / edit prompts first / regenerate — verbatim in `references/confirmation.md`. Branches mirror Step 4.

### Step 7: Generate Images

1. Resolve the image backend via the Image Generation Tools rule at the top — ask once if multiple are installed.
   - **`codex-imagegen` invocation**: when the rule resolves to `codex-imagegen`, see [references/codex-imagegen.md](references/codex-imagegen.md) for the invocation contract (preferred `baoyu-image-gen --provider codex-cli` path, runtime wrapper discovery, parameter notes, stdout schema, batch semantics — n=1 per call so slide batches must dispatch one wrapper call per slide).
2. Confirm every `prompts/NN-slide-{slug}.md` exists (hard requirement; prompt files are the reproducibility record regardless of backend).
3. Session ID: `slides-{topic-slug}-{timestamp}` — pass to the backend only if it supports sessions.
4. Build a task list for selected slides with each slide's prompt file, output PNG path, aspect ratio, session ID, and verified direct references.
5. Dispatch slide images in batches per the `## Batch Generation Policy`: backend native batch first, runtime parallel tool calls second, sequential only as fallback. Backup rule applies to PNG files before dispatch. Report progress as `Generated X/N`. Retry only failed items once before reporting an error.

`--regenerate N` jumps to this step for the named slides only. `--images-only` starts here with existing prompts.

### Step 8: Merge

```bash
${BUN_X} {baseDir}/scripts/merge-to-pptx.ts <slide-deck-dir>
${BUN_X} {baseDir}/scripts/merge-to-pdf.ts <slide-deck-dir>
```

### Step 9: Summary

```
Slide Deck Complete!
Topic: [topic]
Style: [preset or "custom: texture+mood+typography+density"]
Location: [directory]
Slides: N

- 01-slide-cover.png
- ...
- NN-slide-back-cover.png

Outline: outline.md
PPTX: {topic-slug}.pptx
PDF: {topic-slug}.pdf
```

## Slide Modification

| Action | How |
|--------|-----|
| Edit | Update `prompts/NN-slide-{slug}.md` **first**, then `--regenerate N` |
| Add | Create new prompt at position, generate image, renumber subsequent `NN` (slugs unchanged), update `outline.md`, re-merge |
| Delete | Remove PNG + prompt, renumber subsequent, update `outline.md`, re-merge |

Always update the prompt file before regenerating the image — this keeps the prompts directory as the source of truth and makes changes reproducible. Only `NN` changes on renumber; slugs stay stable so references remain valid.

Text correction policy:

- If a slide's title, bullets, or any other rendered text is misspelled, garbled, hard to read, or visually weak, do not patch the bitmap with code.
- For text-correction regenerations, write a new prompt file and a new output path so the flawed candidate is preserved for comparison.
- Post-processing is limited to crop, resize, compression, or format conversion that does not alter text or the main composition.

See `references/modification-guide.md` for full details.

## References

| File | Content |
|------|---------|
| `references/confirmation.md` | Verbatim AskUserQuestion option copy for every confirmation |
| `references/analysis-framework.md` | Content analysis framework |
| `references/outline-template.md` | Outline structure |
| `references/base-prompt.md` | Base prompt body for image generation |
| `references/layouts.md` | Layout options |
| `references/design-guidelines.md` | Audience, typography, color selection |
| `references/content-rules.md` | Content guidelines |
| `references/modification-guide.md` | Edit/add/delete workflows |
| `references/styles/<preset>.md` | Per-preset specifications |
| `references/dimensions/*.md` | Per-dimension specifications |
| `references/config/preferences-schema.md` | EXTEND.md schema |

## Notes

- Image generation takes ~10-30s per slide; report progress between them.
- For sensitive public figures, prefer stylized alternatives to avoid likeness issues.
- Maintain visual consistency via the session ID when the backend supports it.

## Changing Preferences

EXTEND.md lives at the first matching path listed in Step 1.1. Two ways to change it:

- **Edit directly** — open EXTEND.md and change fields. Full schema: `references/config/preferences-schema.md`.
- **Common one-line edits**:
  - `preferred_image_backend: auto` — default; runtime-native tool wins, falls back to the only installed backend, asks only if multiple non-native are present.
  - `preferred_image_backend: codex-imagegen` — pin to Codex's built-in.
  - `preferred_image_backend: baoyu-image-gen` — pin to the baoyu-image-gen skill.
  - `preferred_image_backend: ask` — confirm backend every run.
  - `generation_batch_size: 4` — default number of slide images to render concurrently when the backend/runtime supports batch or parallel generation.
  - `preferred_style: blueprint`, `preferred_audience: experts`, `language: zh`.
