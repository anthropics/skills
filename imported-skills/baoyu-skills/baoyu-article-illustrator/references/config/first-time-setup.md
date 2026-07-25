---
name: first-time-setup
description: First-time setup flow for baoyu-article-illustrator preferences
---

# First-Time Setup

## Overview

When no EXTEND.md is found, guide user through preference setup.

**⛔ BLOCKING OPERATION**: This setup MUST complete before ANY other workflow steps. Do NOT:
- Ask about reference images
- Ask about content/article
- Ask about type or style preferences
- Proceed to content analysis

ONLY ask the questions in this setup flow, save EXTEND.md, then continue.

## Setup Flow

```
No EXTEND.md found
        │
        ▼
┌─────────────────────┐
│ AskUserQuestion     │
│ (all questions)     │
└─────────────────────┘
        │
        ▼
┌─────────────────────┐
│ Create EXTEND.md    │
└─────────────────────┘
        │
        ▼
    Continue to Step 1
```

## Questions

**Language**: Use user's input language or preferred language for all questions. Do not always use English.

Use single AskUserQuestion with multiple questions (AskUserQuestion auto-adds "Other" option):

### Question 1: Watermark

```
header: "Watermark"
question: "Watermark text for generated illustrations? Type your watermark content (e.g., name, @handle)"
options:
  - label: "No watermark (Recommended)"
    description: "No watermark, can enable later in EXTEND.md"
```

Position defaults to bottom-right.

### Question 2: Preferred Style

```
header: "Style"
question: "Default illustration style preference? Or type another style name or your custom style"
options:
  - label: "sketch-notes (Recommended)"
    description: "Warm cream paper, black hand-drawn lines, soft pastel blocks — educational infographic feel. Great default for most articles."
  - label: "None"
    description: "Auto-select based on content analysis (falls back to sketch-notes when no strong signal)"
  - label: "notion"
    description: "Minimalist hand-drawn line art"
  - label: "warm"
    description: "Friendly, approachable, personal"
```

### Question 3: Output Directory

```
header: "Output Directory"
question: "Where to save generated illustrations when illustrating a file?"
options:
  - label: "imgs-subdir (Recommended)"
    description: "{article-dir}/imgs/ — images in a subdirectory next to the article"
  - label: "same-dir"
    description: "{article-dir}/ — images alongside the article file"
  - label: "illustrations-subdir"
    description: "{article-dir}/illustrations/ — separate illustrations subdirectory"
  - label: "independent"
    description: "illustrations/{topic-slug}/ — standalone directory in cwd"
```

### Question 4: Save Location

```
header: "Save"
question: "Where to save preferences?"
options:
  - label: "Project"
    description: ".baoyu-skills/ (this project only)"
  - label: "User"
    description: "~/.baoyu-skills/ (all projects)"
```

## Save Locations

| Choice | Path | Scope |
|--------|------|-------|
| Project | `.baoyu-skills/baoyu-article-illustrator/EXTEND.md` | Current project |
| User | `~/.baoyu-skills/baoyu-article-illustrator/EXTEND.md` | All projects |

## After Setup

1. Create directory if needed
2. Write EXTEND.md with frontmatter
3. Confirm: "Preferences saved to [path]"
4. Continue to Step 1

## EXTEND.md Template

```yaml
---
version: 1
watermark:
  enabled: [true/false]
  content: "[user input or empty]"
  position: bottom-right
  opacity: 0.7
preferred_style:
  name: [selected style or null]
  description: ""
default_output_dir: imgs-subdir  # same-dir | imgs-subdir | illustrations-subdir | independent
language: null
preferred_image_backend: auto
generation_batch_size: 4
custom_styles: []
---
```

`preferred_image_backend: auto` is the baked-in default — first-time setup does not ask about it. The `## Image Generation Tools` rule in SKILL.md then picks the runtime-native tool (Codex `imagegen`, Hermes `image_generate`, etc.) when available, and falls back to installed backends.

`generation_batch_size: 4` is the baked-in default for batch rendering. The current user request may override it for one run.

## Modifying Preferences Later

See the `## Changing Preferences` section in `SKILL.md` for the canonical list of common edits (pin backend, change defaults, retrigger setup). Full schema: `preferences-schema.md`.
