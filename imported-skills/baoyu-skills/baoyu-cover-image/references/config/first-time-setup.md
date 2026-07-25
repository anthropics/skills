---
name: first-time-setup
description: First-time setup flow for baoyu-cover-image preferences
---

# First-Time Setup

## Overview

When no EXTEND.md is found, guide user through preference setup.

**⛔ BLOCKING OPERATION**: This setup MUST complete before ANY other workflow steps. Do NOT:
- Ask about reference images
- Ask about content/article
- Ask about dimensions (type, palette, rendering)
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

**Language**: Use user's input language or saved language preference.

Use AskUserQuestion with ALL questions in ONE call:

### Question 1: Watermark

```yaml
header: "Watermark"
question: "Watermark text for generated cover images?"
options:
  - label: "No watermark (Recommended)"
    description: "Clean covers, can enable later in EXTEND.md"
```

### Question 2: Preferred Type

```yaml
header: "Type"
question: "Default cover type preference?"
options:
  - label: "Auto-select (Recommended)"
    description: "Choose based on content analysis each time"
  - label: "hero"
    description: "Large visual impact - product launch, announcements"
  - label: "conceptual"
    description: "Concept visualization - technical, architecture"
```

### Question 3: Preferred Palette

```yaml
header: "Palette"
question: "Default color palette preference?"
options:
  - label: "Auto-select (Recommended)"
    description: "Choose based on content analysis each time"
  - label: "elegant"
    description: "Sophisticated - soft coral, muted teal, dusty rose"
  - label: "warm"
    description: "Friendly - orange, golden yellow, terracotta"
  - label: "cool"
    description: "Technical - engineering blue, navy, cyan"
```

### Question 4: Preferred Rendering

```yaml
header: "Rendering"
question: "Default rendering style preference?"
options:
  - label: "Auto-select (Recommended)"
    description: "Choose based on content analysis each time"
  - label: "hand-drawn"
    description: "Sketchy organic illustration with personal touch"
  - label: "flat-vector"
    description: "Clean modern vector with geometric shapes"
  - label: "digital"
    description: "Polished precise digital illustration"
```

### Question 5: Default Aspect Ratio

```yaml
header: "Aspect"
question: "Default aspect ratio for cover images?"
options:
  - label: "16:9 (Recommended)"
    description: "Standard widescreen - YouTube, presentations, versatile"
  - label: "2.35:1"
    description: "Cinematic widescreen - article headers, blog posts"
  - label: "1:1"
    description: "Square - Instagram, WeChat, social cards"
  - label: "3:4"
    description: "Portrait - Xiaohongshu, Pinterest, mobile content"
```

Note: More ratios (4:3, 3:2) available during generation. This sets the default recommendation.

### Question 6: Default Output Directory

```yaml
header: "Output"
question: "Default output directory for cover images?"
options:
  - label: "Independent (Recommended)"
    description: "cover-image/{topic-slug}/ - separate from article"
  - label: "Same directory"
    description: "{article-dir}/ - alongside the article file"
  - label: "imgs subdirectory"
    description: "{article-dir}/imgs/ - images folder near article"
```

### Question 7: Quick Mode

```yaml
header: "Quick"
question: "Enable quick mode by default?"
options:
  - label: "No (Recommended)"
    description: "Confirm dimension choices each time"
  - label: "Yes"
    description: "Skip confirmation, use auto-selection"
```

### Question 8: Save Location

```yaml
header: "Save"
question: "Where to save preferences?"
options:
  - label: "Project (Recommended)"
    description: ".baoyu-skills/ (this project only)"
  - label: "User"
    description: "~/.baoyu-skills/ (all projects)"
```

## Save Locations

| Choice | Path | Scope |
|--------|------|-------|
| Project | `.baoyu-skills/baoyu-cover-image/EXTEND.md` | Current project |
| User | `~/.baoyu-skills/baoyu-cover-image/EXTEND.md` | All projects |

## After Setup

1. Create directory if needed
2. Write EXTEND.md with frontmatter
3. Confirm: "Preferences saved to [path]"
4. Continue to Step 1

## EXTEND.md Template

```yaml
---
version: 3
watermark:
  enabled: [true/false]
  content: "[user input or empty]"
  position: bottom-right
  opacity: 0.7
preferred_type: [selected type or null]
preferred_palette: [selected palette or null]
preferred_rendering: [selected rendering or null]
preferred_text: title-only
preferred_mood: balanced
default_aspect: [16:9/2.35:1/1:1/3:4]
default_output_dir: [independent/same-dir/imgs-subdir]
quick_mode: [true/false]
language: null
preferred_image_backend: auto
custom_palettes: []
---
```

`preferred_image_backend: auto` is the baked-in default — first-time setup does not ask about it. The `## Image Generation Tools` rule in SKILL.md then picks the runtime-native tool (Codex `imagegen`, Hermes `image_generate`, etc.) when available, and falls back to installed backends.

## Modifying Preferences Later

See the `## Changing Preferences` section in `SKILL.md` for the canonical list of common edits (pin backend, change defaults, retrigger setup). Full schema: `preferences-schema.md`.

**EXTEND.md Supports**: Watermark | Preferred type | Preferred palette | Preferred rendering | Preferred text | Preferred mood | Default aspect ratio | Default output directory | Quick mode | Image backend preference | Custom palette definitions | Language preference
