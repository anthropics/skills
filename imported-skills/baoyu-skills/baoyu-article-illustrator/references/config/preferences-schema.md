---
name: preferences-schema
description: EXTEND.md YAML schema for baoyu-article-illustrator user preferences
---

# Preferences Schema

## Full Schema

```yaml
---
version: 1

watermark:
  enabled: false
  content: ""
  position: bottom-right  # bottom-right|bottom-left|bottom-center|top-right

preferred_style:
  name: null              # Built-in or custom style name
  description: ""         # Override/notes

preferred_palette: null   # Built-in palette name (macaron|warm|neon) or null

language: null            # zh|en|ja|ko|auto

default_output_dir: null  # same-dir|illustrations-subdir|independent

preferred_image_backend: auto  # auto|ask|<backend-id>

generation_batch_size: 4       # 1-8, used when backend/runtime supports batch or parallel generation

custom_styles:
  - name: my-style
    description: "Style description"
    color_palette:
      primary: ["#1E3A5F", "#4A90D9"]
      background: "#F5F7FA"
      accents: ["#00B4D8", "#48CAE4"]
    visual_elements: "Clean lines, geometric shapes"
    typography: "Modern sans-serif"
    best_for: "Business, education"
---
```

## Field Reference

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `version` | int | 1 | Schema version |
| `watermark.enabled` | bool | false | Enable watermark |
| `watermark.content` | string | "" | Watermark text (@username or custom) |
| `watermark.position` | enum | bottom-right | Position on image |
| `preferred_style.name` | string | null | Style name or null |
| `preferred_style.description` | string | "" | Custom notes/override |
| `preferred_palette` | string | null | Palette override (macaron, warm, neon, or null) |
| `language` | string | null | Output language (null = auto-detect) |
| `default_output_dir` | enum | null | Output directory preference (null = ask each time) |
| `preferred_image_backend` | string | `auto` | Image backend selection. `auto` = prefer runtime-native tool, fall back to the only installed backend, ask if multiple non-native are present. `ask` = always confirm on every run. `<backend-id>` (e.g., `codex-imagegen`, `baoyu-image-gen`, `image_generate`) = pin this backend when available; fall back to `auto` when it isn't. Absent = `auto`. Resolution logic is documented in `SKILL.md`'s `## Image Generation Tools` section. |
| `generation_batch_size` | int | 4 | Number of images to dispatch per batch when the backend has native batch support or the runtime can issue parallel generation calls. Clamp invalid values to 1-8. Current user request overrides this value. |
| `custom_styles` | array | [] | User-defined styles |

## Position Options

| Value | Description |
|-------|-------------|
| `bottom-right` | Lower right corner (default, most common) |
| `bottom-left` | Lower left corner |
| `bottom-center` | Bottom center |
| `top-right` | Upper right corner |

## Output Directory Options

| Value | Description |
|-------|-------------|
| `same-dir` | Same directory as article |
| `illustrations-subdir` | `{article-dir}/illustrations/` subdirectory |
| `independent` | `illustrations/{topic-slug}/` in working directory |

## Custom Style Fields

| Field | Required | Description |
|-------|----------|-------------|
| `name` | Yes | Unique style identifier (kebab-case) |
| `description` | Yes | What the style conveys |
| `color_palette.primary` | No | Main colors (array) |
| `color_palette.background` | No | Background color |
| `color_palette.accents` | No | Accent colors (array) |
| `visual_elements` | No | Decorative elements |
| `typography` | No | Font/lettering style |
| `best_for` | No | Recommended content types |

## Example: Minimal Preferences

```yaml
---
version: 1
watermark:
  enabled: true
  content: "@myusername"
preferred_style:
  name: notion
---
```

## Example: Full Preferences

```yaml
---
version: 1
watermark:
  enabled: true
  content: "@myaccount"
  position: bottom-right

preferred_style:
  name: notion
  description: "Clean illustrations for tech articles"

language: zh

preferred_image_backend: codex-imagegen

generation_batch_size: 4

custom_styles:
  - name: corporate
    description: "Professional B2B style"
    color_palette:
      primary: ["#1E3A5F", "#4A90D9"]
      background: "#F5F7FA"
      accents: ["#00B4D8", "#48CAE4"]
    visual_elements: "Clean lines, subtle gradients, geometric shapes"
    typography: "Modern sans-serif, professional"
    best_for: "Business, SaaS, enterprise"
---
```
