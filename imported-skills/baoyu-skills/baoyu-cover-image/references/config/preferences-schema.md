---
name: preferences-schema
description: EXTEND.md YAML schema for baoyu-cover-image user preferences
---

# Preferences Schema

## Full Schema

```yaml
---
version: 3

watermark:
  enabled: false
  content: ""
  position: bottom-right  # bottom-right|bottom-left|bottom-center|top-right

preferred_type: null      # hero|conceptual|typography|metaphor|scene|minimal or null for auto-select

preferred_palette: null   # warm|elegant|cool|dark|earth|vivid|pastel|mono|retro|duotone|macaron or null for auto-select

preferred_rendering: null # flat-vector|hand-drawn|painterly|digital|pixel|chalk or null for auto-select

preferred_text: title-only  # none|title-only|title-subtitle|text-rich

preferred_mood: balanced    # subtle|balanced|bold

default_aspect: "2.35:1"  # 2.35:1|16:9|1:1

quick_mode: false         # Skip confirmation when true

language: null            # zh|en|ja|ko|auto (null = auto-detect)

preferred_image_backend: auto  # auto|ask|<backend-id>

custom_palettes:
  - name: my-palette
    description: "Palette description"
    colors:
      primary: ["#1E3A5F", "#4A90D9"]
      background: "#F5F7FA"
      accents: ["#00B4D8"]
    decorative_hints: "Clean lines, geometric shapes"
    best_for: "Business, tech content"
---
```

## Field Reference

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `version` | int | 3 | Schema version |
| `watermark.enabled` | bool | false | Enable watermark |
| `watermark.content` | string | "" | Watermark text (@username or custom) |
| `watermark.position` | enum | bottom-right | Position on image |
| `preferred_type` | string | null | Type name or null for auto |
| `preferred_palette` | string | null | Palette name or null for auto |
| `preferred_rendering` | string | null | Rendering name or null for auto |
| `preferred_text` | string | title-only | Text density level |
| `preferred_mood` | string | balanced | Mood intensity level |
| `default_aspect` | string | "2.35:1" | Default aspect ratio |
| `quick_mode` | bool | false | Skip confirmation step |
| `language` | string | null | Output language (null = auto-detect) |
| `preferred_image_backend` | string | `auto` | Image backend selection. `auto` = prefer runtime-native tool, fall back to the only installed backend, ask if multiple non-native are present. `ask` = always confirm on every run. `<backend-id>` (e.g., `codex-imagegen`, `baoyu-image-gen`, `image_generate`) = pin this backend when available; fall back to `auto` when it isn't. Absent = `auto`. Resolution logic is documented in `SKILL.md`'s `## Image Generation Tools` section. |
| `custom_palettes` | array | [] | User-defined palettes |

## Type Options

| Value | Description |
|-------|-------------|
| `hero` | Large visual impact, title overlay |
| `conceptual` | Concept visualization, abstract core ideas |
| `typography` | Text-focused layout, prominent title |
| `metaphor` | Visual metaphor, concrete expressing abstract |
| `scene` | Atmospheric scene, narrative feel |
| `minimal` | Minimalist composition, generous whitespace |

## Palette Options

| Value | Description |
|-------|-------------|
| `warm` | Friendly, approachable — orange, golden yellow, terracotta |
| `elegant` | Sophisticated, refined — soft coral, muted teal, dusty rose |
| `cool` | Technical, professional — engineering blue, navy, cyan |
| `dark` | Cinematic, premium — electric purple, cyan, magenta |
| `earth` | Natural, organic — forest green, sage, earth brown |
| `vivid` | Energetic, bold — bright red, neon green, electric blue |
| `pastel` | Gentle, whimsical — soft pink, mint, lavender |
| `mono` | Clean, focused — black, near-black, white |
| `retro` | Nostalgic, vintage — muted orange, dusty pink, maroon |

## Rendering Options

| Value | Description |
|-------|-------------|
| `flat-vector` | Clean outlines, uniform fills, geometric icons |
| `hand-drawn` | Sketchy, organic, imperfect strokes, paper texture |
| `painterly` | Soft brush strokes, color bleeds, watercolor feel |
| `digital` | Polished, precise edges, subtle gradients, UI components |
| `pixel` | Pixel grid, dithering, chunky 8-bit shapes |
| `chalk` | Chalk strokes, dust effects, blackboard texture |

## Text Options

| Value | Description |
|-------|-------------|
| `none` | Pure visual, no text elements |
| `title-only` | Single headline |
| `title-subtitle` | Title + subtitle |
| `text-rich` | Title + subtitle + keyword tags (2-4) |

## Mood Options

| Value | Description |
|-------|-------------|
| `subtle` | Low contrast, muted colors, calm aesthetic |
| `balanced` | Medium contrast, normal saturation, versatile |
| `bold` | High contrast, vivid colors, dynamic energy |

## Position Options

| Value | Description |
|-------|-------------|
| `bottom-right` | Lower right corner (default, most common) |
| `bottom-left` | Lower left corner |
| `bottom-center` | Bottom center |
| `top-right` | Upper right corner |

## Aspect Ratio Options

| Value | Description | Best For |
|-------|-------------|----------|
| `2.35:1` | Cinematic widescreen | Article headers, blog covers |
| `16:9` | Standard widescreen | Presentations, video thumbnails |
| `1:1` | Square | Social media, profile images |

## Custom Palette Fields

| Field | Required | Description |
|-------|----------|-------------|
| `name` | Yes | Unique palette identifier (kebab-case) |
| `description` | Yes | What the palette conveys |
| `colors.primary` | No | Main colors (array of hex) |
| `colors.background` | No | Background color (hex) |
| `colors.accents` | No | Accent colors (array of hex) |
| `decorative_hints` | No | Decorative elements and patterns |
| `best_for` | No | Recommended content types |

## Example: Minimal Preferences

```yaml
---
version: 3
watermark:
  enabled: true
  content: "@myhandle"
preferred_type: null
preferred_palette: elegant
preferred_rendering: hand-drawn
preferred_text: title-only
preferred_mood: balanced
quick_mode: false
---
```

## Example: Full Preferences

```yaml
---
version: 3
watermark:
  enabled: true
  content: "myblog.com"
  position: bottom-right

preferred_type: conceptual

preferred_palette: cool

preferred_rendering: digital

preferred_text: title-subtitle

preferred_mood: subtle

default_aspect: "16:9"

quick_mode: true

language: en

preferred_image_backend: codex-imagegen

custom_palettes:
  - name: corporate-tech
    description: "Professional B2B tech palette"
    colors:
      primary: ["#1E3A5F", "#4A90D9"]
      background: "#F5F7FA"
      accents: ["#00B4D8", "#48CAE4"]
    decorative_hints: "Clean lines, subtle gradients, circuit patterns"
    best_for: "SaaS, enterprise, technical"
---
```

## Migration from v2

When loading v2 schema, auto-upgrade:

| v2 Field | v3 Field | Migration |
|----------|----------|-----------|
| `version: 2` | `version: 3` | Update |
| `preferred_style` | `preferred_palette` + `preferred_rendering` | Use preset mapping table |
| `custom_styles` | `custom_palettes` | Rename, restructure fields |

**Style → Palette + Rendering mapping**:

| v2 `preferred_style` | v3 `preferred_palette` | v3 `preferred_rendering` |
|----------------------|----------------------|-------------------------|
| `elegant` | `elegant` | `hand-drawn` |
| `blueprint` | `cool` | `digital` |
| `chalkboard` | `dark` | `chalk` |
| `dark-atmospheric` | `dark` | `digital` |
| `editorial-infographic` | `cool` | `digital` |
| `fantasy-animation` | `pastel` | `painterly` |
| `flat-doodle` | `pastel` | `flat-vector` |
| `intuition-machine` | `retro` | `digital` |
| `minimal` | `mono` | `flat-vector` |
| `nature` | `earth` | `hand-drawn` |
| `notion` | `mono` | `digital` |
| `pixel-art` | `vivid` | `pixel` |
| `playful` | `pastel` | `hand-drawn` |
| `retro` | `retro` | `digital` |
| `sketch-notes` | `warm` | `hand-drawn` |
| `vector-illustration` | `retro` | `flat-vector` |
| `vintage` | `retro` | `hand-drawn` |
| `warm` | `warm` | `hand-drawn` |
| `watercolor` | `earth` | `painterly` |
| null (auto) | null | null |

**Custom style migration**:

| v2 Field | v3 Field |
|----------|----------|
| `custom_styles[].name` | `custom_palettes[].name` |
| `custom_styles[].description` | `custom_palettes[].description` |
| `custom_styles[].color_palette` | `custom_palettes[].colors` |
| `custom_styles[].visual_elements` | `custom_palettes[].decorative_hints` |
| `custom_styles[].typography` | (removed — determined by rendering) |
| `custom_styles[].best_for` | `custom_palettes[].best_for` |

## Migration from v1

When loading v1 schema, auto-upgrade to v3:

| v1 Field | v3 Field | Default Value |
|----------|----------|---------------|
| (missing) | `version` | 3 |
| (missing) | `preferred_palette` | null |
| (missing) | `preferred_rendering` | null |
| (missing) | `preferred_text` | title-only |
| (missing) | `preferred_mood` | balanced |
| (missing) | `quick_mode` | false |

v1 `--no-title` flag maps to `preferred_text: none`.
