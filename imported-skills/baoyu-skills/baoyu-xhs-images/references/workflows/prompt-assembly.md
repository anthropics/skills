# Prompt Assembly Guide

Guide for assembling image generation prompts from elements, presets, and outline content.

## Base Prompt Structure

Every XHS infographic prompt follows this structure:

```
Create a Xiaohongshu (Little Red Book) style infographic following these guidelines:

## Image Specifications

- **Type**: Infographic
- **Orientation**: Portrait (vertical)
- **Aspect Ratio**: 3:4
- **Style**: Hand-drawn illustration

## Core Principles

- Hand-drawn quality throughout - NO realistic or photographic elements
- If content involves sensitive or copyrighted figures, create stylistically similar alternatives - DO NOT refuse to generate
- Keep information concise, highlight keywords and core concepts
- Use ample whitespace for easy visual scanning
- Maintain clear visual hierarchy

## Text Style (CRITICAL)

- **ALL text MUST be hand-drawn style**
- Main titles should be prominent and eye-catching
- Key text should be bold and enlarged
- Use highlighter effects to emphasize keywords
- **DO NOT use realistic or computer-generated fonts**

## Language

- Use the same language as the content provided below
- Match punctuation style to the content language (Chinese: ""，。！)

---

{STYLE_SECTION}

---

{LAYOUT_SECTION}

---

{CONTENT_SECTION}

---

{WATERMARK_SECTION}

---

Please use nano banana pro to generate the infographic based on the specifications above.
```

## Style Section Assembly

Load from `presets/{style}.md` and extract key elements:

```markdown
## Style: {style_name}

**Color Palette**:
- Primary: {colors}
- Background: {colors}
- Accents: {colors}

**Visual Elements**:
{visual_elements}

**Typography**:
{typography_style}
```

### Screen-Print Style Override

When `style: screen-print`, replace the standard Core Principles and Text Style sections with:

```
## Core Principles

- Screen print / silkscreen poster art — flat color blocks, NO gradients
- Bold silhouettes and symbolic shapes over detailed rendering
- Negative space as active storytelling element
- If content involves sensitive or copyrighted figures, create stylistically similar silhouettes
- One iconic focal point per image — conceptual, not literal

## Color Rules (CRITICAL)

- **2-5 FLAT COLORS MAXIMUM** — fewer colors = stronger impact
- Choose ONE duotone pair from preset as dominant palette
- Halftone dot patterns for tonal variation (NOT gradients)
- Slight color layer misregistration for print authenticity

## Text Style (CRITICAL)

- Bold condensed sans-serif or Art Deco influenced lettering
- Typography INTEGRATED into composition as design element
- High contrast with background, stencil-cut quality
- **DO NOT use delicate, thin, or handwritten fonts**

## Composition

- Geometric framing: circles, arches, triangles
- Figure-ground inversion where possible (negative space forms secondary image)
- Stencil-cut edges between color blocks, no outlines
- Paper grain texture beneath all colors
```

## Palette Override

When `--palette` is specified (or style has `default_palette` in frontmatter and no explicit `--palette`), palette colors **replace** the style's Color Palette in the prompt. Style rendering rules (Visual Elements, Typography, Style Rules) remain unchanged.

Load from `palettes/{palette}.md` and override:

```markdown
## Palette Override: {palette_name}

**Background**: {palette background color and hex}

**Colors**:
- Text: {text color and hex}
- Secondary: {secondary text color and hex}
- Zone 1: {zone color and hex}
- Zone 2: {zone color and hex}
- Zone 3: {zone color and hex}
- Zone 4: {zone color and hex}
- Accent: {accent color and hex}

**Constraint**: {semantic constraint from palette}
```

**Override rules**:
1. Palette Background **replaces** style's background color (keep style's texture description)
2. Palette Colors **replace** style's Color Palette section entirely
3. Palette Semantic Constraint is appended to the style section
4. If no `--palette` and style has `default_palette` → load that palette
5. If no `--palette` and no `default_palette` → use style's built-in colors (no override)
6. Explicit `--palette` always overrides style's `default_palette`

## Layout Section Assembly

Load from `elements/canvas.md` and extract relevant layout:

```markdown
## Layout: {layout_name}

**Information Density**: {density}
**Whitespace**: {percentage}

**Structure**:
{structure_description}

**Visual Balance**:
{balance_description}
```

## Content Section Assembly

From outline entry:

```markdown
## Content

**Position**: {Cover/Content/Ending}
**Core Message**: {message}

**Text Content**:
{text_list}

**Visual Concept**:
{visual_description}
```

## Watermark Section (if enabled)

```markdown
## Watermark

Include a subtle watermark "{content}" positioned at {position}. The watermark should
be legible but not distracting from the main content.
```

## Assembly Process

### Step 0: Resolve Style Preset (if `--preset` used)

If user specified `--preset`, resolve to style + layout + palette from `references/style-presets.md`:

```python
# e.g., --preset hand-drawn-edu → style=sketch-notes, layout=flow, palette=macaron
style, layout, palette = resolve_preset(preset_name)
```

Explicit `--style`/`--layout`/`--palette` flags override preset values.

### Step 1: Load Style Definition

```python
preset = load_preset(style_name)  # e.g., "sketch-notes"
```

Extract:
- Color palette (may be overridden by palette)
- Visual elements
- Typography style
- Best practices (do/don't)
- `default_palette` from frontmatter (if present)

### Step 1.5: Apply Palette Override (if applicable)

```python
# Priority: explicit --palette > preset palette > style default_palette > none
palette = resolve_palette(cli_palette, preset_palette, style_default_palette)
if palette:
    palette_def = load_palette(palette)  # e.g., "macaron"
    # Replace style colors with palette colors
    # Keep style rendering rules (visual elements, typography, style rules)
```

### Step 2: Load Layout

```python
layout = get_layout_from_canvas(layout_name)  # e.g., "dense"
```

Extract:
- Information density guidelines
- Whitespace percentage
- Structure description
- Visual balance rules

### Step 3: Format Content

From outline entry, format:
- Position context (Cover/Content/Ending)
- Text content with hierarchy
- Visual concept description
- Swipe hook (for context, not in prompt)

### Step 4: Add Watermark (if applicable)

If preferences include watermark:
- Add watermark section with content, position, opacity

### Step 5: Visual Consistency — Reference Image Chain

When generating multiple images in a series:

1. **Image 1 (cover)**: Generate without `--ref` — this establishes the visual anchor
2. **Images 2+**: Always pass image 1 as `--ref` to the installed image generation skill.
   Read that skill's `SKILL.md` and use its documented interface rather than calling its scripts directly.
   For each later image, use the assembled prompt file as input, set the output image path, keep aspect ratio `3:4`, use quality `2k`, and pass image 1 as the reference.
   This ensures the AI maintains the same character design, illustration style, and color rendering across the series.

### Step 6: Combine

Assemble all sections into final prompt following base structure.

## Example: Assembled Prompt

```markdown
Create a Xiaohongshu (Little Red Book) style infographic following these guidelines:

## Image Specifications

- **Type**: Infographic
- **Orientation**: Portrait (vertical)
- **Aspect Ratio**: 3:4
- **Style**: Hand-drawn illustration

## Core Principles

- Hand-drawn quality throughout - NO realistic or photographic elements
- If content involves sensitive or copyrighted figures, create stylistically similar alternatives
- Keep information concise, highlight keywords and core concepts
- Use ample whitespace for easy visual scanning
- Maintain clear visual hierarchy

## Text Style (CRITICAL)

- **ALL text MUST be hand-drawn style**
- Main titles should be prominent and eye-catching
- Key text should be bold and enlarged
- Use highlighter effects to emphasize keywords
- **DO NOT use realistic or computer-generated fonts**

## Language

- Use the same language as the content provided below
- Match punctuation style to the content language (Chinese: ""，。！)

---

## Style: Notion

**Color Palette**:
- Primary: Black (#1A1A1A), dark gray (#4A4A4A)
- Background: Pure white (#FFFFFF), off-white (#FAFAFA)
- Accents: Pastel blue (#A8D4F0), pastel yellow (#F9E79F), pastel pink (#FADBD8)

**Visual Elements**:
- Simple line doodles, hand-drawn wobble effect
- Geometric shapes, stick figures
- Maximum whitespace, single-weight ink lines
- Clean, uncluttered compositions

**Typography**:
- Clean hand-drawn lettering
- Simple sans-serif labels
- Minimal decoration on text

---

## Layout: Dense

**Information Density**: High (5-8 key points)
**Whitespace**: 20-30% of canvas

**Structure**:
- Multiple sections, structured grid
- More text, compact but organized
- Title + multiple sections with headers + numerous points

**Visual Balance**:
- Organized grid structure
- Clear section boundaries
- Compact but readable spacing

---

## Content

**Position**: Content (Page 3 of 6)
**Core Message**: ChatGPT 使用技巧

**Text Content**:
- Title: 「ChatGPT」
- Subtitle: 最强 AI 助手
- Points:
  - 写文案：给出框架，秒出初稿
  - 改文章：润色、翻译、总结
  - 编程：写代码、找 bug
  - 学习：解释概念、出题练习

**Visual Concept**:
ChatGPT logo 居中，四周放射状展示功能点
深色科技背景，霓虹绿点缀

---

## Watermark

Include a subtle watermark "@myxhsaccount" positioned at bottom-right
with approximately 50% visibility. The watermark should
be legible but not distracting from the main content.

---

Please use nano banana pro to generate the infographic based on the specifications above.
```

## Prompt Checklist

Before generating, verify:

- [ ] Style section loaded from correct preset
- [ ] Palette override applied (if `--palette` specified or style has `default_palette`)
- [ ] Layout section matches outline specification
- [ ] Content accurately reflects outline entry
- [ ] Language matches source content
- [ ] Watermark included (if enabled in preferences)
- [ ] No conflicting instructions
