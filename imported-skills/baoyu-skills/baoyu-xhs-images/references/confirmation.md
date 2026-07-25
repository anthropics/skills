# Confirmation Questions

Concrete option copy for Step 2 Smart Confirm. SKILL.md states which question to ask and when — this file supplies the verbatim options used in Claude Code. Other runtimes should adapt the wording to their native user-input tool while preserving intent.

## Step 2 — Smart Confirm Entry

Single-question confirmation presented right after the auto-recommended plan.

```yaml
header: Mode
question: How to proceed with the recommended plan?
options:
  - label: 1. ✅ 确认，直接生成（推荐）
    description: Trust auto-recommendation and proceed immediately
  - label: 2. 🎛️ 自定义调整
    description: Modify strategy/style/layout/count in one step
  - label: 3. 📋 详细模式
    description: Generate 3 outline variants, then choose (two confirmations)
```

## Path B — Customize (Option 2)

Batch these five questions. Leaving a field blank keeps the recommended value.

```yaml
header: Style/Strategy
question: "Strategy + style. Current: {strategy} + {style}"
hint: |
  Strategies: A Story-Driven (warm) | B Information-Dense (notion) | C Visual-First (screen-print)
  Styles: cute / fresh / warm / bold / minimal / retro / pop / notion / chalkboard / study-notes / screen-print / sketch-notes
  Presets: knowledge-card / checklist / tutorial / poster / hand-drawn-edu / ...
```

```yaml
header: Layout
question: "Layout. Current: {layout}"
options: [sparse, balanced, dense, list, comparison, flow, mindmap, quadrant]
```

```yaml
header: Palette
question: "Palette. Current: {palette or 默认}"
options: [默认, macaron, warm, neon]
```

```yaml
header: Count
question: "Image count. Current: {N}"
hint: Range 2-10
```

```yaml
header: Notes
question: Optional notes (selling-point emphasis, audience adjustment, color preference)
optional: true
```

## Path C — Detailed Mode

### Step 2a: Content Understanding

Batch these questions.

```yaml
header: SellingPoints
question: Core selling points (pick all that apply)
multiSelect: true
```

```yaml
header: Audience
question: Target audience
```

```yaml
header: Tone
question: Style preference
options:
  - label: Authentic sharing
  - label: Professional review
  - label: Aesthetic mood
  - label: Auto
```

```yaml
header: Context
question: Additional context (optional)
optional: true
```

### Step 2c: Outline & Style Selection

Batch these three questions.

```yaml
header: Strategy
question: Which outline strategy?
options:
  - label: A — Story-Driven
  - label: B — Information-Dense
  - label: C — Visual-First
  - label: Combine (specify pages from each)
```

```yaml
header: Style
question: Visual style?
options:
  - label: Use recommended
  - label: Select preset
  - label: Select style directly
  - label: Custom description
```

```yaml
header: Elements
question: Visual elements?
options:
  - label: Use defaults (Recommended)
  - label: Adjust background
  - label: Adjust decorations
  - label: Custom
```

## Outline Variant Frontmatter

Used by Path C when writing the three `outline-strategy-{a,b,c}.md` files. Each variant MUST have a different structure AND a different recommended style — include `style_reason` explaining why the style fits the strategy.

```yaml
---
strategy: a  # a | b | c
name: Story-Driven
style: warm  # recommended style for this strategy
palette: ~   # optional: macaron | warm | neon | ~ (style default)
style_reason: "Warm tones enhance emotional storytelling and personal connection"
elements:
  background: solid-pastel
  decorations: [clouds, stars-sparkles]
  emphasis: star-burst
  typography: highlight
layout: balanced
image_count: 5
---

## P1 Cover
**Type**: cover
**Hook**: "入冬后脸不干了🥹终于找到对的面霜"
**Visual**: Product hero shot with cozy winter atmosphere
**Layout**: sparse

## P2 Problem
**Type**: pain-point
...
```

Page-count heuristic: strategy A typically 4-6 pages, B typically 3-5, C typically 3-4.
