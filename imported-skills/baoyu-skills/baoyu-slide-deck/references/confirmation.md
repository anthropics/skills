# Confirmation Questions

Concrete option copy for the confirmation steps. SKILL.md lists which questions to ask — this file gives the verbatim options used in Claude Code. Adapt copy to the runtime's native user-input tool; the intent matters more than the exact wording.

## Round 1 (Always)

Batch all five questions in a single `AskUserQuestion` call.

### Q1: Style

```yaml
header: Style
question: Which visual style for this deck?
options:
  - label: "{recommended_preset} (Recommended)"
    description: Best match based on content analysis
  - label: "{alternative_preset}"
    description: "{alternative style description}"
  - label: Custom dimensions
    description: Choose texture, mood, typography, density separately
```

### Q2: Audience

```yaml
header: Audience
question: Who is the primary reader?
options:
  - label: General readers (Recommended)
    description: Broad appeal, accessible content
  - label: Beginners/learners
    description: Educational focus, clear explanations
  - label: Experts/professionals
    description: Technical depth, domain knowledge
  - label: Executives
    description: High-level insights, minimal detail
```

### Q3: Slide Count

```yaml
header: Slides
question: How many slides?
options:
  - label: "{N} slides (Recommended)"
    description: Based on content length
  - label: "Fewer ({N-3} slides)"
    description: More condensed, less detail
  - label: "More ({N+3} slides)"
    description: More detailed breakdown
```

### Q4: Review Outline

```yaml
header: Outline
question: Review outline before generating prompts?
options:
  - label: Yes, review outline (Recommended)
    description: Review slide titles and structure
  - label: No, skip outline review
    description: Proceed directly to prompt generation
```

### Q5: Review Prompts

```yaml
header: Prompts
question: Review prompts before generating images?
options:
  - label: Yes, review prompts (Recommended)
    description: Review image generation prompts
  - label: No, skip prompt review
    description: Proceed directly to image generation
```

## Round 2 — Custom Dimensions

Triggered only when Q1 of Round 1 = "Custom dimensions". Batch all four dimension questions.

### Texture

```yaml
header: Texture
question: Which visual texture?
options:
  - label: clean
    description: Pure solid color, no texture
  - label: grid
    description: Subtle grid overlay, technical
  - label: organic
    description: Soft textures, hand-drawn feel
  - label: pixel
    description: Chunky pixels, 8-bit aesthetic
```

`paper` is also valid — accept via "Other".

### Mood

```yaml
header: Mood
question: Which color mood?
options:
  - label: professional
    description: Cool-neutral, navy/gold
  - label: warm
    description: Earth tones, friendly
  - label: cool
    description: Blues, grays, analytical
  - label: vibrant
    description: High saturation, bold
  - label: macaron
    description: Pastel blocks on cream
```

`dark`, `neutral` valid via "Other".

### Typography

```yaml
header: Typography
question: Which typography style?
options:
  - label: geometric
    description: Modern sans-serif, clean
  - label: humanist
    description: Friendly, readable
  - label: handwritten
    description: Marker/brush, organic
  - label: editorial
    description: Magazine style, dramatic
```

`technical` valid via "Other".

### Density

```yaml
header: Density
question: Information density?
options:
  - label: balanced (Recommended)
    description: 2-3 key points per slide
  - label: minimal
    description: One focus point, maximum whitespace
  - label: dense
    description: Multiple data points, compact
```

## Outline Review (Step 4)

```yaml
header: Confirm
question: Ready to generate prompts?
options:
  - label: Yes, proceed (Recommended)
    description: Generate image prompts
  - label: Edit outline first
    description: I'll modify outline.md before continuing
  - label: Regenerate outline
    description: Create new outline with different approach
```

## Prompt Review (Step 6)

```yaml
header: Confirm
question: Ready to generate slide images?
options:
  - label: Yes, proceed (Recommended)
    description: Generate all slide images
  - label: Edit prompts first
    description: I'll modify prompts before continuing
  - label: Regenerate prompts
    description: Create new prompts with different approach
```

## Existing Content (Step 1.3)

```yaml
header: Existing
question: Existing content found. How to proceed?
options:
  - label: Regenerate outline
    description: Keep images, regenerate outline only
  - label: Regenerate images
    description: Keep outline, regenerate images only
  - label: Backup and regenerate
    description: Backup to {slug}-backup-{timestamp}, then regenerate all
  - label: Exit
    description: Cancel, keep existing content unchanged
```
