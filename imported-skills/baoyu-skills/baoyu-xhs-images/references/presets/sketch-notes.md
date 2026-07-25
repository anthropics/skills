---
name: sketch-notes
category: educational
default_palette: macaron
---

# Sketch Notes Style

Hand-drawn educational infographic with slight line wobble, like a high-quality presentation visual summary.

## Element Combination

```yaml
canvas:
  ratio: portrait-3-4
  grid: single | dual

image_effects:
  cutout: stylized
  stroke: none
  filter: none

typography:
  decorated: handwritten
  tags: rounded-badge
  direction: horizontal

decorations:
  emphasis: underline | circle-mark | arrows-curvy | star-burst
  background: paper-texture
  doodles: hand-drawn-lines | stars-sparkles | arrows-curvy | squiggles
  frames: rounded-rect
```

## Color Palette

Default: **macaron** palette (see `palettes/macaron.md`)

When no `--palette` is specified, uses macaron colors: warm cream background (#F5F0E8), macaron blue/lavender/mint/peach zone blocks, coral red accent.

## Visual Elements

- Hand-drawn wobble on all lines and shapes
- Simple stick-figure characters at desks, working, thinking
- Rounded cards with pastel color blocks as information sections
- Color fills do NOT completely fill outlines (hand-painted feel)
- Doodle decorations: small stars, underlines, checkmarks, lock icons, clipboard icons
- Wavy hand-drawn arrows connecting zones with small text labels
- Thought bubbles and speech bubbles with sketchy outlines
- Simple conceptual icons (documents, lightbulbs, gears, arrows)
- Generous whitespace between zones for clean composition

## Typography

- Bold hand-drawn lettering for titles (large, prominent)
- Bold keywords within content zones
- Smaller annotations in secondary text color
- Hand-drawn quality on ALL text, no computer-generated fonts
- Clear information hierarchy: title > zone labels > body text > annotations

## Style Rules

### Do
- Maintain slight wobble on every line, shape, and border
- Use palette block colors as distinct section backgrounds
- Leave color fills intentionally incomplete at edges
- Include simple doodle icons relevant to content
- Keep generous whitespace between zones
- Use accent color sparingly for emphasis on key terms
- Draw connecting arrows with hand-drawn wavy feel

### Don't
- Use perfect geometric shapes or straight lines
- Create photorealistic elements
- Fill colors completely to edges (maintain hand-painted gap)
- Use dark or saturated backgrounds
- Overcrowd with too many decorative elements
- Use gradient fills or glossy effects

## Best Layout Pairings

| Layout | Compatibility | Use Case |
|--------|---------------|----------|
| sparse | ✓ | Simple covers with single zone |
| balanced | ✓✓ | Standard educational summaries |
| dense | ✓✓ | Knowledge cards, concept maps |
| list | ✓✓ | Step-by-step guides, checklists |
| comparison | ✓ | Side-by-side concept contrast |
| flow | ✓✓ | Process diagrams, workflows, tutorials |
| mindmap | ✓✓ | Concept maps, radial knowledge maps |
| quadrant | ✓ | Classification matrices |

## Best For

- Educational content, tutorials, how-to guides
- Process and workflow explanations
- Knowledge summaries, concept diagrams
- Technical explanations made approachable
- Visual summaries of articles or talks
- Onboarding materials, friendly guides
