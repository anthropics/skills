---
name: mood-dimension
description: Emotional intensity dimension for cover images
---

# Mood Dimension

Controls emotional intensity and visual weight of cover images.

## Values

| Value | Contrast | Saturation | Weight | Energy |
|-------|:--------:|:----------:|:------:|:------:|
| `subtle` | Low | Muted | Light | Calm |
| `balanced` | Medium | Normal | Medium | Moderate |
| `bold` | High | Vivid | Heavy | Dynamic |

## Detail

### subtle

Calm, understated visual presence.

**Characteristics**:
- Low contrast between elements
- Muted, desaturated colors
- Light visual weight
- Gentle, refined aesthetic
- Soft edges and transitions

**Use Cases**:
- Thought leadership content
- Professional/corporate communications
- Meditation, wellness topics
- Academic or scholarly articles
- Luxury brand aesthetics

**Color Guidance**:
- Pastels, earth tones, neutrals
- Low saturation (30-50%)
- Soft gradients
- Minimal color variety (2-3 colors)

### balanced

Versatile, harmonious visual presence.

**Characteristics**:
- Medium contrast
- Natural saturation levels
- Balanced visual weight
- Clear but not aggressive
- Standard aesthetic approach

**Use Cases**:
- General articles (default)
- Most blog content
- Educational material
- Product documentation
- News and updates

**Color Guidance**:
- Standard saturation (50-70%)
- Complementary color schemes
- Clear foreground/background separation
- Moderate color variety (3-4 colors)

### bold

Dynamic, high-impact visual presence.

**Characteristics**:
- High contrast between elements
- Vivid, saturated colors
- Heavy visual weight
- Energetic, attention-grabbing
- Sharp edges and strong shapes

**Use Cases**:
- Product launches
- Promotional announcements
- Event marketing
- Call-to-action content
- Entertainment/gaming topics

**Color Guidance**:
- High saturation (70-100%)
- Vibrant, primary colors
- Strong contrast ratios
- Dynamic color combinations (4+ colors)

## Type Compatibility

| Type | subtle | balanced | bold |
|------|:------:|:--------:|:----:|
| hero | ✓ | ✓✓ | ✓✓ |
| conceptual | ✓✓ | ✓✓ | ✓ |
| typography | ✓ | ✓✓ | ✓✓ |
| metaphor | ✓✓ | ✓✓ | ✓ |
| scene | ✓✓ | ✓✓ | ✓ |
| minimal | ✓✓ | ✓✓ | ✗ |

✓✓ = highly recommended | ✓ = compatible | ✗ = not recommended

## Palette Interaction

Mood modifies the base palette characteristics:

| Palette Category | subtle | balanced | bold |
|------------------|--------|----------|------|
| Warm palettes (warm, earth, pastel) | More whitespace, softer tones | Standard colors | Deeper, richer warm tones |
| Cool palettes (cool, mono, elegant) | Lighter lines, muted colors | Standard colors | Stronger contrast, sharper definition |
| Dark palettes (dark, vivid) | Reduced contrast, softer glow | Standard colors | Maximum impact, vivid saturation |
| Vintage palettes (retro) | More faded, sepia-heavy | Standard colors | Bolder retro contrasts |
| Duotone palettes (duotone) | Softer contrast between pair | Standard two-color split | Maximum contrast, stark separation |

## Rendering Interaction

Mood adjusts rendering characteristics:

| Rendering | subtle | balanced | bold |
|-----------|--------|----------|------|
| flat-vector | Thinner strokes, lighter fills | Standard weight | Thicker strokes, stronger fills |
| hand-drawn | Lighter pencil pressure, more space | Standard strokes | Heavier marker strokes, denser elements |
| painterly | Diluted washes, more white | Standard brush | Thicker paint, saturated strokes |
| digital | Reduced shadows, lower contrast | Standard rendering | Stronger shadows, sharper edges |
| pixel | Fewer colors, simpler shapes | Standard palette | More colors, denser pixel detail |
| chalk | Lighter chalk, more board showing | Standard chalk | Heavy chalk, vivid colors, dense marks |
| screen-print | Fewer colors (2), lighter halftone | Standard 3-4 colors, medium halftone | More colors (4-5), dense halftone, stronger misregistration |

## Auto Selection

When `--mood` is omitted, select based on signals:

| Signals | Mood Level |
|---------|------------|
| Professional, corporate, thought leadership, academic, luxury | `subtle` |
| General, educational, standard, blog, documentation | `balanced` |
| Launch, announcement, promotion, event, gaming, entertainment | `bold` |

Default: `balanced`
