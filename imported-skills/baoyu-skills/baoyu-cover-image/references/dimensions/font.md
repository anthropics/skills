---
name: font-dimension
description: Typography style dimension for cover images
---

# Font Dimension

Controls typography style and character feel.

## Values

| Font | Visual Style | Line Quality | Character |
|------|--------------|--------------|-----------|
| `clean` | Geometric sans-serif | Sharp, uniform | Modern, precise, neutral |
| `handwritten` | Hand-lettered, brush | Organic, varied | Warm, personal, friendly |
| `serif` | Classic serifs, elegant | Refined, structured | Editorial, authoritative |
| `display` | Bold, decorative | Heavy, expressive | Attention-grabbing, playful |

## Detail

### clean

Modern, universal typography with neutral character.

**Characteristics**:
- Geometric sans-serif letterforms
- Sharp, uniform line weight
- Clean edges, no flourishes
- High readability at all sizes
- Minimal personality, maximum clarity

**Use Cases**:
- Technical documentation
- Professional/corporate content
- Minimal design approaches
- Data-driven articles
- Modern brand aesthetics

**Prompt Hints**:
- Use clean geometric sans-serif typography
- Modern, minimal letterforms
- Sharp edges, uniform stroke weight
- High contrast against background

### handwritten

Warm, organic typography with personal character.

**Characteristics**:
- Hand-lettered or brush style
- Organic, varied line weight
- Natural imperfections
- Approachable, human feel
- Casual yet intentional

**Use Cases**:
- Personal stories
- Lifestyle content
- Wellness and self-improvement
- Creative tutorials
- Friendly brand voices

**Prompt Hints**:
- Use warm hand-lettered typography with organic brush strokes
- Friendly, personal feel
- Natural variation in stroke weight
- Approachable, human character

### serif

Classic, elegant typography with editorial authority.

**Characteristics**:
- Traditional serif letterforms
- Refined, structured strokes
- Elegant proportions
- Timeless sophistication
- Formal, trustworthy feel

**Use Cases**:
- Editorial content
- Academic articles
- Luxury brand content
- Historical topics
- Literary pieces

**Prompt Hints**:
- Use elegant serif typography with refined letterforms
- Classic, editorial character
- Structured, proportional spacing
- Authoritative, sophisticated feel

### display

Bold, decorative typography for maximum impact.

**Characteristics**:
- Heavy, expressive letterforms
- Decorative elements
- Strong visual presence
- Playful or dramatic character
- Designed for headlines

**Use Cases**:
- Announcements
- Entertainment content
- Promotional materials
- Event marketing
- Gaming topics

**Prompt Hints**:
- Use bold decorative display typography
- Heavy, expressive headlines
- Strong visual impact
- Attention-grabbing character

## Default

`clean` — Universal, pairs well with most rendering styles.

## Rendering Compatibility

| Font × Rendering | flat-vector | hand-drawn | painterly | digital | pixel | chalk | screen-print |
|------------------|:-----------:|:----------:|:---------:|:-------:|:-----:|:-----:|:------------:|
| clean | ✓✓ | ✗ | ✗ | ✓✓ | ✓ | ✗ | ✓ |
| handwritten | ✓ | ✓✓ | ✓✓ | ✓ | ✗ | ✓✓ | ✗ |
| serif | ✓ | ✗ | ✓ | ✓✓ | ✗ | ✗ | ✓ |
| display | ✓✓ | ✓ | ✓ | ✓✓ | ✓✓ | ✓ | ✓✓ |

✓✓ = highly recommended | ✓ = compatible | ✗ = not recommended

## Type Compatibility

| Font × Type | hero | conceptual | typography | metaphor | scene | minimal |
|-------------|:----:|:----------:|:----------:|:--------:|:-----:|:-------:|
| clean | ✓ | ✓✓ | ✓✓ | ✓ | ✗ | ✓✓ |
| handwritten | ✓✓ | ✓ | ✓ | ✓✓ | ✓✓ | ✓ |
| serif | ✓ | ✓ | ✓✓ | ✓ | ✓ | ✓ |
| display | ✓✓ | ✓ | ✓✓ | ✓ | ✓ | ✗ |

## Palette Interaction

Font style adapts to palette characteristics:

| Palette Category | clean | handwritten | serif | display |
|------------------|-------|-------------|-------|---------|
| Warm (warm, earth, pastel) | Softer weight | Natural fit | Warm tones | Playful energy |
| Cool (cool, mono, elegant) | Perfect match | Contrast | Classic pairing | Bold statement |
| Dark (dark, vivid) | High contrast | Glow effects | Dramatic | Maximum impact |
| Vintage (retro) | Modern contrast | Nostalgic fit | Period-appropriate | Retro headlines |
| Duotone (duotone) | Sharp contrast | Not recommended | Dramatic pairing | Cinematic impact |

## Auto Selection

When `--font` is omitted, select based on signals:

| Signals | Font |
|---------|------|
| Personal, lifestyle, human, warm, friendly, story | `handwritten` |
| Technical, professional, clean, modern, minimal, data | `clean` |
| Editorial, academic, luxury, classic, literary | `serif` |
| Announcement, entertainment, promotion, bold, event, gaming | `display` |

Default: `clean`
