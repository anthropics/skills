# Design Guidelines

Detailed design principles for slide decks.

## Audience Guidelines

Design decisions adapt to target audience. Use `--audience` to set.

| Audience | Content Density | Visual Style | Terminology | Slides |
|----------|-----------------|--------------|-------------|--------|
| `beginners` | Low | Friendly, illustrative | Plain language | 8-15 |
| `intermediate` | Medium | Balanced, structured | Some jargon OK | 10-20 |
| `experts` | High | Data-rich, precise | Technical terms | 12-25 |
| `executives` | Low-Medium | Clean, impactful | Business language | 8-12 |
| `general` | Medium | Accessible, engaging | Minimal jargon | 10-18 |

### Audience → Density Mapping

Recommended density dimension based on audience:

| Audience | Recommended Density | Rationale |
|----------|-------------------|-----------|
| `executives` | minimal | One insight per slide, respect time |
| `beginners` | minimal → balanced | Single concepts, build understanding |
| `general` | balanced | Accessible but informative |
| `intermediate` | balanced | Standard information density |
| `experts` | balanced → dense | Can handle more data per slide |

**Automatic Density Selection**:
- If `--audience executives` → default to `minimal` density
- If `--audience beginners` → default to `minimal` or `balanced`
- If `--audience experts` → allow `dense` density
- Otherwise → default to `balanced`

### Audience-Specific Principles

**Beginners**:
- One concept per slide
- Visual metaphors over abstract diagrams
- Step-by-step progression
- Generous whitespace

**Experts**:
- Multiple data points per slide acceptable
- Technical diagrams with precise labels
- Assume domain knowledge
- Dense but organized information

**Executives**:
- Lead with insights, not data
- "So what?" on every slide
- Decision-enabling content
- Bottom-line upfront (BLUF)

## Visual Hierarchy Principles

| Principle | Description |
|-----------|-------------|
| Focal Point | ONE dominant element per slide draws attention first |
| Rule of Thirds | Position key elements at grid intersections |
| Z-Pattern | Guide eye: top-left → top-right → bottom-left → bottom-right |
| Size Contrast | Headlines 2-3x larger than body text |
| Breathing Room | Minimum 10% margin from all edges |

## Content Density

See `references/dimensions/density.md` for full density dimension specs.

| Level | Description | Use When |
|-------|-------------|----------|
| High | Multiple data points, detailed charts, dense text | Expert audience, technical reviews |
| Medium | Key points with supporting details | General business, mixed audiences |
| Low | One main idea, large visuals, minimal text | Beginners, keynotes, emotional impact |

**High-Density Principles** (McKinsey-style):
- Every element earns its space
- Data speaks louder than decoration
- Annotations explain insights, not describe data
- White space is strategic, not filler

**Density by Slide Type**:
| Slide Type | Recommended Density |
|------------|-------------------|
| Cover/Title | minimal |
| Agenda/Overview | balanced |
| Content/Analysis | balanced or dense |
| Data/Metrics | dense |
| Quote/Impact | minimal |
| Summary/Takeaway | balanced |

## Color Selection

See `references/dimensions/mood.md` for full mood dimension specs.

**Content-First Approach**:
1. Analyze content topic, mood, and industry
2. Consider target audience expectations
3. Match palette to subject matter
4. Ensure strong contrast for readability

**Quick Palette Guide**:
| Content Type | Recommended Mood |
|--------------|-----------------|
| Technical/Architecture | cool |
| Educational/Friendly | warm |
| Corporate/Professional | professional |
| Creative/Artistic | vibrant |
| Scientific/Medical | cool or neutral |
| Entertainment/Gaming | dark or vibrant |

## Typography Principles

See `references/dimensions/typography.md` for full typography dimension specs.

| Element | Treatment |
|---------|-----------|
| Headlines | Bold, 2-3x body size, narrative style |
| Body Text | Regular weight, readable size |
| Captions | Smaller, lighter weight |
| Data Labels | Monospace for technical content |
| Emphasis | Use bold or color, not underlines |

## Font Recommendations

**English Fonts**:
| Font | Style | Best For |
|------|-------|----------|
| Liter | Sans-serif, geometric | Modern, clean, technical |
| HedvigLettersSans | Sans-serif, distinctive | Brand-forward, creative |
| Oranienbaum | High-contrast serif | Elegant, classical |
| SortsMillGoudy | Classical serif | Traditional, readable |
| Coda | Round sans-serif | Friendly, approachable |

**Chinese Fonts**:
| Font | Style | Best For |
|------|-------|----------|
| MiSans | Modern sans-serif | Clean, versatile, screen-optimized |
| Noto Sans SC | Neutral sans-serif | Standard, multilingual |
| siyuanSongti | Refined Song typeface | Elegant, editorial |
| alimamashuheiti | Geometric sans-serif | Commercial, structured |
| LXGW Bright | Song-Kai hybrid | Warm, readable |

**Multilingual Pairing**:
| Use Case | English | Chinese |
|----------|---------|---------|
| Technical | Liter | MiSans |
| Editorial | Oranienbaum | siyuanSongti |
| Friendly | Coda | LXGW Bright |
| Corporate | HedvigLettersSans | alimamashuheiti |

## Visual Elements Reference

See `references/dimensions/texture.md` for full texture dimension specs.

### Background Treatments

| Treatment | Description | Best For |
|-----------|-------------|----------|
| Solid color | Single background color | Clean, minimal |
| Split background | Two colors, diagonal or vertical | Contrast, sections |
| Gradient | Subtle vertical or diagonal fade | Modern, dynamic |
| Textured | Pattern or texture overlay | Character, style |

### Typography Treatments

| Treatment | Description | Best For |
|-----------|-------------|----------|
| Size contrast | 3-4x difference headline vs body | Impact, hierarchy |
| All-caps headers | Uppercase with letter spacing | Authority, structure |
| Monospace data | Fixed-width for numbers/code | Technical, precision |
| Hand-drawn | Organic, imperfect letterforms | Friendly, approachable |

### Geometric Accents

| Element | Description | Best For |
|---------|-------------|----------|
| Diagonal dividers | Angled section separators | Energy, movement |
| Corner brackets | L-shaped frames | Focus, framing |
| Circles/hexagons | Shape frames for images | Modern, tech |
| Underline accents | Thick lines under headers | Emphasis, hierarchy |

## Consistency Requirements

| Element | Guideline |
|---------|-----------|
| Spacing | Consistent margins and padding throughout |
| Colors | Maximum 3-4 colors per slide, palette consistent across deck |
| Typography | Same font families and sizes for same content types |
| Visual Language | Repeat patterns, shapes, and treatments |

## Dimension Combination Guide

When combining dimensions, consider compatibility:

| Audience | Recommended Dimensions |
|----------|----------------------|
| Executives | clean + neutral + geometric + minimal |
| Beginners | organic + warm + humanist + minimal |
| General | any texture + any mood + humanist/geometric + balanced |
| Experts | grid/clean + cool + technical + balanced/dense |

| Content Type | Recommended Dimensions |
|--------------|----------------------|
| Tutorial | organic + warm + handwritten + balanced |
| Technical | grid + cool + technical + balanced |
| Business | clean + professional + geometric + balanced |
| Creative | organic + vibrant + humanist + balanced |
| Data-heavy | clean + cool + technical + dense |
