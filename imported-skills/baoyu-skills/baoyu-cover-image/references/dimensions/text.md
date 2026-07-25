---
name: text-dimension
description: Text density dimension for cover images
---

# Text Dimension

Controls text density and information hierarchy on cover images.

## Values

| Value | Title | Subtitle | Tags | Visual Area |
|-------|:-----:|:--------:|:----:|:-----------:|
| `none` | - | - | - | 100% |
| `title-only` | ✓ | - | - | 85% |
| `title-subtitle` | ✓ | ✓ | - | 75% |
| `text-rich` | ✓ | ✓ | ✓ (2-4) | 60% |

## Detail

### none

Pure visual cover with no text elements.

**Use Cases**:
- Photography-focused covers
- Abstract art pieces
- Visual-only social sharing
- When title added externally

**Composition**:
- Full visual area available
- No reserved text zones
- Emphasis on visual metaphor

### title-only

Single headline, maximum impact.

**Use Cases**:
- Most article covers (default)
- Clear single message
- Strong brand recognition

**Composition**:
- Title: prominent placement
- Reserved zone: top or bottom 15%
- Visual supports title message

**Title Guidelines**:
- Use exact title from source content or user-provided title
- Do NOT invent or modify titles
- Match content language

### title-subtitle

Title with supporting context.

**Use Cases**:
- Technical articles needing clarification
- Series with episode/part info
- Content with dual messages

**Composition**:
- Title: primary element
- Subtitle: secondary element
- Reserved zone: 25%
- Clear hierarchy between title/subtitle

**Title Guidelines**:
- Use exact title from source content or user-provided title
- Do NOT invent or modify titles

**Subtitle Guidelines**:
- Clarify or contextualize title
- Can include series name, author, date
- Smaller, less prominent than title

### text-rich

Information-dense cover with multiple text elements.

**Use Cases**:
- Infographic-style covers
- Event announcements with details
- Promotional material with features
- Content with multiple key points

**Composition**:
- Title: primary focus
- Subtitle: supporting info
- Tags: 2-4 keyword labels
- Reserved zone: 40%
- Clear visual hierarchy

**Title Guidelines**:
- Use exact title from source content or user-provided title
- Do NOT invent or modify titles

**Tag Guidelines**:
- 2-4 tags maximum
- Short keywords (1-2 words each)
- Positioned as badges/labels
- Can highlight: category, date, author, key features

## Type Compatibility

| Type | none | title-only | title-subtitle | text-rich |
|------|:----:|:----------:|:--------------:|:---------:|
| hero | ✓ | ✓✓ | ✓✓ | ✓ |
| conceptual | ✓✓ | ✓✓ | ✓ | ✓ |
| typography | ✗ | ✓ | ✓✓ | ✓✓ |
| metaphor | ✓✓ | ✓ | ✓ | ✗ |
| scene | ✓✓ | ✓ | ✓ | ✗ |
| minimal | ✓✓ | ✓✓ | ✓ | ✗ |

✓✓ = highly recommended | ✓ = compatible | ✗ = not recommended

## Auto Selection

When `--text` is omitted, select based on signals:

| Signals | Text Level |
|---------|------------|
| Visual-only, photography, abstract, art | `none` |
| Article, blog, standard cover | `title-only` |
| Series, tutorial, technical with context | `title-subtitle` |
| Announcement, features, multiple points, infographic | `text-rich` |

Default: `title-only`
