# Outline Template

Standard structure for slide deck outlines with style instructions.

## Outline Format

```markdown
# Slide Deck Outline

**Topic**: [topic description]
**Style**: [preset name OR "custom"]
**Dimensions**: [texture] + [mood] + [typography] + [density]
**Audience**: [target audience]
**Language**: [output language]
**Slide Count**: N slides
**Generated**: YYYY-MM-DD HH:mm

---

<STYLE_INSTRUCTIONS>
Design Aesthetic: [2-3 sentence description combining dimension characteristics]

Background:
  Texture: [from texture dimension]
  Base Color: [from mood dimension palette]

Typography:
  Headlines: [from typography dimension - describe visual appearance]
  Body: [from typography dimension - describe visual appearance]

Color Palette:
  Primary Text: [Name] ([Hex]) - [usage]
  Background: [Name] ([Hex]) - [usage]
  Accent 1: [Name] ([Hex]) - [usage]
  Accent 2: [Name] ([Hex]) - [usage]

Visual Elements:
  - [element 1 from texture + mood combination]
  - [element 2 with rendering guidance]
  - ...

Density Guidelines:
  - Content per slide: [from density dimension]
  - Whitespace: [from density dimension]

Style Rules:
  Do: [guidelines from dimension combinations]
  Don't: [anti-patterns from dimension combinations]
</STYLE_INSTRUCTIONS>

---

[Slide entries follow...]
```

## Building STYLE_INSTRUCTIONS from Dimensions

When using custom dimensions or presets, build STYLE_INSTRUCTIONS by combining:

### 1. Design Aesthetic

Combine characteristics from all four dimensions into 2-3 sentences:

| Texture | Contribution |
|---------|--------------|
| clean | "Clean, digital precision with crisp edges" |
| grid | "Technical grid overlay with engineering precision" |
| organic | "Hand-drawn feel with soft textures" |
| pixel | "Chunky pixel aesthetic with 8-bit charm" |
| paper | "Aged paper texture with vintage character" |

| Mood | Contribution |
|------|--------------|
| professional | "Professional navy and gold palette" |
| warm | "Warm earth tones creating approachable atmosphere" |
| cool | "Cool analytical blues and grays" |
| vibrant | "Bold, high-saturation colors with energy" |
| dark | "Deep cinematic backgrounds with glowing accents" |
| neutral | "Minimal grayscale sophistication" |

### 2. Background

From `references/dimensions/texture.md`:
- Texture description
- Base color from mood palette

### 3. Typography

From `references/dimensions/typography.md`:
- Headline visual description (NOT font names)
- Body text visual description (NOT font names)

**Important**: Describe appearance for image generation: "bold geometric sans-serif with perfect circular O shapes" NOT "Inter font".

### 4. Color Palette

From `references/dimensions/mood.md`:
- Copy the palette specifications for the selected mood
- Include hex codes and usage notes

### 5. Visual Elements

Combine texture and mood characteristics:

| Combination | Visual Elements |
|-------------|-----------------|
| clean + professional | Clean charts, outlined icons, structured grids |
| grid + cool | Technical schematics, dimension lines, blueprints |
| organic + warm | Hand-drawn icons, brush strokes, doodles |
| pixel + vibrant | Pixel art icons, retro game elements |
| paper + warm | Vintage stamps, aged elements, sepia overlays |

### 6. Density Guidelines

From `references/dimensions/density.md`:
- Content per slide limits
- Whitespace requirements
- Element count guidelines

### 7. Style Rules

Combine dimension-specific rules:

**Do rules by texture**:
- clean: Maintain sharp edges, use grid alignment
- grid: Show precise measurements, use technical diagrams
- organic: Allow imperfection, layer with subtle overlaps
- pixel: Keep aliased edges, use chunky elements
- paper: Add subtle aging effects, use warm tones

**Don't rules by texture**:
- clean: Don't use hand-drawn elements
- grid: Don't use organic curves
- organic: Don't use perfect geometry
- pixel: Don't smooth edges
- paper: Don't use bright digital colors

## Cover Slide Template

```markdown
## Slide 1 of N

**Type**: Cover
**Filename**: 01-slide-cover.png

// NARRATIVE GOAL
[What this slide achieves in the story arc]

// KEY CONTENT
Headline: [main title]
Sub-headline: [supporting tagline]

// VISUAL
[Detailed visual description - specific elements, composition, mood]

// LAYOUT
Layout: [optional: layout name from gallery, e.g., title-hero]
[Composition, hierarchy, spatial arrangement]
```

## Content Slide Template

```markdown
## Slide X of N

**Type**: Content
**Filename**: {NN}-slide-{slug}.png

// NARRATIVE GOAL
[What this slide achieves in the story arc]

// KEY CONTENT
Headline: [main message - narrative, not label]
Sub-headline: [supporting context]
Body:
- [point 1 with specific detail]
- [point 2 with specific detail]
- [point 3 with specific detail]

// VISUAL
[Detailed visual description]

// LAYOUT
Layout: [optional: layout name from gallery]
[Composition, hierarchy, spatial arrangement]
```

## Back Cover Slide Template

```markdown
## Slide N of N

**Type**: Back Cover
**Filename**: {NN}-slide-back-cover.png

// NARRATIVE GOAL
[Meaningful closing - not just "thank you"]

// KEY CONTENT
Headline: [memorable closing statement or call-to-action]
Body: [optional summary points or next steps]

// VISUAL
[Visual that reinforces the core message]

// LAYOUT
Layout: [optional: layout name from gallery]
[Clean, impactful composition]
```

## STYLE_INSTRUCTIONS Block

The `<STYLE_INSTRUCTIONS>` block is the SINGLE SOURCE OF TRUTH for style information in this outline.

| Section | Content | Source |
|---------|---------|--------|
| Design Aesthetic | Overall visual direction | Combined from all dimensions |
| Background | Base color and texture details | texture + mood dimensions |
| Typography | Font descriptions (visual, not names) | typography dimension |
| Color Palette | Named colors with hex codes and usage | mood dimension |
| Visual Elements | Graphic elements with rendering instructions | texture + mood dimensions |
| Density Guidelines | Content limits and whitespace | density dimension |
| Style Rules | Do/Don't guidelines | Combined from dimensions |

**Important**:
- Typography descriptions must describe visual appearance (e.g., "rounded sans-serif", "bold geometric") since image generators cannot use font names
- Prompts should extract STYLE_INSTRUCTIONS from this outline, NOT re-read style files

## Preset → Dimensions Reference

When using a preset, look up dimensions in `references/dimensions/presets.md`:

| Preset | Dimensions |
|--------|------------|
| blueprint | grid + cool + technical + balanced |
| sketch-notes | organic + warm + handwritten + balanced |
| corporate | clean + professional + geometric + balanced |
| minimal | clean + neutral + geometric + minimal |
| ... | See presets.md for full mapping |

## Section Dividers

Use `---` (horizontal rule) between:
- Header metadata and STYLE_INSTRUCTIONS
- STYLE_INSTRUCTIONS and first slide
- Each slide entry

## Slide Numbering

- Cover is always Slide 1
- Content slides use sequential numbers
- Back Cover is always final slide (N)
- Filename prefix matches slide position: `01-`, `02-`, etc.

## Filename Slugs

Generate meaningful slugs from slide content:

| Slide Type | Slug Pattern | Example |
|------------|--------------|---------|
| Cover | `cover` | `01-slide-cover.png` |
| Content | `{topic-slug}` | `02-slide-problem-statement.png` |
| Back Cover | `back-cover` | `10-slide-back-cover.png` |

Slug rules:
- Kebab-case (lowercase, hyphens)
- Derived from headline or main topic
- Maximum 30 characters
- Unique within deck
