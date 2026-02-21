---
name: character-board
description: Build production-ready character boards for 2D animation targeting South Park flat-cutout style and Boondocks anime style. Use this when the user requests character sheets, model sheets, SVG asset maps, animation rigs, color palettes, or geometry reference guides for animated characters.
license: Complete terms in LICENSE.txt
---

# Character Board Skill

Create structured character board packages for 2D animation. Output SVG files organized into four domains: **specs**, **color-palettes**, **geometry**, and **svg-assets**. All output must respect the target style's visual language.

## Supported Styles

| Style | Key Traits |
|---|---|
| `south-park` | Flat cutout, bold fills, minimal outlines, simple geometry, zero shading |
| `boondocks` | Anime-influenced, angular lines, strong outlines, 6–7 head heights, cel shading |

---

## Workflow

Complete the board in four sequential phases. For each phase, produce SVG files saved to the correct subdirectory under `templates/<style>/`.

---

### Phase 1 — Character Specs (`specs/`)

Create a **model sheet** SVG containing:
- Three orthographic views: **front · ¾ turn · side profile**
- A **height scale bar** in "heads" (1 head = head height unit)
- An **expression strip** of 4–6 keyframe faces (neutral, happy, angry, surprised, sad, determined)
- Text labels for character name, version, and date

**South Park rules:**
- Head is a near-perfect circle (~⅓ total body height)
- Body is a trapezoid or oval; arms/legs are stubby pill shapes
- Eyes are two simple dots; mouth is a thin arc
- No perspective distortion — pure flat orthographic

**Boondocks rules:**
- Head is ≈1/6 to 1/7 of total height
- Angular jaw; large eyes placed at vertical midpoint of head
- Facial thirds: forehead / brow-to-nose / nose-to-chin each ≈1/3 of face height
- 3/4 view shows clear nose bridge and far-eye foreshortening

Output: `character-spec.svg`

---

### Phase 2 — Color Palettes (`color-palettes/`)

Create a **swatch board** SVG containing named, hex-coded color groups.

**Required groups (both styles):**

| Group | Swatches |
|---|---|
| Skin | base, shadow, highlight |
| Hair | base, shadow, accent |
| Outfit Primary | base, shadow, highlight |
| Outfit Secondary | base, shadow |
| Eyes | iris, pupil, white, reflection |
| Outline | main, secondary |

**South Park rules:**
- Flat fills only — shadow = same hue, 20% darker; no gradients
- Palette max 12 total colors
- Outline is always solid black `#1a1a1a`

**Boondocks rules:**
- Cel-shade approach: base + one shadow stop (multiply blend)
- Highlight can be a separate lighter tone or rim-light color
- Allow up to 20 total colors
- Outline varies by plane: thick contour, thin interior

Output: `palette.svg`

---

### Phase 3 — Geometry References (`geometry/`)

Create a **construction guide** SVG with:
- Underlying shape primitives (circles, ellipses, rectangles, polygons)
- Centerline axis (vertical + horizontal cross)
- Proportion ruler with labeled head-unit tick marks
- Annotations for key measurements

**South Park rules:**
- Primary shapes: 1 large circle (head), 1 oval/trapezoid (body), 4 pill shapes (limbs)
- Head ≈ 33% of total height; body ≈ 42%; legs ≈ 25%
- Show snap-to-grid: 16px grid

**Boondocks rules:**
- Head = circle + flattened chin polygon
- Facial cross: horizontal line at eye level, vertical centerline
- Facial thirds lines: hairline / brow / nose-base / chin
- Body = tapered torso box, pelvis box; limbs segmented (upper arm / forearm / hand)
- Show 7-heads-tall proportion ruler

Output: `construction-guide.svg`

---

### Phase 4 — SVG Asset Maps (`svg-assets/`)

Create an **asset map** SVG that breaks the character into independently transformable parts for rigging. Each part must be:
- A named `<g id="part-name">` group
- Drawn with a distinct bounding box label
- Annotated with its layer order (z-index)

**South Park parts (simple rig):**

```
head · body · left-arm · right-arm · left-leg · right-leg · accessory-1 · accessory-2
```

Registration point for each part: joint center or geometric center.

**Boondocks parts (detailed rig):**

```
hair-back · head · hair-front · face · left-eye · right-eye · mouth
neck · torso · left-upper-arm · left-forearm · left-hand
right-upper-arm · right-forearm · right-hand
pelvis · left-thigh · left-shin · left-foot
right-thigh · right-shin · right-foot
outfit-overlay · accessory-1 · accessory-2
```

Output: `asset-map.svg`

---

## Shared Assets

Reusable assets across both styles live in `templates/shared/`:

- `color-palettes/skin-tones.svg` — universal skin tone reference chart
- `geometry/base-grid.svg` — 16px snap grid overlay (import into other SVGs)

---

## Output Checklist

For each character, produce:

- [ ] `templates/<style>/specs/character-spec.svg`
- [ ] `templates/<style>/color-palettes/palette.svg`
- [ ] `templates/<style>/geometry/construction-guide.svg`
- [ ] `templates/<style>/svg-assets/asset-map.svg`

Name additional characters by prefixing: `<character-name>-spec.svg`, `<character-name>-palette.svg`, etc.

---

## Style Quick-Reference

### South Park Visual Language
- Stroke: `stroke-width="3"` solid black only
- Fill: flat `fill` attribute — no gradients, no filters
- Font: Bold sans-serif, all-caps labels
- Shapes: prefer `<circle>`, `<ellipse>`, `<rect>`, `<path>` with rounded corners

### Boondocks Visual Language
- Stroke: `stroke-width="4"` contour, `stroke-width="2"` interior
- Fill: base color layer + `<feColorMatrix>` or multiply overlay for cel shadow
- Font: Medium-weight sans-serif, title-case labels
- Shapes: angular `<polygon>` and `<path>` with sharp corners for face/jaw; curved paths for hair
