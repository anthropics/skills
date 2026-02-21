# SVG Maps — Asset Index

This directory contains SVG asset maps for each character: per-character rig breakdowns with named groups, pivot points, and z-layer ordering.

SVG maps are generated from the character board specifications and the skill template at `skills/character-board/templates/`.

---

## Status

| Character | Style | SVG Map | Status |
|---|---|---|---|
| The Anchor | South Park flat | `the-anchor.svg` | Pending |
| The MAGA Cultist | South Park flat | `maga-cultist.svg` | Pending |
| The Typical Leftist | South Park flat | `typical-leftist.svg` | Pending |
| The Informed Person | Boondocks fluid | `informed-person.svg` | Pending |
| The Opportunist | Boondocks fluid | `opportunist.svg` | Pending |
| The Talking Head | South Park flat | `talking-head.svg` | Pending |

---

## South Park Flat — Standard Part List

South Park flat characters use an 8-part rig. All parts in a single SVG file, each in a named `<g>` group.

```
head
body
left-arm
right-arm
left-leg
right-leg
accessory-1        ← character-specific (cap, tote bag, tablet, etc.)
accessory-2        ← character-specific (phone, earpiece, book, etc.)
```

Registration point per part:

| Part | Pivot |
|---|---|
| `head` | Geometric center of head circle |
| `body` | Torso center |
| `left-arm` | Shoulder joint (top of arm shape) |
| `right-arm` | Shoulder joint |
| `left-leg` | Hip joint (top of leg shape) |
| `right-leg` | Hip joint |
| `accessory-1` | Geometric center |
| `accessory-2` | Geometric center |

---

## Boondocks Fluid — Standard Part List

Boondocks fluid characters use a 22-part rig. All parts in a single SVG, each in a named `<g>` group with `transform-origin` set at the pivot point.

```
hair-back
head
hair-front
face
left-eye
right-eye
mouth
neck
torso
left-upper-arm
left-forearm
left-hand
right-upper-arm
right-forearm
right-hand
pelvis
left-thigh
left-shin
left-foot
right-thigh
right-shin
right-foot
outfit-overlay     ← clothing detail layer over body segments
accessory-1        ← character-specific
accessory-2        ← character-specific
```

Registration point per part:

| Part | Pivot |
|---|---|
| `head` | Neck connection point |
| `hair-front` / `hair-back` | Top of head |
| `left-upper-arm` / `right-upper-arm` | Shoulder joint |
| `left-forearm` / `right-forearm` | Elbow joint |
| `left-hand` / `right-hand` | Wrist joint |
| `left-thigh` / `right-thigh` | Hip joint |
| `left-shin` / `right-shin` | Knee joint |
| `left-foot` / `right-foot` | Ankle joint |
| `torso` | Waist center |
| `accessory-*` | Geometric center |

---

## SVG Group Convention

```svg
<g id="[part-name]" style="transform-origin: [px] [py]px;">
  <!-- shapes for this part -->
</g>
```

All `transform-origin` values are set in the coordinate space of the full SVG viewBox, not relative to the group's own bounding box.

---

## Character-Specific Accessories

| Character | accessory-1 | accessory-2 |
|---|---|---|
| The Anchor | Earpiece + cord | Papers on desk |
| The MAGA Cultist | Red cap | Phone (mid-scroll) |
| The Typical Leftist | Tote bag | Reusable coffee cup |
| The Informed Person | Glasses (separate layer) | Book / newspaper |
| The Opportunist | Business card | Phone (multi-app) |
| The Talking Head | Tablet | — |

---

## Generation Notes

SVG maps are produced using the skill template at:

```
skills/character-board/templates/south-park/svg-assets/asset-map.svg
skills/character-board/templates/boondocks/svg-assets/asset-map.svg
```

When generating a character's SVG map:
1. Start from the appropriate style template
2. Apply the character's color palette (from `assets/color-palettes/`)
3. Adjust geometry for the character's specific build
4. Rename `accessory-1` and `accessory-2` groups to match the character's props
5. Set all `transform-origin` values at joint centers

---

## File Format Requirements

- Format: SVG 1.1
- ViewBox: `0 0 400 600` (South Park) or `0 0 400 700` (Boondocks)
- All fills: flat color attributes (no inline gradients) for South Park
- All fills: flat base + shadow layer group for Boondocks
- Outline: `stroke-width="3"` (South Park), `stroke-width="4"` contour + `stroke-width="2"` interior (Boondocks)
- No embedded raster images
- No external font dependencies
