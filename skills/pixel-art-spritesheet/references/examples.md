# Sprite Sheet Examples

Complete examples showing the workflow from rough prompt to final output.

## Example 1: Simple Prompt → Full Spec

**User says:** "make me a cat"

**Enhanced specification:**

```
SPRITE SHEET SPECIFICATION
==============================
Subject: cute and friendly cat
Style: Pokemon GBC (4 colors)
Mood: cute, rounded, expressive

CANVAS SETUP
- Dimensions: 128x32 pixels
- Grid: 1 row × 4 columns
- Cell: 32x32 pixels per frame
- Background: #FF00FF (magenta, transparent)

COLOR PALETTE
1. #FFFFFF - highlight
2. #FFD59E - main body (orange tabby)
3. #E07038 - shadows/stripes
4. #5C3018 - outline/darkest

CHARACTER DESIGN
- Shape: compact body with large head, pointed ears, long tail
- Features: large expressive eyes, small nose, whiskers
- Facing: right

ANIMATION: Idle (4 frames)
  F1: Neutral sitting pose, tail wrapped around feet
  F2: Slight squash, tail begins to swish
  F3: Return to neutral, tail mid-swish
  F4: Slight stretch, tail completes swish
```

**Image generation prompt:**

```
Create a pixel art sprite sheet, 128x32 pixels total.

STYLE: Pokemon GBC era pixel art, 4-color palette only, clean pixels with no anti-aliasing, crisp edges, retro game aesthetic.

LAYOUT: 4 frames in a horizontal row, each frame 32x32 pixels, solid magenta #FF00FF background.

CHARACTER: A cute and friendly cat. Compact body with large head, pointed ears, long tail. Large expressive eyes, small nose, whiskers. Facing right.

PALETTE: Strictly use only these 4 colors: #FFFFFF, #FFD59E, #E07038, #5C3018

ANIMATION FRAMES (left to right):
Frame 1: Neutral sitting pose, tail wrapped around feet
Frame 2: Slight squash, tail begins to swish
Frame 3: Return to neutral, tail mid-swish
Frame 4: Slight stretch, tail completes swish

CRITICAL: No gradients, no anti-aliasing, no extra colors. Hard pixel edges only. Each frame clearly separated. Character centered in each cell with consistent size across all frames.
```

---

## Example 2: Bichon Frise Dog (Detailed)

**User says:** "A pixel art sprite sheet of a cute White Bichon Frise dog"

**Enhanced specification:**

```
SPRITE SHEET SPECIFICATION
==============================
Subject: Cute White Bichon Frise - fluffy round cloud-like dog
Style: Pokemon GBC (4 colors)
Mood: adorable, puffy, cheerful

CANVAS SETUP
- Dimensions: 192x96 pixels
- Grid: 3 rows × 6 columns
- Cell: 32x32 pixels per frame
- Background: #FF00FF (magenta, transparent)

COLOR PALETTE
1. #FFFFFF - main fluff (white)
2. #CCCCCC - light shadows
3. #666666 - dark shadows/depth
4. #000000 - outline, eyes, nose

CHARACTER DESIGN
- Shape: Round puffy "cotton ball" silhouette, cloud with legs
- Head: Perfectly round, afro-style fluff, large relative to body
- Body: Small, hidden under fluff, stubby legs barely visible
- Features: Small black dot eyes, tiny black nose, hidden mouth
- Facing: Right in all frames

ANIMATION ROW 1: Walk Cycle (6 frames, side view)
  F1: Right front paw forward (contact)
  F2: Legs gathered under body (mid-stride)
  F3: Right front paw back
  F4: Back legs stepping forward
  F5: Return to neutral
  F6: Same as F1 but 1px down (bounce)

ANIMATION ROW 2: Sit Idle (6 frames, 3/4 view)
  F1: Standing neutral
  F2: Rear legs bending, body lowering
  F3: Fully seated, looking forward
  F4: Seated, head tilts slightly
  F5: Seated, pixel heart appears above
  F6: Hold pose with heart

ANIMATION ROW 3: Bark (6 frames, side view)
  F1: Neutral stance, mouth closed
  F2: Head tilts up, mouth 50% open
  F3: Mouth fully open (bark)
  F4: Mouth fully open (hold)
  F5: Mouth closing
  F6: Return to neutral
```

---

## Example 3: NES-Style Knight

**User says:** "walking knight nes style"

**Enhanced specification:**

```
SPRITE SHEET SPECIFICATION
==============================
Subject: Armored knight warrior
Style: NES 8-bit (4 colors)
Mood: iconic, bold, heroic

CANVAS SETUP
- Dimensions: 64x16 pixels
- Grid: 1 row × 4 columns
- Cell: 16x16 pixels per frame
- Background: #FF00FF

COLOR PALETTE
1. #FFFFFF - metal highlights
2. #8888CC - armor main color
3. #4444AA - armor shadows
4. #000000 - outline

CHARACTER DESIGN
- Shape: Stocky humanoid, oversized round helmet
- Features: T-visor, sword in right hand, shield on left arm
- Proportions: 1:2 head-to-body ratio
- Facing: Right

ANIMATION: Walk (4 frames)
  F1: Right foot forward, sword down
  F2: Passing, body at highest point
  F3: Left foot forward, sword down
  F4: Passing, body at highest point
```

---

## Example 4: SNES RPG Slime

**User says:** "slime enemy for rpg"

**Enhanced specification:**

```
SPRITE SHEET SPECIFICATION
==============================
Subject: Blue gel slime monster
Style: SNES 16-bit (8 colors)
Mood: bouncy, gelatinous, cute-threatening

CANVAS SETUP
- Dimensions: 128x32 pixels
- Grid: 1 row × 4 columns
- Cell: 32x32 pixels per frame
- Background: #FF00FF

COLOR PALETTE
1. #FFFFFF - glossy highlight
2. #E0F0FF - bright gel
3. #88D8FF - main body
4. #3898DC - body shadow
5. #1C4A6E - deep shadow
6. #0A2840 - core/darkest
7. #000000 - eyes
8. #FF00FF - background

CHARACTER DESIGN
- Shape: Teardrop/dome blob, no limbs
- Features: Two simple black dot eyes, white glossy highlight top-left
- Motion: Squash and stretch throughout animation
- Facing: Centered/symmetrical

ANIMATION: Bounce (4 frames)
  F1: Neutral dome shape, resting
  F2: Squashed flat (wider, 30% shorter)
  F3: Stretched tall (narrower, 30% taller)
  F4: Settling back to neutral with slight wobble
```

---

## Quick Reference Tables

### Grid Calculations

| Frames | Rows | Cell | Canvas W | Canvas H |
|--------|------|------|----------|----------|
| 4      | 1    | 16   | 64       | 16       |
| 4      | 1    | 32   | 128      | 32       |
| 6      | 1    | 32   | 192      | 32       |
| 4      | 4    | 32   | 128      | 128      |
| 6      | 3    | 32   | 192      | 96       |
| 8      | 4    | 32   | 256      | 128      |

### Animation Frame Counts

| Animation | Min | Recommended | Notes |
|-----------|-----|-------------|-------|
| Idle      | 2   | 4           | Subtle movement |
| Walk      | 4   | 6           | Contact-pass-contact |
| Run       | 4   | 6           | Include flight phase |
| Attack    | 3   | 4           | Wind-strike-recover |
| Jump      | 3   | 4           | Crouch-air-land |
| Bounce    | 2   | 4           | Squash-stretch |

### Style Quick Reference

| Style   | Colors | Cell Size | Best For |
|---------|--------|-----------|----------|
| GB DMG  | 4      | 16x16     | Retro authenticity |
| GBC     | 4      | 32x32     | Pokemon-style creatures |
| NES     | 4      | 16x16     | Classic platformers |
| SNES    | 8-16   | 32-48     | Detailed RPG sprites |
