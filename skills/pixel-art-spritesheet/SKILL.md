---
name: pixel-art-spritesheet
description: Create pixel art sprite sheets and animations. Use when user wants pixel art, sprites, game characters, retro graphics, walk cycles, idle animations, or character sheets. Triggers on requests involving: pixel art, sprites, 8-bit, 16-bit, retro game graphics, sprite sheets, character animations, Game Boy style, NES style, SNES style, Pokemon style.
---

# Pixel Art Sprite Sheet Creator

Create beautiful pixel art sprite sheets from simple descriptions.

## Quick Start - Default Demo

When skill loads with no specific request, offer this default:

> "I'll create a demo sprite sheet for you - a cute slime creature with a 4-frame bounce animation. This shows the skill in action. Want me to generate it, or describe what character you'd like instead?"

**Default Demo Spec:**
- Character: Blue slime blob
- Style: SNES RPG
- Canvas: 128x32 (4 frames, 32x32 each)
- Animation: Idle bounce

## Agent Workflow

Follow this workflow for every request:

### Step 1: Parse User Intent

Extract from user's message:
- **Subject**: What character/creature/object? (default: "cute slime")
- **Style**: What era/aesthetic? (default: "Pokemon GBC")
- **Animation**: What action? (default: "idle bounce")
- **Size**: How detailed? (default: 32x32 cells)

If the user prompt is vague like "make me a cat sprite", that's fine - use smart defaults.

### Step 2: Generate Detailed Spec

Transform the user's rough idea into a complete specification using this template:

```
SPRITE SHEET SPECIFICATION
==========================
Subject: [character] - [1-2 sentence visual description]
Style: [console/era] ([color count] colors)
Mood: [personality/feeling the sprite conveys]

CANVAS SETUP
- Dimensions: [W]x[H] pixels
- Grid: [R] rows × [C] columns
- Cell: [W]x[H] pixels per frame
- Background: #FF00FF (magenta, transparent)

COLOR PALETTE
1. [Hex] - [usage: outline/shadow/main/highlight]
2. [Hex] - [usage]
3. [Hex] - [usage]
4. [Hex] - [usage]

CHARACTER DESIGN
- Shape: [overall silhouette - be specific]
- Head: [size ratio, features]
- Body: [proportions]
- Details: [eyes, mouth, accessories]
- Facing: [direction, consistency rule]

ANIMATION: [Name] ([frame count] frames)
Row 1:
  F1: [detailed pose description]
  F2: [detailed pose description]
  F3: [detailed pose description]
  F4: [detailed pose description]
```

### Step 3: Generate the Image

Use the spec to create the actual sprite sheet:

**Option A - AI Image Generation (Recommended)**
Generate an image prompt optimized for AI image generators:

```
Create a pixel art sprite sheet, [W]x[H] pixels total.

STYLE: [console] era pixel art, [N]-color palette only, clean pixels with no anti-aliasing, crisp edges, retro game aesthetic.

LAYOUT: [C] frames in a horizontal row, each frame [cell_w]x[cell_h] pixels, solid magenta #FF00FF background.

CHARACTER: [detailed visual description from spec]

PALETTE: Strictly use only these [N] colors: [list hex codes]

ANIMATION FRAMES (left to right):
Frame 1: [pose]
Frame 2: [pose]
Frame 3: [pose]
Frame 4: [pose]

CRITICAL: No gradients, no anti-aliasing, no extra colors. Hard pixel edges only. Each frame clearly separated. Character centered in each cell.
```

**Option B - Programmatic Generation**
Run the bundled script for simple sprites:
```bash
python scripts/generate_sprite.py --spec "spec.json" --output "sprite.png"
```

### Step 4: Deliver to User

Provide:
1. The generated sprite sheet image
2. The full specification (for iteration)
3. Animation preview tip: "Open in any sprite editor and set frame delay to 100-200ms"

## Prompt Enhancement Examples

| User Says | Enhanced To |
|-----------|-------------|
| "cat sprite" | Cute orange tabby cat, Pokemon GBC style, 4-color, 32x32, sitting idle with tail swish |
| "knight" | Armored knight, NES style, 4-color, 16x16, walk cycle 4 frames |
| "make a dog" | Fluffy white dog (Bichon style), GBC style, 4-color, 32x32, happy bounce animation |
| "dragon" | Baby dragon, SNES style, 8-color, 48x48, wing flap idle |
| "slime enemy" | Blue gel slime, SNES RPG style, 4-color, 32x32, squash-stretch bounce |

## Style Presets

### Pokemon GBC (Default)
```
Colors: 4 (white, light, dark, black)
Cell: 32x32
Feel: Cute, rounded, expressive
Best for: Creatures, characters, Pokemon-likes
```

### NES 8-bit
```
Colors: 4 (1 transparent + 3)
Cell: 16x16 or 8x16
Feel: Iconic, simple, bold silhouettes
Best for: Classic game characters, enemies
```

### SNES 16-bit
```
Colors: 8-16
Cell: 32x32 or 48x48
Feel: Detailed, smooth, vibrant
Best for: RPG characters, detailed creatures
```

### Game Boy DMG
```
Colors: 4 (green palette)
Cell: 16x16
Feel: Nostalgic, limited, charming
Best for: Retro authenticity
```

## Animation Templates

### Idle Bounce (4 frames) - Great default
```
F1: Neutral pose
F2: Slight squash (1-2px shorter)
F3: Neutral pose
F4: Slight stretch (1-2px taller)
```

### Walk Cycle (4 frames)
```
F1: Right foot forward (contact)
F2: Passing (feet together)
F3: Left foot forward (contact)
F4: Passing (feet together)
```

### Attack (4 frames)
```
F1: Wind up (lean back)
F2: Strike (extend forward)
F3: Impact (full extension)
F4: Recovery (return to neutral)
```

### Emote/React (4 frames)
```
F1: Neutral
F2: Surprised (eyes wide, slight jump)
F3: Emote particle appears (!, ?, ♥)
F4: Hold with particle
```

## Color Palette Quick Reference

### Grayscale (Classic GB)
`#FFFFFF` `#AAAAAA` `#555555` `#000000`

### Green GB
`#9BBC0F` `#8BAC0F` `#306230` `#0F380F`

### Warm Creature
`#FFFFFF` `#FFD59E` `#E07038` `#5C3018`

### Cool Creature
`#FFFFFF` `#88D8FF` `#3898DC` `#1C4A6E`

### Forest
`#E8F0C8` `#88C070` `#389050` `#183028`

### Fire
`#FFF8C0` `#F8B830` `#E05010` `#582010`

## Quality Rules

ALWAYS ensure:
- Exact color count (no extra colors from anti-aliasing)
- Magenta background (#FF00FF) for transparency
- Consistent character size across all frames
- Clear silhouette readable at 1x zoom
- Smooth animation loop (last frame connects to first)
- Character facing same direction in all frames (unless turning animation)

## Output Formats

Provide the user with:

1. **PNG Image**: The sprite sheet file
2. **Spec Document**: Full specification for iteration
3. **Quick Stats**: "4 frames, 32x32 each, 128x32 total, 4 colors"

## Iteration Support

When user wants changes:
- "bigger" → Increase cell size (32→48 or 48→64)
- "more frames" → Add intermediate poses
- "different colors" → Swap palette, keep structure
- "cuter" → Larger head ratio, rounder shapes, bigger eyes
- "fiercer" → Sharper angles, smaller eyes, aggressive pose
