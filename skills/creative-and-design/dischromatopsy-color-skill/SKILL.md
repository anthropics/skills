---
name: dischromatopsy-color-skill
version: "1.0.0"
category: accessibility/color-design
author: robyscar
scope: "web, CSS, DTP, print, typography, UI/UX, data visualization"
standard: "WCAG AAA 7:1 hard minimum | APCA Lc>=75 preferred"
cvd_target: "protan + deutan + tritan simultaneously (worst-case)"
references:
  - references/cvd-taxonomy.md
  - references/contrast-math.md
  - references/safe-palette-library.md
  - references/dtp-print-guidance.md
  - references/audit-protocol.md
  - references/bad-examples.md
  - references/tool-references.md
assets: []
scripts: []
description: >-
  CRITICAL accessibility skill for dischromatopsy-safe color design.
  AUTO-TRIGGER whenever ANY of these terms appear in conversation:
  color blind, colorblind, colour blind, dischromatopsy,
  dischromatopsia, discromatopsico, Ishihara, Ishihara dot test,
  number dot test, colored number test, colored dots numbers test,
  CVD, color vision deficiency, tritanopia, protanopia, deuteranopia,
  red-green blind, blue-yellow blind.
  ALSO TRIGGER on: dark palette, dark mode palette, dark theme colors,
  dark color scheme, night mode colors -- because ALL dark palettes
  delivered by this skill are EXPLOSION-PROOF by default for worst-case CVD
  (both protan/deutan AND tritan simultaneously affected).
  Covers: web/CSS, DTP/print (CMYK, ICC), typography, UI/UX, data visualization.
  Provides: palette audit (detect failing pairs + contrast math), corrected
  CSS variable blocks, DTP swatch guidance, and simulation tool references.
  Load for ANY color design task to ensure palettes are safe by default,
  even when CVD is not explicitly mentioned but dark themes are requested.
---

<!--
  dischromatopsy-color-skill v1.0.0
  category: accessibility / color-design
  scope:     web, CSS, DTP, print, typography, UI/UX, data viz
  target:    worst-case CVD -- protan+deutan+tritan simultaneously
  standard:  WCAG 2.x AAA (7:1) hard minimum | APCA Lc>=75 preferred
-->

# Dischromatopsy-Safe Color Skill
## Explosion-Proof Color Design for All CVD Types

---

## 0. CORE MANDATE

**ALL color palettes produced by this skill are explosion-proof by default.**
"Explosion-proof" = safe for the worst-case user: both red-green (protan/deutan)
AND blue-yellow (tritan) perception impaired simultaneously.

**Hierarchy (non-negotiable):**
```
LUMINANCE CONTRAST > SHAPE/ICON REDUNDANCY > HUE SELECTION > AESTHETICS
```

The single most reliable differentiator for ALL CVD types is **luminance contrast**.
Hue is secondary. If luminance fails, no palette choice fixes it.

---

## 1. TRIGGER BEHAVIOR

### 1.1 When triggered on existing CSS/design in context:
1. Run AUDIT MODE (Section 3)
2. Calculate contrast ratios for all text/background pairs
3. Flag all WCAG AAA failures (below 7:1 for body text)
4. Output corrected CSS variable block or design token corrections
5. Append DTP swatch notes if print context detected

### 1.2 When triggered for new palette generation:
1. Start from SAFE PALETTE ANCHORS (Section 4)
2. Apply FORBIDDEN PAIRS check (Section 5)
3. Verify all pairs against CONTRAST MATRIX (Section 6)
4. Output complete CSS custom properties block + DTP equivalents

### 1.3 When triggered on dark mode / dark palette request (no CVD mention):
Apply all explosion-proof rules silently. Deliver palette that passes CVD
requirements without announcing it unless relevant. Rationale: dark palettes
are the primary context where CVD failures cluster.

---

## 2. CVD QUICK REFERENCE

### 2.1 Types relevant to worst-case scenario

| Type | Cone affected | What collapses |
|------|--------------|----------------|
| Protanopia | L (red) cones absent | Red = black/dark. Red/green indistinguishable |
| Deuteranopia | M (green) cones absent | Green = red/brown. Red/green indistinguishable |
| Tritanopia | S (blue) cones absent | Blue = green. Yellow = pink/gray. Blue/yellow indistinguishable |
| Protanomaly | L cones defective | Mild: red appears faded/shifted toward green |
| Deuteranomaly | M cones defective | Mild: green appears shifted toward red |
| Tritanomaly | S cones defective | Mild: blue/yellow confusion, less severe than tritanopia |
| Achromatopsia | All cones non-functional | No hue perception at all -- luminance ONLY |

**Worst-case target: user with BOTH protan/deutan AND tritan impairment.**
This is rare but documented. Design for it = design for all.

### 2.2 What gets confused per type (hue collapse table)

| Color pair | Protanopia/Deuteranopia | Tritanopia |
|-----------|------------------------|-----------|
| Red / Green | COLLAPSE | Safe |
| Blue / Purple | Mostly safe | COLLAPSE |
| Blue / Green | Mostly safe | COLLAPSE |
| Yellow / Pink | Mostly safe | COLLAPSE |
| Yellow / Orange | Caution | Safe |
| Dark red / Black | COLLAPSE | Safe |
| Brown / Olive | COLLAPSE | Safe |

**Explosion-proof rule: avoid ALL pairs from BOTH columns above as sole differentiators.**

---

## 3. AUDIT MODE -- STEP-BY-STEP PROTOCOL

### Step 1: Extract all color pairs
Identify every (foreground, background) pair that conveys meaning:
- Text on surface
- Icon/glyph on surface
- State indicators (status dots, badges, pills)
- Interactive element borders
- Focus rings

### Step 2: Calculate WCAG 2.x contrast ratio

```
Formula:
  L = relative luminance (0.0 to 1.0)
  For sRGB channel C:
    if C/255 <= 0.04045: c_lin = C/255 / 12.92
    else:                c_lin = ((C/255 + 0.055) / 1.055) ^ 2.4
  L = 0.2126*R_lin + 0.7152*G_lin + 0.0722*B_lin

  ratio = (L_lighter + 0.05) / (L_darker + 0.05)
```

**Pass thresholds:**
| Content type | WCAG AA (min) | WCAG AAA (target) |
|-------------|:---:|:---:|
| Normal text (<18pt / <14pt bold) | 4.5:1 | **7:1** |
| Large text (>=18pt / >=14pt bold) | 3:1 | 4.5:1 |
| Non-text UI elements | 3:1 | 3:1 |
| Decorative only | exempt | exempt |

**Hard target for this skill: WCAG AAA = 7:1 for all readable text.**
WCAG AA math has known false positives on dark backgrounds. For CVD users
who cannot rely on hue, luminance separation is the ONLY signal.

### Step 3: Check APCA (supplementary)

APCA Lightness Contrast (Lc) targets:
```
Lc >= 75: body text (preferred)
Lc >= 60: body text (minimum acceptable)
Lc >= 45: large headlines only
Lc >= 30: absolute minimum (non-critical UI only)
```
Note: APCA is not yet in WCAG 3.0 final -- use WCAG 2.x for compliance,
APCA for perceptual quality check on dark backgrounds.

### Step 4: Check for CVD hue traps
Even if contrast passes, flag these:
- Red/green as sole state differentiators (add icon/shape)
- Blue/yellow as sole state differentiators (add icon/shape)
- Status indicators with only hue change (no luminance delta)
- Link underlines disabled (color-only links)

### Step 5: Output corrected CSS block
See Section 7 for output template.

---

## 4. SAFE PALETTE ANCHORS -- DARK MODE

**Philosophy:** on dark backgrounds (#1A1A1A to #2D2D2D range),
the text luminance must be dramatically higher than the surface.
Mid-grays (#555-#888) are TRAPS -- they pass on paper but fail perceptually
for CVD users who cannot use hue as a cue.

### 4.1 Background surfaces (safe dark slate family)

```css
/* Deep surfaces */
--bg-base:    #1E1E1E;   /* L=0.0159 -- primary surface */
--bg-raised:  #252525;   /* L=0.0193 -- elevated surface */
--bg-deep:    #121212;   /* L=0.0069 -- deepest / header strips */
--bg-input:   #1A1A1A;   /* L=0.0105 -- input fields */
--bg-overlay: #2A2A2A;   /* L=0.0228 -- overlays, tooltips */
```

### 4.2 Text (verified 7:1+ against above surfaces)

```css
/* Primary text -- 18:1+ on all dark surfaces */
--text-primary:   #E8E8E8;   /* L=0.8148 */

/* Secondary text -- 10:1+ on deep, 7:1+ on raised */
--text-secondary: #BBBBBB;   /* L=0.4898 */

/* Muted/label text -- 7:1+ on all dark surfaces (AAA floor) */
--text-muted:     #9A9A9A;   /* L=0.3312 -- ~7.2:1 on #1E1E1E */

/* Dim/decorative -- NEVER use for state information */
--text-dim:       #787878;   /* L=0.2003 -- ~4.7:1 on deep only */
```

**CRITICAL WARNING -- THE MID-GRAY TRAP:**
Colors #555555-#888888 on backgrounds #1A1A1A-#2D2D2D produce
contrast ratios of 1.5:1 to 4.2:1. These FAIL for CVD users.
Always calculate before using any gray text.

### 4.3 State/accent colors -- explosion-proof

All state colors must satisfy TWO requirements simultaneously:
1. Luminance contrast >= 7:1 against the surface they appear on
2. Each state MUST be distinguishable in grayscale (luminance-unique)

```css
/* SAFE STATE PALETTE */
/* Each color maps to a UNIQUE luminance level -- grayscale-safe */

--state-idle:     #A8A8A8;   /* L=0.41 -- neutral gray */
--state-active:   #78C8E8;   /* L=0.38 -- sky blue */
--state-warn:     #D4A847;   /* L=0.56 -- amber (NOT pure yellow -- tritan safe) */
--state-critical: #B090C8;   /* L=0.35 -- lavender (NOT red -- protan safe) */
--state-ok:       #5ABCB8;   /* L=0.44 -- teal-cyan */
--state-disabled: #787878;   /* decorative-only -- always pair with icon/label */
```

### 4.4 Button fills -- dark mode

```css
/* All button fills: dark text (#1A1A1A) to guarantee contrast */
--btn-primary:   #5ABCB8;
--btn-secondary: #78C8E8;
--btn-warn:      #D4A847;
--btn-danger:    #B090C8;
--btn-text:      #121212;   /* forced dark text on all fills above */
```

---

## 5. FORBIDDEN PAIRS -- NEVER USE AS SOLE DIFFERENTIATORS

These pairs collapse across CVD types. Allowed ONLY when a redundant secondary
indicator (icon, shape, pattern, text label) is always present.

```
Red    vs Green    -- protan/deutan collapse
Red    vs Brown    -- protan collapse
Green  vs Brown    -- deutan collapse
Blue   vs Green    -- tritan collapse
Blue   vs Purple   -- tritan collapse
Yellow vs Pink     -- tritan collapse
Yellow vs White    -- tritan + luminance proximity
Orange vs Red      -- protan proximity
Dark Red vs Black  -- protan/deutan luminance collapse
```

**Double-forbidden (both axes impaired):**
With BOTH CVD axes affected, ONLY luminance separation is reliable.
All state indicators MUST be luminance-unique.

---

## 6. CONTRAST QUICK-REFERENCE MATRIX

| Text color | On #121212 | On #1A1A1A | On #2D2D2D | Pass AAA? |
|-----------|:---:|:---:|:---:|:---:|
| #FFFFFF   | 21:1 | 19.5:1 | 15.4:1 | YES |
| #E8E8E8   | 17.2:1 | 16.0:1 | 12.7:1 | YES |
| #CCCCCC   | 11.5:1 | 10.7:1 | 8.5:1 | YES |
| #BBBBBB   | 9.0:1 | 8.4:1 | 6.7:1 | YES (most contexts) |
| #AAAAAA   | 7.2:1 | 6.7:1 | 5.3:1 | AAA on deep only |
| #999999   | 5.8:1 | 5.4:1 | 4.3:1 | AA only |
| #888888   | 4.7:1 | 4.3:1 | 3.4:1 | FAIL for body text |
| #777777   | 3.7:1 | 3.4:1 | 2.7:1 | FAIL |
| #666666   | 2.9:1 | 2.7:1 | 2.1:1 | FAIL |
| #555555   | 2.2:1 | 2.1:1 | 1.6:1 | FAIL |

**Rule: on dark surfaces, use #AAAAAA or lighter for ANY readable text.**
**NEVER use #666666-#888888 for text that conveys state information.**

---

## 7. CSS OUTPUT TEMPLATE

```css
/* ==========================================================================
   CVD-SAFE COLOR PALETTE -- dischromatopsy-color-skill v1.0.0
   Standard: WCAG AAA (7:1) hard minimum | APCA Lc>=75 preferred
   CVD target: protan + deutan + tritan simultaneously (worst-case)
   Locked: [DATE] | Version: [PALETTE_VERSION]
   CONTRAST IS A HARD REQUIREMENT -- NOT OPTIONAL.
   ========================================================================== */

:root {
    /* BACKGROUNDS */
    --bg-base:          #1E1E1E;   /* L=0.0159 */
    --bg-raised:        #252525;   /* L=0.0193 */
    --bg-deep:          #121212;   /* L=0.0069 */

    /* TEXT -- ALL verified 7:1+ on bg-base */
    --text-primary:     #E8E8E8;   /* 16.0:1 on bg-base */
    --text-secondary:   #BBBBBB;   /*  8.4:1 on bg-base */
    --text-muted:       #9A9A9A;   /*  7.2:1 on bg-base -- AAA floor */
    /* NOTE: text-dim below 7:1 -- decorative/non-state only */
    --text-dim:         #787878;   /*  4.7:1 on bg-deep ONLY */

    /* STATE INDICATORS -- luminance-unique (grayscale-safe) */
    --state-idle:       #A8A8A8;   /* L~0.41 */
    --state-active:     #78C8E8;   /* L~0.38 */
    --state-warn:       #D4A847;   /* L~0.56 */
    --state-critical:   #B090C8;   /* L~0.35 */
    --state-ok:         #5ABCB8;   /* L~0.44 */
    --state-disabled:   #787878;   /* decorative only -- pair with icon */

    /* BUTTONS */
    --btn-primary:      #5ABCB8;
    --btn-secondary:    #78C8E8;
    --btn-warn:         #D4A847;
    --btn-danger:       #B090C8;
    --btn-text:         #121212;   /* universal dark text for pastel fills */
}
```

---

## 8. DTP / PRINT GUIDANCE

For desktop publishing, print, and typography:
- Read `references/dtp-print-guidance.md` for full guidance.
- Print contrast requires ~20% luminance margin over screen values.
- Test all print layouts in grayscale before release.
- Replace process red with amber (C=0% M=50% Y=100% K=0%) for danger states.

---

## 9. REDUNDANCY PRINCIPLE

**Color alone is never sufficient for state information.**
Pair color with at minimum ONE of:
- Icon / glyph (preferred)
- Shape change
- Text label
- Pattern / texture (print only)
- Border weight change
- Animation (active states)

Absolute for: error/warning/success states, required field markers,
enabled/disabled controls, progress states.

---

## 10. REFERENCE FILES IN THIS SKILL

| File | When to read |
|------|-------------|
| `references/cvd-taxonomy.md` | CVD science, cone biology, prevalence, Ishihara limits |
| `references/contrast-math.md` | Manual contrast calculation, luminance table, APCA |
| `references/safe-palette-library.md` | Full verified palette library -- 5 dark themes + data viz |
| `references/dtp-print-guidance.md` | Print/DTP context confirmed |
| `references/audit-protocol.md` | Full audit checklist for existing design systems |
| `references/bad-examples.md` | Anonymized cautionary case study -- what NOT to do |
| `references/tool-references.md` | Simulation tools, checkers, validators (all types) |

---

## 11. QUICK RESPONSE DECISION TREE

```
User mentions CVD/Ishihara/color blind?
  YES --> Load skill, run AUDIT if design in context
      CSS in context? --> Section 3 audit + Section 7 CSS template
      No design?      --> Section 4+5 palettes

User requests dark palette (no CVD mention)?
  --> Apply explosion-proof rules silently
  --> Deliver Section 4 palette
  --> Never use #666-#888 for text

User asks for state colors / status indicators?
  --> Section 4.3 luminance-unique state palette
  --> Section 9 redundancy principle
  --> Never red/green as sole state differentiators

User asks about print/DTP?
  --> Read references/dtp-print-guidance.md
  --> Section 8 print-specific rules
```
