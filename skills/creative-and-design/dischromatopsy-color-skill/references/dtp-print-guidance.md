# DTP / Print Guidance — Color Vision Deficiency-Safe Design for Print
<!-- dischromatopsy-color-skill v1.0.0 | references/dtp-print-guidance.md -->

## 1. Key Differences: Screen vs. Print

| Property | Screen (sRGB) | Print (CMYK) |
|----------|:---:|:---:|
| Color model | Additive (light) | Subtractive (ink) |
| Black | 0% luminance (#000000) | 100% Key (K) ink |
| White | 100% luminance (#FFFFFF) | 0% ink (paper) |
| Gamut | sRGB ≤ P3 ≤ Rec.2020 | Smaller than sRGB (most CMYK) |
| Luminance range | High (emissive) | Low (reflective) |
| CVD risk | Luminance math applies | Same math + ink shift risk |

**Critical for CVD design in print:**
Reflective media (paper) has a lower luminance range than emissive screens.
What appears as sufficient contrast on screen may appear marginal in print.
**Add +20% luminance margin when converting screen CVD-safe palettes to print.**

---

## 2. Color Space and ICC Profiles

### Recommended ICC profiles by use case:

| Use case | ICC profile | Notes |
|----------|-------------|-------|
| EU coated offset | Fogra39 / Fogra51 | Standard European print |
| US coated offset | SWOP v2 / GRACoL 2013 | Standard US print |
| Uncoated paper | Fogra47 / SWOP Uncoated | Matte/uncoated stock |
| Wide format / inkjet | Profile varies by machine | Use machine-specific profile |
| Digital print | Usually sRGB or manufacturer CMYK | Check with print vendor |

### Conversion workflow:
1. Design in sRGB (web) or Adobe RGB (print)
2. Use Relative Colorimetric or Perceptual rendering intent
3. Convert to destination CMYK profile at FINAL output stage
4. Soft-proof before sending to print
5. Run grayscale proof — if legible in grayscale, CVD is covered

---

## 3. Print-Specific CVD Color Traps

### Trap 1: Yellow ink on white paper (tritan risk)
Pure yellow (#FFFF00) in print appears as very pale, nearly white to tritan viewers.
The yellow ink reflects a wide spectrum — including the blue-leaning white point of paper.

**Fix:**
```
Screen yellow: #F0E442 (Okabe-Ito) — fine for screen
Print warning amber: C=0%, M=25%, Y=90%, K=5%  (darker amber)
Hex equivalent: ~#D4960A — darker, more distinguishable
```

### Trap 2: Cyan ink confusion (tritan risk)
Cyan process ink can appear blue-gray to tritan viewers.
If blue and cyan are used as distinct states in print, they may collapse.

**Fix:** Use cyan + teal WITH a luminance delta of at least 20% between them,
OR add a text label/icon to distinguish them.

### Trap 3: Red ink appearance (protan risk)
Process red (C=0%, M=100%, Y=100%, K=0%) appears as very dark brown or near-black
to protanopes. Never use red alone for danger/error indicators in print.

**Fix:**
```
Replace red with orange-amber: C=0%, M=50%, Y=100%, K=0% — hex ~#E88020
This is distinguishable for all CVD types by luminance + hue.
```

### Trap 4: Thin fonts on dark tinted backgrounds (print legibility)
Screen dark themes often use 9–10px text on dark surfaces.
In print, equivalent point sizes (8–9pt) on dark tinted paper are near-illegible.

**Fix:**
- Minimum body text on dark in print: 10pt, weight >= Regular (400)
- Minimum caption text: 8pt, weight Bold (700)
- Minimum fine print: 7pt — DO NOT use dark backgrounds at this size

---

## 4. Typography — Print Contrast Guidance

### Point size / contrast relationship

Print contrast is affected by ink spread (dot gain) and paper texture.
A 7:1 WCAG ratio on screen does NOT guarantee 7:1 perceived in print.

**Practical minimums for CVD-safe print:**

| Context | Minimum size | Minimum weight | Min contrast (screen equiv.) |
|---------|:---:|:---:|:---:|
| Body text | 10pt | Regular 400 | 7:1 |
| Captions, footnotes | 8pt | Regular 400 or Bold | 9:1 |
| Headlines | 18pt | Any | 4.5:1 |
| Labels on colored backgrounds | 9pt | Bold 700 | 7:1 |
| Reversed text (white on dark) | 10pt | Regular 400 | 7:1 |

### Font selection for CVD print

- Prefer humanist sans-serif: Inter, Frutiger, Myriad, Trebuchet
- Avoid ultra-thin weights (100–200) on any colored background
- Avoid decorative/script fonts for any state information
- x-height matters: fonts with high x-height (>0.50 ratio) are more legible
  at small sizes → better for CVD users who rely on letterform recognition

---

## 5. Grayscale Proof — The CVD Print Test

**Rule: If it works in grayscale, it works for all CVD types.**

Grayscale proof workflow:
1. Adobe Acrobat: Print Production > Output Preview > Simulate > Grayscale
2. Adobe Illustrator: View > Proof Colors > Grayscale
3. Photoshop: Image > Mode > Grayscale (on a copy only)
4. InDesign: export PDF, open in Acrobat, use Output Preview

Check in grayscale:
- [ ] Can all body text be read?
- [ ] Is the visual hierarchy preserved? (headers > body > captions)
- [ ] Are all state indicators distinguishable from each other?
- [ ] Do chart series/data categories remain distinguishable?
- [ ] Are buttons distinguishable from non-interactive text?

---

## 6. Safe CMYK State Colors — Print Reference

```
IDLE / NEUTRAL:
  CMYK: C=0% M=0% Y=0% K=35%  → Gray ~#A8A8A8

ACTIVE / RUNNING:
  CMYK: C=55% M=10% Y=5% K=0%  → Sky blue ~#70B8D8

WARNING / CAUTION:
  CMYK: C=0% M=30% Y=80% K=5%  → Amber ~#D4980A

CRITICAL / DANGER:
  CMYK: C=20% M=30% Y=0% K=0%  → Lavender ~#B898C8
  (NOT process red — protan trap)

SUCCESS / OK:
  CMYK: C=55% M=0% Y=30% K=10% → Teal ~#58B0A0

DISABLED:
  CMYK: C=0% M=0% Y=0% K=50%  → Mid gray — pair with text label
```

---

## 7. Accessibility Labels in Print (DTP Redundancy)

WCAG is a web standard. Print has no formal equivalent standard.
However, the principles carry over directly.

**Non-optional in print for CVD users:**
- Every color-coded element must have a text label or icon partner
- Maps, charts, and diagrams must have a legend that works in grayscale
- Warning boxes must use an icon (!) in addition to color tint
- Danger/critical sections must use text label "WARNING" / "CRITICAL" not just red

**Pattern to avoid:**
```
[RED BOX] — only color differentiates danger from info
```

**Pattern to use:**
```
[AMBER BOX + ! ICON + "WARNING" TEXT LABEL]
```
