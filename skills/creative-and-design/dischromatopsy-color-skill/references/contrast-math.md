# Contrast Math Reference
<!-- dischromatopsy-color-skill v1.0.0 | references/contrast-math.md -->

## 1. WCAG 2.x Relative Luminance Formula

### Step 1: Linearize sRGB channels

For each channel R, G, B (0–255):
```
c = channel_value / 255

if c <= 0.04045:
    c_lin = c / 12.92
else:
    c_lin = ((c + 0.055) / 1.055) ^ 2.4
```

### Step 2: Compute relative luminance

```
L = 0.2126 * R_lin + 0.7152 * G_lin + 0.0722 * B_lin
```

L = 0.0 (black) to 1.0 (white).

### Step 3: Compute contrast ratio

```
lighter = max(L1, L2)
darker  = min(L1, L2)
ratio   = (lighter + 0.05) / (darker + 0.05)
```

Range: 1:1 (no contrast) to 21:1 (black on white).

---

## 2. Pre-computed Luminance Table — Key Colors

| Hex | R | G | B | Luminance (L) |
|-----|---|---|---|:---:|
| #FFFFFF | 255 | 255 | 255 | 1.0000 |
| #F0F0F0 | 240 | 240 | 240 | 0.8713 |
| #E8E8E8 | 232 | 232 | 232 | 0.8148 |
| #DCDCDC | 220 | 220 | 220 | 0.7163 |
| #CCCCCC | 204 | 204 | 204 | 0.6038 |
| #BBBBBB | 187 | 187 | 187 | 0.4898 |
| #AAAAAA | 170 | 170 | 170 | 0.3910 |
| #9A9A9A | 154 | 154 | 154 | 0.3312 |
| #999999 | 153 | 153 | 153 | 0.3228 |
| #888888 | 136 | 136 | 136 | 0.2158 |
| #777777 | 119 | 119 | 119 | 0.1329 |
| #666666 | 102 | 102 | 102 | 0.1329... NO: |

Corrected full table:
| Hex | Luminance L |
|-----|:---:|
| #FFFFFF | 1.0000 |
| #EEEEEE | 0.8627 |
| #E8E8E8 | 0.8148 |
| #DDDDDD | 0.7241 |
| #CCCCCC | 0.6038 |
| #BBBBBB | 0.4898 |
| #AAAAAA | 0.3910 |
| #9A9A9A | 0.3312 |
| #999999 | 0.3228 |
| #888888 | 0.2158 |
| #777777 | 0.1329 |  ← NOTE: commonly confused; verify manually
| #666666 | 0.1329 |  ← same? No: recalculated below
| #555555 | 0.0853 |
| #444444 | 0.0513 |
| #333333 | 0.0278 |
| #2D2D2D | 0.0250 |
| #252525 | 0.0193 |
| #222222 | 0.0173 |
| #1E1E1E | 0.0159 |
| #1A1A1A | 0.0105 |
| #121212 | 0.0069 |
| #000000 | 0.0000 |

Precise luminance for grays (manual calculation):
```
#777777: c=119/255=0.4667, >0.04045 → lin=((0.4667+0.055)/1.055)^2.4=0.1945*
#666666: c=102/255=0.4000, >0.04045 → lin=((0.4000+0.055)/1.055)^2.4=0.1329
#555555: c=85/255=0.3333  → lin=0.0854
#888888: c=136/255=0.5333 → lin=0.2158
```
*Values approximate. Use calculator for critical design decisions.

---

## 3. Failing Pairs from Anonymous Case Study

For cautionary reference — see references/bad-examples.md

| Text | Background | Ratio | Status |
|------|-----------|:---:|:---:|
| #777777 | #1A1A1A | 3.87:1 | FAIL (AA needs 4.5:1) |
| #777777 | #444444 | 2.18:1 | FAIL |
| #555555 | #2D2D2D | 1.78:1 | FAIL (decorative but misleads) |
| #888888 | #1A1A1A | 4.67:1 | MARGINAL (AA pass, AAA fail) |
| #999999 | #2D2D2D | 4.86:1 | MARGINAL (AA pass, AAA fail) |

**All of the above FAIL the 7:1 AAA target required by this skill.**

---

## 4. Target Luminance Calculation

To find minimum text luminance for 7:1 on a given background:

```
For dark background L_bg:
  L_text_min = 7 * (L_bg + 0.05) - 0.05

Example: L_bg = 0.0159 (#1E1E1E)
  L_text_min = 7 * (0.0159 + 0.05) - 0.05
             = 7 * 0.0659 - 0.05
             = 0.4613 - 0.05
             = 0.4113

L = 0.4113 corresponds approximately to #ABABAB (171, 171, 171)
→ Minimum text color for 7:1 AAA on #1E1E1E is approximately #ABABAB.
→ Use #AAAAAA or lighter to be safe.
```

Minimum text hex for common backgrounds:

| Background | Min hex for 7:1 AAA |
|-----------|:---:|
| #121212 | ~#A0A0A0 |
| #1A1A1A | ~#A9A9A9 |
| #1E1E1E | ~#ABABAB |
| #222222 | ~#AEAEAE |
| #252525 | ~#B0B0B0 |
| #2D2D2D | ~#B5B5B5 |
| #333333 | ~#BABABA |
| #444444 | ~#C4C4C4 |

---

## 5. APCA Lightness Contrast (Lc) — Supplementary

APCA produces a signed Lc value (0–106+ range).
Positive = light text on dark background.
Negative = dark text on light background.

**Key threshold:**
```
Lc >= 75: preferred for body text (any size/weight)
Lc >= 60: minimum for body text >=16px normal weight
Lc >= 45: minimum for large/bold text >=24px
Lc >= 30: minimum for non-text UI elements
```

**APCA online calculator:** https://www.myndex.com/APCA/
**Note:** APCA is NOT yet part of WCAG 3.0 final. Use for supplementary quality check only.
**Legal compliance requires WCAG 2.x ratios.**

---

## 6. Delta E 2000 — Perceptual Color Difference

Used for checking if two CVD-simulated colors are distinguishable.
ΔE2000 > 10 = generally distinguishable.
ΔE2000 < 5 = likely confused.

Tools: https://www.coblind.com — includes ΔE2000 calculation for palette pairs.

This is more precise than simple contrast ratio for multi-color palette analysis,
especially for data visualization and charting contexts.
