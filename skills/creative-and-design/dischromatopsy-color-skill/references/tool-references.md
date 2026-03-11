# Tool References — CVD Testing, Simulation, and Contrast Validation
<!-- dischromatopsy-color-skill v1.0.0 | references/tool-references.md -->

## 1. Contrast Ratio Checkers

| Tool | URL | Notes |
|------|-----|-------|
| WebAIM Contrast Checker | https://webaim.org/resources/contrastchecker/ | WCAG 2.x AA/AAA, hex input |
| Coolors Contrast Checker | https://coolors.co/contrast-checker | Visual + ratio + pass/fail |
| APCA Calculator (Myndex) | https://www.myndex.com/APCA/ | APCA Lc score — supplementary |
| Atmos Contrast Checker | https://atmos.style/contrast-checker | Both WCAG 2.x AND APCA results |
| Color.review | https://color.review | Large visual preview, hex input |
| Colour Contrast Analyser | https://www.tpgi.com/color-contrast-analyser/ | Desktop app (Win/Mac), screen picker |

---

## 2. CVD Simulation Tools

### Online / Browser

| Tool | URL | CVD types supported | Algorithm |
|------|-----|:---:|---|
| Coblis v2 | https://www.color-blindness.com/coblis-color-blindness-simulator/ | All types | HCIRN (Wickline) |
| DaltonLens Online | https://daltonlens.org/colorblindness-simulator | Protan, deutan, tritan + severity | Brettel 1997 / Machado 2009 / Viénot 1999 |
| RGBlind | https://rgblind.com/color-blindness-simulator | All types | Multiple |
| Color Blind Website Checker | https://www.toptal.com/designers/colorfilter | Full page URL simulation | Brettel |
| Palette Accessibility Checker | https://www.coblind.com/color-palette-for-color-blind | Palette pairs + ΔE2000 | Multiple |

**Algorithm recommendation:**
- For **tritanopia** simulation: use **Brettel 1997** — most accurate for tritan
- For **protan/deutan** simulation: Viénot 1999 or Machado 2009 — both solid
- Avoid Coblis v1 (ColorMatrix algorithm — known to be inaccurate)
- Chromium DevTools uses Machado 2009 — reliable for protan/deutan

### Desktop Apps

| Tool | Platform | Notes |
|------|----------|-------|
| Color Oracle | Win / Mac / Linux | Free, simulates entire screen |
| Sim Daltonism | Mac / iOS | Free, floating window overlay |
| DaltonLens Desktop | Win / Mac / Linux | Free, real-time simulation |

### Browser DevTools (Built-in)

**Chrome / Edge DevTools:**
1. F12 → More tools → Rendering
2. "Emulate vision deficiencies" dropdown
3. Supports: Blurred vision, Protanopia, Deuteranopia, Tritanopia, Achromatopsia
4. Algorithm: Machado 2009 (reliable)

**Firefox DevTools:**
1. F12 → Accessibility tab
2. "Simulate" dropdown
3. Supports same types as Chrome

---

## 3. Palette Analysis Tools

| Tool | URL | Notes |
|------|-----|-------|
| Viz Palette | https://www.vizpalette.com | Data viz palette builder with CVD simulation |
| Chroma.js Palette Helper | https://gka.github.io/palettes/ | Perceptually uniform palette generation |
| colorblindcheck (R) | https://jakubnowosad.com/colorblindcheck | R package for palette distance analysis + ΔE |
| Palette Buddy | https://www.palettebuddy.io | Visual palette builder with contrast check |
| accessible-palette | https://accessible-palette.com | Generates full accessible color systems |

---

## 4. Design Tool Plugins

### Figma
- **A11y - Color Contrast Checker** — checks all text layers
- **Color Blind** — simulates CVD on frames/components
- **Stark** — comprehensive accessibility suite (paid, has free tier)
- **Contrast** — by Stark (free standalone contrast checker)

### Adobe Illustrator (built-in)
- View > Proof Setup > Color Blindness – Protanopia-type
- View > Proof Setup > Color Blindness – Deuteranopia-type
- Note: NO tritanopia simulation built-in

### Adobe Photoshop (built-in)
- View > Proof Colors > same as Illustrator
- Same limitation: protan/deutan only

### Sketch
- Plugins: **Stark** or **A11y** for CVD simulation

---

## 5. Standards and Specification References

| Document | URL | Notes |
|----------|-----|-------|
| WCAG 2.2 | https://www.w3.org/TR/WCAG22/ | Current legal standard |
| SC 1.4.3 Contrast (Minimum) | https://www.w3.org/WAI/WCAG22/Understanding/contrast-minimum | AA: 4.5:1 normal, 3:1 large |
| SC 1.4.6 Contrast (Enhanced) | https://www.w3.org/WAI/WCAG22/Understanding/contrast-enhanced | AAA: 7:1 normal, 4.5:1 large |
| SC 1.4.11 Non-text Contrast | https://www.w3.org/WAI/WCAG22/Understanding/non-text-contrast | AA: 3:1 for UI components |
| SC 1.4.1 Use of Color | https://www.w3.org/WAI/WCAG22/Understanding/use-of-color | Color not sole differentiator |
| APCA (Myndex / SAPC) | https://github.com/Myndex/SAPC-APCA | Beta — not in WCAG 3.0 final yet |
| WCAG 3.0 Working Draft | https://www.w3.org/TR/wcag-3.0/ | In development — ~2030 est. |

---

## 6. Scientific / Academic References

| Reference | URL | Notes |
|-----------|-----|-------|
| Brettel et al. 1997 (tritanopia simulation) | JOSA A, Vol 14 | Foundation algorithm for tritan sim |
| Machado et al. 2009 | IEEE TVCG | Best protan/deutan simulation |
| Okabe & Ito 2008 (CUD palette) | JCVIS | Origin of the universal CVD-safe palette |
| Wong 2011 (Nature Methods palette) | Nature Methods 8(6):441 | Okabe-Ito adoption by Nature |
| DaltonLens algorithm review | https://daltonlens.org/opensource-cvd-simulation/ | Best comparison of simulation algorithms |
| Martin Krzywinski palettes | https://mk.bcgsc.ca/colorblind/palettes.mhtml | 15-color palettes per CVD type |

---

## 7. CVD Testing / Screening Tests (for user reference)

| Test | What it detects | Notes |
|------|----------------|-------|
| Ishihara (38 plates) | Protan + deutan | Does NOT detect tritanopia |
| Hardy-Rand-Rittler (HRR) | All types including tritan | Better than Ishihara for comprehensive screening |
| Farnsworth-Munsell 100 Hue | All types + severity | Clinical gold standard for grading |
| Cambridge Color Test | All types | Research/clinical use |
| Anomaloscope | Protan/deutan grading | True gold standard for R-G axis |
| Farnsworth D-15 | All types, moderate/severe | Dichotomous — fast clinical screening |

**Key implication for designers:** a user reporting Ishihara failure has protan or
deutan CVD. They may ALSO have tritan issues (acquired or congenital) that the
Ishihara test would not detect. Design for both axes regardless.
