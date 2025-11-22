# Yopitek Color Palette Reference

## Primary Colors

### Tech Blue (Primary Brand Color)
```
HEX:  #0066CC
RGB:  rgb(0, 102, 204)
CMYK: c100 m50 y0 k20
HSL:  hsl(210, 100%, 40%)
```
**Usage:** Primary brand elements, headers, CTAs, links
**Accessibility:** AA compliant on white backgrounds

---

### Deep Navy (Professional)
```
HEX:  #1A2332
RGB:  rgb(26, 35, 50)
CMYK: c100 m75 y50 k70
HSL:  hsl(218, 32%, 15%)
```
**Usage:** Text, backgrounds, professional contexts
**Accessibility:** AAA compliant with white text

---

### Pure White
```
HEX:  #FFFFFF
RGB:  rgb(255, 255, 255)
CMYK: c0 m0 y0 k0
HSL:  hsl(0, 0%, 100%)
```
**Usage:** Backgrounds, negative space, light themes

---

## Secondary Colors

### Electric Cyan (Innovation)
```
HEX:  #00D4FF
RGB:  rgb(0, 212, 255)
CMYK: c70 m0 y0 k0
HSL:  hsl(190, 100%, 50%)
```
**Usage:** Accents, highlights, digital interfaces, wireless router branding

---

### Signal Green (Connectivity)
```
HEX:  #00E676
RGB:  rgb(0, 230, 118)
CMYK: c70 m0 y70 k0
HSL:  hsl(151, 100%, 45%)
```
**Usage:** Active states, success indicators, NFC reader branding

---

### Circuit Orange (Performance)
```
HEX:  #FF6B35
RGB:  rgb(255, 107, 53)
CMYK: c0 m70 y80 k0
HSL:  hsl(16, 100%, 60%)
```
**Usage:** Highlights, performance indicators, graphic card branding

---

## Neutral Colors

### Cool Gray 90
```
HEX:  #2D3142
RGB:  rgb(45, 49, 66)
HSL:  hsl(229, 19%, 22%)
```
**Usage:** Secondary text, dark UI elements

---

### Cool Gray 50
```
HEX:  #9DA3B4
RGB:  rgb(157, 163, 180)
HSL:  hsl(224, 14%, 66%)
```
**Usage:** Disabled states, borders, subtle elements

---

### Cool Gray 10
```
HEX:  #F5F6F8
RGB:  rgb(245, 246, 248)
HSL:  hsl(220, 20%, 97%)
```
**Usage:** Subtle backgrounds, alternate sections

---

## Product Line Color Associations

### Wireless Routers
**Primary:** Tech Blue (#0066CC)
**Accent:** Electric Cyan (#00D4FF)
**Theme:** Connectivity and waves

### Graphic Cards
**Primary:** Circuit Orange (#FF6B35)
**Accent:** Electric Cyan (#00D4FF)
**Theme:** Performance and power

### NFC Card Readers
**Primary:** Signal Green (#00E676)
**Accent:** Tech Blue (#0066CC)
**Theme:** Security and touch

---

## Color Combinations

### Primary Combination
- Background: Pure White (#FFFFFF)
- Primary: Tech Blue (#0066CC)
- Text: Deep Navy (#1A2332)
- Accents: Electric Cyan (#00D4FF)

### Dark Mode Combination
- Background: Deep Navy (#1A2332)
- Primary: Electric Cyan (#00D4FF)
- Text: Pure White (#FFFFFF)
- Accents: Tech Blue (#0066CC)

### High Energy Combination
- Background: Pure White (#FFFFFF)
- Primary: Circuit Orange (#FF6B35)
- Secondary: Tech Blue (#0066CC)
- Accent: Electric Cyan (#00D4FF)

---

## Accessibility Guidelines

### Text Contrast Ratios (WCAG 2.1)

**AAA Compliant (7:1)**
- Deep Navy (#1A2332) on White (#FFFFFF) = 13.5:1 ✓
- White (#FFFFFF) on Deep Navy (#1A2332) = 13.5:1 ✓

**AA Compliant (4.5:1)**
- Tech Blue (#0066CC) on White (#FFFFFF) = 5.9:1 ✓
- Cool Gray 90 (#2D3142) on White (#FFFFFF) = 10.5:1 ✓

**Use with Caution (Large Text Only)**
- Electric Cyan (#00D4FF) on White (#FFFFFF) = 2.9:1
- Signal Green (#00E676) on White (#FFFFFF) = 1.8:1
- Circuit Orange (#FF6B35) on White (#FFFFFF) = 3.1:1

*Note: Accent colors should be used for decorative elements or large text (18pt+) only*

---

## CSS Color Variables

```css
:root {
  /* Primary Colors */
  --yopitek-tech-blue: #0066CC;
  --yopitek-deep-navy: #1A2332;
  --yopitek-white: #FFFFFF;

  /* Secondary Colors */
  --yopitek-electric-cyan: #00D4FF;
  --yopitek-signal-green: #00E676;
  --yopitek-circuit-orange: #FF6B35;

  /* Neutral Colors */
  --yopitek-gray-90: #2D3142;
  --yopitek-gray-50: #9DA3B4;
  --yopitek-gray-10: #F5F6F8;
}
```

---

## Color Psychology

**Tech Blue** - Trust, professionalism, technology, stability
**Electric Cyan** - Innovation, digital, modern, fresh
**Signal Green** - Success, connectivity, go-ahead, safety
**Circuit Orange** - Energy, enthusiasm, performance, warmth
**Deep Navy** - Authority, reliability, corporate, premium

---

## Print Color Notes

### Pantone Equivalents (Approximate)

- Tech Blue: Pantone 300 C
- Deep Navy: Pantone 533 C
- Electric Cyan: Pantone 311 C
- Signal Green: Pantone 2270 C
- Circuit Orange: Pantone 1655 C

*Note: Always request printed proofs for critical brand materials*

### Special Printing Considerations

- Use CMYK values for offset printing
- RGB for digital displays
- Request color matching system (PMS) for brand-critical items
- Maintain color consistency across materials with color profiles
