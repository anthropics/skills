# Typography Reference

## Table of Contents
1. Font Selection
2. Type Scale
3. Font Pairing
4. Line Height and Spacing
5. OpenType Features
6. Pixel and Display Fonts
7. Web Font Loading
8. Common Mistakes

---

## 1. Font Selection

### Banned Defaults
Never use these as primary typefaces: Inter, Roboto, Arial, Helvetica, system-ui, sans-serif (as the only declaration), Space Grotesk (overused in AI contexts), or any font that ships as a browser default.

### Where to Find Good Fonts
- Google Fonts: vast but requires curation. Sort by trending, not popular.
- Bunny Fonts: privacy-friendly Google Fonts mirror.
- Fontshare: free, high-quality fonts from Indian Type Foundry.
- Atipo Foundry: distinctive display and text faces.
- CDN: `https://fonts.cdnfonts.com` for broader selection.

### Selection Criteria
A good typeface for a project should:
- Match the emotional register of the content (a legal dashboard should not use a playful rounded sans)
- Have sufficient weight range (at minimum: regular, medium, bold)
- Include tabular figures if displaying data
- Support the required character sets
- Feel distinct from the last 5 things you built

### The Geist System
Vercel's Geist family offers three complementary typefaces:
- **Geist Sans**: clean, geometric sans for UI text
- **Geist Mono**: monospaced for code and data
- **Geist Pixel**: bitmap-inspired display font with 5 variants (Square, Grid, Circle, Triangle, Line), useful for banners, experimental layouts, and product moments where typography becomes part of the interface language

Install via `npm i geist`. Each variant has its own CSS variable (e.g., `--font-geist-pixel-square`).

---

## 2. Type Scale

Use a modular scale. Pick a ratio and apply it consistently.

| Ratio | Name | Use Case |
|---|---|---|
| 1.125 | Major Second | Dense data UIs, admin panels |
| 1.200 | Minor Third | General purpose, balanced |
| 1.250 | Major Third | Most common, works broadly |
| 1.333 | Perfect Fourth | Editorial, generous spacing |
| 1.500 | Perfect Fifth | Display-heavy, marketing |
| 1.618 | Golden Ratio | High-impact landing pages |

### Calculating Sizes
Base size: 16px (1rem). Multiply up for headings, divide down for captions.

```
Caption:  0.75rem (12px)
Small:    0.875rem (14px)
Body:     1rem (16px)
Large:    1.125rem (18px)
H4:       1.25rem (20px)
H3:       1.563rem (25px)
H2:       1.953rem (31px)
H1:       2.441rem (39px)
Display:  3.052rem (49px)
```

For fluid type, use `clamp()`:
```css
h1 { font-size: clamp(2rem, 5vw + 1rem, 3.5rem); }
```

---

## 3. Font Pairing

### Principles
- Pair fonts with contrasting structures: a serif display with a sans body, or a geometric sans heading with a humanist sans body.
- Never pair fonts that are too similar (two geometric sans faces will fight).
- One display font is enough. Two is almost always too many.
- The body font does the heavy lifting. It must be supremely readable at 16px.

### Proven Pairs
- **Display serif + sans body**: Playfair Display / Source Sans 3
- **Geometric sans + humanist sans**: Outfit / Nunito Sans
- **Slab + grotesque**: Zilla Slab / Work Sans
- **Monospace accent + sans body**: JetBrains Mono / DM Sans
- **Variable display + clean body**: Instrument Serif / Instrument Sans

---

## 4. Line Height and Spacing

| Context | Line Height | Letter Spacing |
|---|---|---|
| Body text | 1.5 to 1.6 | 0 to 0.01em |
| Headings (large) | 1.1 to 1.2 | -0.02 to -0.01em |
| Headings (small) | 1.2 to 1.3 | 0 |
| Captions | 1.4 | 0.02 to 0.05em |
| All caps text | 1.2 | 0.08 to 0.15em |
| Monospace/code | 1.5 to 1.7 | 0 |

### Paragraph Spacing
Use margin-bottom on paragraphs, not margin-top. Space between paragraphs should equal roughly the line-height value (1.5em works well). Never use `<br>` for spacing.

---

## 5. OpenType Features

When the font supports them, enable:
```css
.body-text {
  font-feature-settings: "liga" 1, "kern" 1;
  font-variant-ligatures: common-ligatures;
}
.data-table {
  font-variant-numeric: tabular-nums;
}
.legal-text {
  font-variant-numeric: oldstyle-nums;
}
.heading {
  font-feature-settings: "ss01" 1; /* Stylistic set */
}
```

---

## 6. Pixel and Display Fonts

Pixel fonts are useful for specific moments: retro interfaces, game UIs, terminal aesthetics, or when the digital nature of the medium should be emphasized. They are not novelty fonts when used with system thinking.

Key principles for pixel fonts:
- Only use at sizes that align with the pixel grid (multiples of the font's design size)
- Disable anti-aliasing for crisp rendering: `font-smooth: never; -webkit-font-smoothing: none;`
- Pair with a clean sans for body text
- Use for headings, labels, badges, or UI accents, not paragraphs

---

## 7. Web Font Loading

Use `font-display: swap` to prevent invisible text during load. Preload critical fonts:

```html
<link rel="preload" href="/fonts/display.woff2" as="font" type="font/woff2" crossorigin>
```

Subset fonts to the characters actually used. For Google Fonts, append `&text=` with the specific characters or use `&subset=latin`.

Self-host when possible. CDN fonts introduce a third-party dependency and a DNS lookup.

---

## 8. Common Mistakes

- Using more than 3 font families on a page
- Setting body text below 16px on desktop or 14px on mobile
- Applying letter-spacing to body text (it reduces readability)
- Using light (300) font weight for body text on low-contrast backgrounds
- Centering long paragraphs (center alignment works for 1-2 lines maximum)
- Forgetting to set `max-width` on text blocks (ideal: 60-75 characters per line, roughly 600-750px)
- Using all caps for more than a few words without increasing letter-spacing
