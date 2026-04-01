# Color and Contrast Reference

## Table of Contents
1. Color Space and Manipulation
2. Palette Construction
3. Tinted Neutrals
4. Dark Mode
5. Accessibility
6. CSS Variables Pattern
7. Common Mistakes

---

## 1. Color Space and Manipulation

Use OKLCH for perceptually uniform color. Unlike HSL, OKLCH ensures that colors at the same lightness value actually appear equally bright to the human eye.

```css
/* OKLCH: lightness (0-1), chroma (0-0.4), hue (0-360) */
--accent: oklch(0.65 0.25 25);        /* vibrant red-orange */
--accent-hover: oklch(0.60 0.28 25);  /* darker, more saturated */
--accent-muted: oklch(0.75 0.08 25);  /* same hue, much less chroma */
```

For programmatic palette generation, adjust lightness for tints/shades, chroma for saturation, and hue for variation. OKLCH makes this predictable.

---

## 2. Palette Construction

### The 60-30-10 Rule
- 60% dominant (surface/background)
- 30% secondary (cards, sections, supporting elements)
- 10% accent (CTAs, active states, highlights)

### Building a Palette
1. Start with the accent color (the brand or action color)
2. Derive a surface color: very low chroma version of the accent hue
3. Build neutral scale: tinted toward the accent hue (never pure gray)
4. Add a semantic layer: success (green family), warning (amber), error (red), info (blue)
5. Generate dark mode variants by inverting the lightness scale, not the colors

### Token Structure
```css
:root {
  /* Surfaces */
  --surface-0: oklch(0.99 0.005 80);    /* page background */
  --surface-1: oklch(0.97 0.008 80);    /* card background */
  --surface-2: oklch(0.94 0.01 80);     /* elevated/hover surface */
  --surface-3: oklch(0.90 0.012 80);    /* active/selected surface */

  /* Text */
  --text-primary: oklch(0.15 0.02 80);
  --text-secondary: oklch(0.40 0.02 80);
  --text-tertiary: oklch(0.55 0.015 80);

  /* Accent */
  --accent: oklch(0.55 0.25 30);
  --accent-hover: oklch(0.50 0.28 30);
  --accent-subtle: oklch(0.92 0.04 30);

  /* Borders */
  --border: oklch(0.88 0.01 80);
  --border-strong: oklch(0.78 0.015 80);

  /* Semantic */
  --success: oklch(0.55 0.18 145);
  --warning: oklch(0.65 0.18 70);
  --error: oklch(0.55 0.22 25);
}
```

---

## 3. Tinted Neutrals

Never use pure gray (#808080, rgb(128,128,128), etc.). Always tint neutrals toward the dominant hue of the palette. This creates warmth and cohesion.

**Warm neutrals** (tinted toward amber/brown): suited for editorial, luxury, organic brands
**Cool neutrals** (tinted toward blue/slate): suited for tech, data, professional tools
**Neutral neutrals** (tinted toward the accent hue at very low chroma): the most versatile approach

```css
/* Instead of #333333 */
--text-primary: oklch(0.25 0.015 260);  /* cool-tinted dark */

/* Instead of #f5f5f5 */
--surface-bg: oklch(0.97 0.005 260);    /* cool-tinted light */
```

---

## 4. Dark Mode

Dark mode is not "invert everything." Follow these rules:

1. Surface colors get darker but retain their hue tint
2. Text colors flip but never become pure white (use oklch lightness 0.93-0.97)
3. Accent colors often need a lightness bump (+0.05 to +0.10) to maintain contrast
4. Shadows become less visible on dark surfaces; use subtle inner glows or border effects instead
5. Elevation in dark mode goes lighter (higher surfaces are lighter), opposite of light mode
6. Images and illustrations may need reduced brightness/contrast (`filter: brightness(0.9)`)

```css
[data-theme="dark"] {
  --surface-0: oklch(0.13 0.01 260);
  --surface-1: oklch(0.17 0.012 260);
  --surface-2: oklch(0.21 0.015 260);
  --text-primary: oklch(0.93 0.01 260);
  --text-secondary: oklch(0.70 0.01 260);
  --border: oklch(0.25 0.01 260);
}
```

---

## 5. Accessibility

### Contrast Requirements (WCAG 2.2)
- Normal text (<24px or <18.66px bold): 4.5:1 minimum
- Large text (>=24px or >=18.66px bold): 3:1 minimum
- UI components and graphical objects: 3:1 minimum
- Focus indicators: 3:1 against adjacent colors

### Testing
Use OKLCH lightness difference as a quick heuristic: a difference of 0.40+ between text and background lightness values usually passes AA. For precise checking, use the APCA (Advanced Perceptual Contrast Algorithm) when possible, as it better represents human perception than WCAG 2.x contrast ratios.

### Color Blindness
Never use color as the only way to convey information. Pair color with icons, patterns, or text labels. Test palettes with a deuteranopia/protanopia simulator.

---

## 6. CSS Variables Pattern

Define all colors as CSS custom properties. Group by function, not by color name.

```css
/* Good: semantic naming */
--color-surface: ...;
--color-text: ...;
--color-accent: ...;
--color-border: ...;

/* Bad: literal naming */
--blue: ...;
--dark-gray: ...;
--light-blue: ...;
```

For component-level overrides:
```css
.card {
  --card-bg: var(--surface-1);
  --card-border: var(--border);
  background: var(--card-bg);
  border: 1px solid var(--card-border);
}
.card.highlighted {
  --card-bg: var(--accent-subtle);
  --card-border: var(--accent);
}
```

---

## 7. Common Mistakes

- Using pure black (#000) for text (use tinted near-black instead)
- Using gray text on colored backgrounds (low contrast, hard to read)
- Applying opacity to achieve lighter colors (makes elements look washed out; use chroma reduction instead)
- Using too many accent colors (one primary accent, one secondary maximum)
- Forgetting to test dark mode after building light mode
- Using brand colors at full saturation for large surfaces (they vibrate and cause eye strain; reserve full chroma for small accents)
- Not providing hover/focus states with visible color change
