# Typography Rules Reference

## Font Hierarchy

A well-structured type system has 3–4 levels:

| Level | Purpose | Typical Size | Weight |
|---|---|---|---|
| Display / H1 | Hero titles, page names | 32–72px | Bold or Black |
| H2 / Section | Section headings | 24–36px | SemiBold or Bold |
| H3 / Subsection | Sub-groupings | 18–24px | Medium or SemiBold |
| Body | Main reading content | 14–16px | Regular |
| Caption / Label | Supporting info, metadata | 11–13px | Regular or Medium |

**Rule**: Each level should be visually distinct from adjacent levels. If H2 and H3 look the same, one of them is doing nothing.

---

## Font Pairing

### The 2-Font Rule
Use a maximum of **2 typefaces** in one design:
- One for **headings** (display, expressive)
- One for **body** (readable, neutral)

Optionally, use one font family with different weights (Bold for headings, Regular for body). This always looks cohesive.

### Good Pairing Patterns
- **Serif heading + Sans-serif body** — Classic, trustworthy (e.g., Playfair + Inter... wait, avoid Inter. Try Playfair + Source Sans)
- **Sans-serif heading + Sans-serif body** — Clean, modern (different weights of the same family)
- **Display/decorative heading + Simple body** — Expressive but readable

### Font Families to Avoid (Overused / Generic)
- Inter (massively overused in AI-generated UIs)
- Roboto (Android default, feels generic)
- Arial / Helvetica (system fallback, no personality)
- Times New Roman (dated unless intentionally retro)

### Better Alternatives
**For body text**: Source Sans 3, DM Sans, Nunito, Lato, Figtree, Plus Jakarta Sans
**For headings**: Fraunces, Syne, Clash Display, Cabinet Grotesk, Satoshi, Bricolage Grotesque
**For monospace/code**: JetBrains Mono, Fira Code, IBM Plex Mono

---

## Size Scale

Use a **modular scale** — sizes based on a ratio, not arbitrary numbers:

### Major Third Scale (1.25×)
12 → 15 → 19 → 24 → 30 → 38 → 48 → 60px

### Perfect Fourth Scale (1.333×)
12 → 16 → 21 → 28 → 37 → 50px

### Practical Scale (Most Common)
12, 14, 16, 18, 20, 24, 28, 32, 36, 48, 60, 72px

**Minimum sizes**:
- Body text: **16px** (14px acceptable, 12px only for captions)
- Mobile body: **16px** minimum (browsers auto-zoom below this)
- Tiny labels: **11px** minimum, never smaller

---

## Line Height (Leading)

| Text Type | Line Height Multiplier |
|---|---|
| Large headings (40px+) | 1.1–1.2× |
| Medium headings (24–40px) | 1.2–1.35× |
| Body text | 1.4–1.6× |
| Captions / small text | 1.3–1.5× |

**Example**: 16px body text → line-height: 24px (1.5×)

**Never use line-height: 1** for multi-line text. It's unreadable.

---

## Line Length (Measure)

- **Optimal**: 60–75 characters per line (~550–680px at 16px)
- **Acceptable**: 45–90 characters
- **Too wide**: 100+ characters (eye has to travel too far)
- **Too narrow**: Under 40 characters (too many line breaks, choppy)

In CSS: `max-width: 65ch` is a great rule for body text containers.

---

## Letter Spacing (Tracking)

- **Body text**: 0 or very slightly positive (0–0.01em)
- **Small caps / all caps**: Always add letter spacing (0.05–0.1em). All-caps with no tracking looks cramped.
- **Large display text**: Often slightly negative (-0.02 to -0.04em). Tighter feels more premium.
- **Never**: Negative letter spacing on body text (hurts readability)

---

## Text Contrast (WCAG)

| Text Type | Minimum Contrast Ratio |
|---|---|
| Normal text (under 18px regular / 14px bold) | 4.5:1 |
| Large text (18px+ regular or 14px+ bold) | 3:1 |
| UI components (borders, icons) | 3:1 |
| Decorative text | No requirement |

**How to check**: Use a contrast checker. Common tools: Figma's built-in accessibility checker, WebAIM Contrast Checker, or browser devtools.

**Common failures**:
- Light gray body text on white (#999 on white = ~2.8:1 — fails!)
- Yellow or light green text on white
- Any low-opacity text overlay on images without a dark scrim

---

## Alignment Rules

- **Left-align body text** in most Western/LTR languages. It's the most readable.
- **Center-align** only for short text: headlines, CTAs, hero text, labels.
- **Never center-align** long body paragraphs. It's exhausting to read.
- **Right-align** numbers in tables (so decimal points align).
- **Avoid justified text** on the web (creates uneven word spacing, looks bad without hyphenation).

---

## Common Typography Mistakes

1. **Using too many font sizes** — Pick 4–5 and stick to them. Designers call this a "type ramp."
2. **All caps body text** — Extremely hard to read in long form. Reserve for labels and buttons only.
3. **Bold everything** — If everything is bold, nothing is bold. Bold = emphasis, use sparingly.
4. **Underlining non-links** — Users will click underlined text expecting it to be a link.
5. **Low-contrast text** — The single most common accessibility failure. Always check.
6. **Inconsistent alignment** — Some centered, some left-aligned, some right-aligned with no system = chaos.
7. **No hierarchy** — Everything the same size = wall of text.

---

## Fluid Typography (clamp())

Static type sizes break at breakpoints. Fluid typography scales smoothly between a minimum and maximum size based on viewport width.

### How clamp() Works

```css
font-size: clamp(MIN, PREFERRED, MAX);
```

- **MIN** — smallest the text should ever be (e.g. on narrow mobile)
- **PREFERRED** — fluid value using `vw` (viewport width) units
- **MAX** — largest the text should ever be (e.g. on wide desktop)

### Common Fluid Type Values

```css
/* Body text: 16px → 18px */
font-size: clamp(1rem, 0.9rem + 0.5vw, 1.125rem);

/* H2: 24px → 36px */
font-size: clamp(1.5rem, 1.2rem + 1.5vw, 2.25rem);

/* H1: 32px → 60px */
font-size: clamp(2rem, 1.5rem + 2.5vw, 3.75rem);

/* Display: 48px → 80px */
font-size: clamp(3rem, 2rem + 5vw, 5rem);
```

### When to Use Fluid Typography
- Headings and display text — biggest win
- Hero sections and large callouts
- Any text that appears at very different sizes across breakpoints

### When NOT to Use It
- Body text (usually fine staying at 16px)
- Labels, captions, small UI text (should stay fixed and readable)
- When you need pixel-perfect control at specific breakpoints

### The Rule
Fluid type should never drop below its minimum readable size. Always test `clamp()` values at the narrowest viewport you support.
