---
name: brutalist-swiss-landing-page
description: Build landing pages in Web Brutalism or Swiss International Typographic Style. Use this skill when the user asks for a landing page, hero section, or product page that should feel raw and confrontational, or clean and grid-driven. Produces committed, specific design code — not a surface-level imitation.
license: Complete terms in LICENSE.txt
---

This skill builds landing pages in one of two design traditions: **Web Brutalism** or **Swiss / International Typographic Style**. They look nothing alike and think about design completely differently. Pick the one that fits. If the user doesn't specify, read the brief and choose — then go all the way.

The user gives you a product, service, or brand. Your job is to translate that into a real, working page. HTML/CSS/JS or React, whichever they need.

---

## The Two Styles

Before writing any code, get clear on which world you're working in.

### Brutalism

Brutalism on the web isn't an accident. It's a rejection — of polish, of gentle UX, of the idea that interfaces should be frictionless. It looks raw because it means to.

What it actually uses:
- Heavy borders, usually 3–6px solid. No blur on shadows — just hard offsets: `box-shadow: 4px 4px 0 #ff2d00`
- Black, white, and one aggressive accent. Maybe a neon. No gradients unless you're breaking a rule on purpose
- Monospaced or ultra-weight grotesque type. `Space Mono`, `Courier New`, `Impact`. Headlines at 10vw or bigger
- Layouts that look wrong on first glance. Elements that overlap. Grids that get violated
- Hover states that feel blunt — color inversions, hard underlines, cursor switched to crosshair
- Scrolling marquees, visible `<hr>` elements, old-internet structure used deliberately

The failure mode here is softening it. If it looks "pretty," you've missed the point. Uncomfortable-but-intentional is the target.

---

### Swiss / International Typographic Style

Swiss design came out of Zürich and Basel in the 1950s. It's where the grid came from. It's where Helvetica came from. The philosophy: design serves communication, and everything else is noise.

What it actually uses:
- A strict column grid — 12 columns, consistent gutters, nothing breaks out of it
- Flush-left alignment (ragged right). Never justified
- Helvetica Neue if it's on the system, or `Barlow`, `Archivo`, `DM Sans` as open-source alternatives. One display size, one body size, one caption size
- Black, white, and one accent (classic Swiss red is `#e63c2f`). That's it
- White space that's mathematically intentional, not just empty
- Motion only when it communicates something — a fade-in on load is fine, a spinning logo is not

The failure mode here is adding personality because you're bored. Swiss design earns its look through precision. If an element can't justify being there, remove it.

---

## Before You Write Code

Answer these first:

1. Brutalism or Swiss? If the brand is rebellious or provocative, Brutalism. If it's rational, technical, or professional, Swiss.
2. What's the single typographic moment — the one headline or number that has to land?
3. What are the three colors? Write them as CSS variables before anything else.
4. What's the grid? For Swiss: columns, gutters, max-width. For Brutalism: where will you break it?
5. What sections does the page need? Hero, features, CTA, footer — sketch it out.

---

## Specific Rules

### Type

Brutalism: pick something with weight or character. `Helvetica Neue Black`, `Impact`, `DM Mono`, `Space Mono`. Mix weights aggressively. Headlines should feel too big.

Swiss: one typeface, strict hierarchy. Load it from Google Fonts if needed. Size ratios should be consistent — if your body is 16px, your display might be 72px, your caption 12px. No in-between sizes that don't belong to the scale.

Never use: Inter, Roboto, Poppins, Nunito. These are defaults, not choices.

### Color

```css
/* Brutalism */
:root {
  --bg: #0a0a0a;
  --fg: #f0f0f0;
  --accent: #ff2d00;
  --border: #f0f0f0;
}

/* Swiss */
:root {
  --bg: #ffffff;
  --fg: #111111;
  --accent: #e63c2f;
  --grid-gap: 2rem;
}
```

### Grid

Swiss — define it and stick to it:
```css
.grid {
  display: grid;
  grid-template-columns: repeat(12, 1fr);
  gap: var(--grid-gap);
  max-width: 1400px;
  margin: 0 auto;
  padding: 0 2rem;
}
```

Brutalism — start with a grid, then break it. `position: absolute` to pull elements out. `mix-blend-mode` for collisions. Thick borders as structural dividers.

### Motion

Brutalism: instant. Color inversions, no easing, `step-end` or `linear`. Maybe a marquee.

Swiss: one clean fade-in on page load (`opacity: 0` to `1`, 300ms). Nav links get a sliding underline on hover. That's usually enough.

---

## What Each Section Should Do

**Hero**
- Brutalism: full viewport, headline at 12–16vw, one CTA button with hard shadow and invert-on-hover. A scrolling ticker below if it fits the brand.
- Swiss: grid-aligned headline flush left, subheadline at half the size, one CTA. Vertical rhythm should feel like it was measured.

**Features**
- Brutalism: number each feature with an oversized numeral (80–120px). Borders between items. Copy is short and blunt. No icons.
- Swiss: 3 or 6 columns. Each block has a category label (small caps or light weight), a headline, and one sentence. Everything aligns.

**CTA**
- Brutalism: full-bleed, inverted colors, aggressive copy, one button.
- Swiss: white space, centered or grid-aligned, direct copy, minimal button (outlined or solid accent, no decoration).

**Footer**
- Brutalism: black background, monospaced type, raw link lists, copyright in the accent color.
- Swiss: grid columns of links, small type, nothing decorative.

---

## Hard Stops

These apply to both styles:

- No `border-radius`. Not even 2px.
- No blurred box shadows in Swiss. Ever.
- No gradients unless you're doing something deliberately transgressive in Brutalism.
- No stock illustration. No clip art.
- No centered body text.
- Two typefaces maximum.
- No Tailwind, no Bootstrap. Handwritten CSS only.
- No animation that doesn't communicate something.

---

## Code Requirements

- Single-file HTML with embedded `<style>` and `<script>`, or a React component — whatever the user asks for
- Semantic HTML: `<header>`, `<main>`, `<section>`, `<footer>`, `<nav>`
- All colors, fonts, and spacing as CSS custom properties on `:root`
- Responsive — mobile-first for Swiss, desktop-first acceptable for Brutalism
- Accessible: contrast ratios pass WCAG AA, focus states on all interactive elements

---

## Reference Points

For Brutalism: look at early Balenciaga.com, Bloomberg's typographic section headers, the brutalistwebsites.com gallery.

For Swiss: Armin Hofmann's posters, Josef Müller-Brockmann's grid diagrams, Vignelli's NYC subway work. The original Neue Grafik magazine if you can find scans.

Don't copy these. Understand what they're doing and why, then make something new.

---

## One Last Thing

Brutalism with soft edges is just bad design. Swiss with decorative clutter is the same. Both styles require you to commit to rules and follow them — even when your instinct is to add something "just to make it more interesting."

If you're ever tempted to add a gradient, a rounded corner, or a drop shadow with blur in a Swiss layout, that's the instinct to ignore.
