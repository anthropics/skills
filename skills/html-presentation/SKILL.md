---
name: html-presentation
description: "Create, edit, and iterate on high-quality single-file HTML slide presentations (1280x720px, PDF-exportable). Use when the user wants to build or improve a pitch deck, hackathon presentation, demo deck, or any slideshow as a self-contained HTML file. Triggers on requests like 'make a presentation', 'create slides', 'build a pitch deck', 'add a slide about X', or iteration feedback like 'too text-heavy', 'add more visuals', 'fix the layout', 'make it look better', 'this slide is boring', 'looks like a website not a pitch deck'."
license: Complete terms in LICENSE.txt
---

# HTML Presentation Skill

Single-file HTML presentations that render at 1280×720px per slide, look great in browser, and export cleanly to PDF via Cmd+P.

## Setup

### Dimensions & Print
```css
.slide { width: 1280px; height: 720px; overflow: hidden; page-break-after: always; }
.slide-inner { padding: 52px 72px; display: flex; flex-direction: column; position: relative; z-index: 1; }
@page { size: 1280px 720px; margin: 0; }
@media print { * { box-shadow: none !important; } }  /* critical — shadows cause PDF artifacts */
@media screen { body { display: flex; flex-direction: column; align-items: center; gap: 32px; padding: 32px; } }
```

### Fonts (always load from Google Fonts)
- **Primary:** Outfit (300, 400, 500, 600, 700, 800) — all body, headings, UI
- **Accent:** Instrument Serif italic — one key word per major heading only
- **Mono:** JetBrains Mono (400, 500) — eyebrow labels, code, slide numbers

### Color Palette
```css
--bg-primary: #F7FAF8;  --bg-card: rgba(255,255,255,0.5);
--text-primary: #0F172A;  --text-secondary: #475569;  --text-muted: #94A3B8;
--accent-teal: #0D9488;  --accent-blue: #3B82F6;  --accent-violet: #7C3AED;
--accent-orange: #EA580C;  --border: rgba(0,0,0,0.08);
--critical: #DC2626;  --success: #16A34A;
```

## Quality Standards

Read `references/aesthetics.md` for the full quality bar before starting any presentation.

**Non-negotiable rules:**
1. **Lead with WHY.** Every slide opens with a narrative paragraph before data or diagrams.
2. **Stats in context.** Embed numbers in prose; don't float them as giant orphaned cards.
3. **No over-decoration.** Cards: one subtle border (`rgba(0,0,0,0.08)`), no colored left-borders, no dot-pills, no badge stacking.
4. **Text prominence.** Body narrative ≥ 16px. Labels/captions: 11–12px. Critical narrative never at 12px.
5. **Diagrams beat text cards.** Pipeline/architecture/flow → inline SVG with arrows, not text boxes.

## Typography Hierarchy

| Role | Size | Weight | Font |
|------|------|--------|------|
| Title slide h1 | 48–56px | 700 | Outfit, letter-spacing -0.02em |
| Slide heading h2 | 34px | 700 | Outfit, letter-spacing -0.015em |
| Card heading h3 | 18px | 600 | Outfit |
| Narrative body | 16–17px | 400 | Outfit, line-height 1.65, color: var(--text-secondary) |
| Eyebrow label | 11px | 500 | JetBrains Mono, UPPERCASE, teal, letter-spacing 0.1em |
| Stat number | 28–36px | 700 | Outfit, letter-spacing -0.02em |
| Caption/muted | 11–12px | 400 | Outfit, color: var(--text-muted) |

**Accent italic:** `<span style="font-family:'Instrument Serif',serif;font-style:italic;color:var(--accent-teal);">word</span>` — one emotionally resonant word per major heading.

## Slide Anatomy

```html
<div class="slide">
  <!-- z-index 0: optional decorative glows or photo accents (max 2) -->
  <div class="slide-inner">
    <div class="label">Section Name</div>   <!-- eyebrow -->
    <h2>Slide <span class="accent-italic">Title</span></h2>
    <p>Narrative WHY paragraph...</p>
    <!-- content: cards, diagrams, tables, lists -->
  </div>
  <div class="brand-mark">...</div>         <!-- bottom-left: logo + product name -->
  <div class="slide-number">04 / 15</div>  <!-- bottom-right: JetBrains Mono, 11px -->
</div>
```

## Component Patterns

### Background Decorations (max 2 per slide, always z-index 0)
```html
<!-- Soft radial glow blob -->
<div style="position:absolute;border-radius:50%;filter:blur(120px);opacity:0.06;z-index:0;
  background:var(--accent-teal);width:500px;height:500px;top:-100px;right:-100px;"></div>

<!-- Edge photo accent (atmospheric only) -->
<div style="position:absolute;right:0;top:0;width:420px;height:720px;z-index:0;overflow:hidden;">
  <img src="[unsplash]" style="width:100%;height:100%;object-fit:cover;opacity:0.12;filter:saturate(0.4);">
  <div style="position:absolute;inset:0;background:linear-gradient(90deg,var(--bg-primary) 0%,transparent 40%,transparent 60%,var(--bg-primary) 100%);"></div>
</div>
```

### Cards
```html
<!-- Standard card -->
<div style="background:var(--bg-card);border:1px solid var(--border);border-radius:10px;padding:22px;">
<!-- Small card -->
<div style="background:var(--bg-card);border:1px solid var(--border);border-radius:8px;padding:14px 16px;">
<!-- Info/narrative card -->
<div style="background:var(--bg-card);border:1px solid var(--border);border-radius:10px;padding:16px 18px;">
```

### Pipeline Flow (horizontal)
```html
<div style="display:flex;align-items:center;justify-content:center;gap:0;">
  <div style="text-align:center;flex:1;">
    <div style="font-size:20px;font-weight:700;color:var(--accent-teal);">6</div>
    <div style="font-size:11px;color:var(--text-secondary);">Data Sources</div>
  </div>
  <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="#CBD5E1" stroke-width="2"><path d="M5 12h14M12 5l7 7-7 7"/></svg>
  <!-- repeat for each stage -->
</div>
```

### Architecture Diagram
Inline `<svg viewBox="0 0 1136 380">` with `<rect>` column containers, `<text>` in JetBrains Mono, and `<line>`/`<path>` arrows in teal (`#0D9488`).

### Tech Logos (CDN)
```html
<img src="https://cdn.simpleicons.org/{name}/{hex-without-#}" style="width:24px;height:24px;">
<!-- Example: https://cdn.simpleicons.org/python/0D9488 -->
```

### Format/Standard Tags
```html
<span style="background:rgba(13,148,136,0.1);color:#0D9488;padding:3px 9px;border-radius:5px;
  font-size:11px;font-family:'JetBrains Mono',monospace;font-weight:500;">FHIR R4</span>
```

## Slide Type Recipes

**Title slide:** Left: logo + product name + large h1 + 2–3 sentence description + 4 key metrics row + team + links. Right: floating UI preview cards (absolutely positioned decorative). Background: radial teal glow + faint ECG SVG line at 6% opacity.

**Problem slide:** Narrative story paragraph (pain as a real scenario), 3 stat cards, then 2-col info cards with nuanced WHY context. Edge photo accent at opacity 0.12.

**Solution slide:** 2-sentence overview, then 3-column card grid (icon + h3 + narrative paragraph each). Bottom: horizontal pipeline flow with key numbers and arrows.

**Architecture slide:** heading + 1-sentence description + full-width inline SVG diagram with column headers, component boxes, and directional arrows.

**Tech stack slide:** 4-column grid by category (Backend, AI/ML, Frontend, Standards). Each item: CDN logo img + name + brief role. Fetch real logos — no plain text tags.

**Performance/metrics slide:** Visual charts (CSS bars or inline SVG), per-class breakdowns, methodology note at bottom.

**Roadmap slide:** 3 phase columns, distinct accent colors, title + timeframe + 3–4 bullets each. Vision statement at bottom, italic, large, centered.

**Closing slide:** Minimal. Large product name, one italic tagline, key links. Mirror title slide background.

## Iteration & Verification

1. Serve: `python3 -m http.server 8765` → `http://localhost:8765/presentation.html`
2. Screenshot every modified slide; check no overflow, readable text, images load
3. PDF test: Cmd+P → Save as PDF → verify `@page` sizing applies
4. Overflow fix: reduce font 1–2px, compress padding, or cut content

## Anti-Patterns

- Slides that read like a website (pills/badges everywhere, colorful borders)
- Giant isolated stat cards with no surrounding narrative
- Body narrative at 12px or smaller
- Text-only architecture/pipeline slides — use SVG diagrams
- `box-shadow` in `@media print` — causes PDF rendering artifacts
- Dark backgrounds on text-heavy slides
- More than 2 background decorations per slide
- Slide count padding — consolidate when multiple slides cover the same concept
- Colored dots inside pill badges
