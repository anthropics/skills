---
name: cyber-garage
description: "Builds dark cyberpunk web interfaces with a production-tested design system. Provides exact colors, typography, component CSS, layout grids, and page templates. Use when the user asks to build dashboards, admin panels, dark-themed pages, trading UIs, or any web interface with a cyberpunk aesthetic."
---

# Cyber Garage — Dark Cyberpunk Design System

Production-tested design system extracted from a live SaaS platform. Provides exact design tokens and copy-paste CSS for building pixel-consistent dark-themed web UIs.

- Full component CSS: [references/COMPONENTS.md](references/COMPONENTS.md)

## Fonts

```html
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=JetBrains+Mono:wght@300;400;500;700&display=swap" rel="stylesheet">
```

| Usage | Font | Weight | Size |
|-------|------|--------|------|
| Body text | `Inter` | 400 | 14px |
| Headings | `Inter` | 600-700 | 18-36px |
| Code / Data / Labels | `JetBrains Mono` | 400-700 | 11-13px |
| Section titles | `JetBrains Mono` | 600 | 12px `uppercase` `letter-spacing: 0.1em` |
| Badges / Buttons | `JetBrains Mono` | 500-700 | 11-12px |
| Big metric values | `JetBrains Mono` | 700 | 24-32px |

## Color Palette

### Backgrounds

| Token | Value | Usage |
|-------|-------|-------|
| body | `#030710` | Page background |
| nav | `rgba(3,7,16,0.85)` | Nav (+ `backdrop-filter: blur(16px)`) |
| card | `rgba(127,200,255,0.02)` | Cards, sections |
| card-hover | `rgba(127,200,255,0.06)` | Hover states |
| modal | `#0d1117` | Modal body |
| input | `#0a0e1a` | Form inputs |
| panel | `#161b22` | Inset panels |
| overlay | `rgba(0,0,0,0.75)` | Modal overlay (+ `backdrop-filter: blur(6px)`) |

### Text

| Token | Value | Usage |
|-------|-------|-------|
| primary | `#e2e8f0` | Body text (never use pure `#fff`) |
| secondary | `#c8d6e5` | Table cells |
| muted | `#6b8299` | Labels, subtitles |
| dim | `#4a6278` | Hints |
| dimmer | `#3d4f63` | Footer notes |

### Accents

| Token | Value | Usage |
|-------|-------|-------|
| blue | `#7fc8ff` | Primary — links, values, brand (user pages) |
| gold | `#facc15` | Admin — titles, active states |

### Semantic Colors

| Token | Value |
|-------|-------|
| success | `#4ade80` |
| warning | `#facc15` |
| amber | `#f59e0b` |
| danger | `#f87171` |
| info | `#7fc8ff` |
| purple | `#c084fc` |
| cyan | `#06b6d4` |
| sky | `#38bdf8` |
| teal | `#34d399` |
| emerald | `#10b981` |
| rose | `#f43f5e` |
| indigo | `#6366f1` |

### Border Opacity Scale

| Level | Value | Usage |
|-------|-------|-------|
| subtle | `rgba(127,200,255,0.06)` | Cards |
| light | `rgba(127,200,255,0.08)` | Table headers |
| medium | `rgba(127,200,255,0.12)` | Modals |
| strong | `rgba(127,200,255,0.15)` | Buttons, inputs |
| glow | `rgba(127,200,255,0.3)` | Hover states |

## Neon Top Line

Every page starts with:
```html
<div class="neon-line"></div>
```
```css
.neon-line {
  position: fixed; top: 0; left: 0; right: 0; height: 2px; z-index: 101;
  background: linear-gradient(90deg, transparent, #1E88E5 20%, #42A5F5 80%, transparent);
}
/* Admin variant: transparent, #eab308 20%, #facc15 80%, transparent */
```

## Layout

```css
.container { max-width: 1200px; margin: 0 auto; padding: 80px 20px 40px; }
```

| Pattern | CSS |
|---------|-----|
| Summary cards | `grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 16px` |
| 2-column | `grid-template-columns: 1fr 1fr; gap: 16px` |
| 3-column | `grid-template-columns: repeat(auto-fit, minmax(340px, 1fr)); gap: 16px` |
| Button row | `display: flex; gap: 6-8px; flex-wrap: wrap` |

### Mobile (768px)

```css
@media (max-width: 768px) {
  .container { padding: 72px 12px 24px; }
  .summary-grid { grid-template-columns: repeat(2, 1fr); }
  .summary-value { font-size: 24px; }
  .chart-container { height: 220px; }
  .hide-mobile { display: none; }
}
```

## Glow Effects

```css
text-shadow: 0 0 30px rgba(127,200,255,0.15);   /* text glow */
box-shadow: 0 0 20px rgba(127,200,255,0.06);     /* box hover */
box-shadow: 0 20px 60px rgba(0,0,0,0.5), 0 0 40px rgba(127,200,255,0.05); /* modal */
```

## Page Skeleton

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>PAGE_TITLE</title>
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700&family=JetBrains+Mono:wght@300;400;500;700&display=swap" rel="stylesheet">
  <style>
    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
    body { background: #030710; color: #e2e8f0; font-family: 'Inter', sans-serif; min-height: 100vh; }
    a { color: #7fc8ff; text-decoration: none; }
  </style>
</head>
<body>
  <div class="neon-line"></div>
  <nav class="nav">
    <a href="/" class="nav-brand">brand_</a>
    <div class="nav-links"><a href="/" class="active">PAGE_TITLE</a></div>
  </nav>
  <div class="container">
    <h1 class="page-title">PAGE_TITLE</h1>
    <p class="page-subtitle">Description</p>
  </div>
</body>
</html>
```

## Component Library

Full CSS for all components: **[references/COMPONENTS.md](references/COMPONENTS.md)**

Quick list: Nav bar, page titles (gradient), summary cards, chart sections, data tables, badges (6 types), tab buttons, color-coded action buttons, toggle buttons, CTA buttons, config buttons, modals, form inputs, auth bar, status dots, alert banners, icon containers.

## Rules

1. `JetBrains Mono` for ALL data, numbers, labels, section titles, badges, buttons
2. `Inter` for body text, paragraphs, descriptions
3. NEVER use pure white `#fff` — max is `#e2e8f0`
4. NEVER use solid black borders — always `rgba(127,200,255,...)` with low opacity
5. Cards: `border-radius: 12px`, modals: `14px`, buttons: `6-8px`
6. Background opacity: `0.02` rest → `0.04-0.06` hover → `0.1-0.15` active
7. Border opacity: `0.06` subtle → `0.12` normal → `0.15-0.3` prominent
8. Admin pages = gold `#facc15`; user pages = blue `#7fc8ff`
9. Modals close on overlay click
10. `backdrop-filter: blur()` — nav 16-20px, overlays 4-8px
11. Always include the neon-line at top of every page
12. Transitions: `0.15s` buttons, `0.2s` links, `0.3s` cards

---

Copyright (c) 2025-2026 Roman Antonov — [romwtb@gmail.com](mailto:romwtb@gmail.com) — [github.com/roman-rr](https://github.com/roman-rr) — [roman-rr.github.io](https://roman-rr.github.io/)
