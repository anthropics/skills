---
name: roman-cyber-garage
description: Dark cyberpunk design system with complete theme reference — colors, typography, components, modals, tables, cards, badges, buttons, and layout patterns. Use this skill when building dark-themed dashboards, admin panels, trading UIs, or any cyberpunk-aesthetic web interface. Production-tested on real SaaS products.
license: Complete terms in LICENSE.txt
---

# Roman Cyber Garage

A production-tested dark cyberpunk design system extracted from a live SaaS trading platform. Provides exact design tokens, component CSS, and layout patterns for building visually consistent, professional dark-themed web UIs.

The user provides a frontend task — a page, component, modal, dashboard, or UI element to build. Apply the design system below to produce pixel-consistent output matching the cyberpunk aesthetic.

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
| Nav brand | `JetBrains Mono` | 700 | 16-18px |
| Section titles | `JetBrains Mono` | 600 | 12px `uppercase` `letter-spacing: 0.1em` |
| Badges / Buttons | `JetBrains Mono` | 500-700 | 11-12px |
| Big metric values | `JetBrains Mono` | 700 | 24-32px |

## Color Palette

### Backgrounds

| Token | Value | Usage |
|-------|-------|-------|
| `--bg-body` | `#030710` | Page background |
| `--bg-nav` | `rgba(3,7,16,0.85)` | Nav (+ `backdrop-filter: blur(16px)`) |
| `--bg-card` | `rgba(127,200,255,0.02)` | Cards, sections |
| `--bg-card-hover` | `rgba(127,200,255,0.06)` | Card/row hover |
| `--bg-modal` | `#0d1117` | Modal body |
| `--bg-modal-alt` | `#0a0f1e` | Alt modal body |
| `--bg-input` | `#0a0e1a` | Inputs, selects |
| `--bg-panel` | `#161b22` | Inset panels |
| `--bg-overlay` | `rgba(0,0,0,0.75)` | Modal overlay (+ `backdrop-filter: blur(6px)`) |

### Text

| Token | Value | Usage |
|-------|-------|-------|
| `--text-primary` | `#e2e8f0` | Body text |
| `--text-secondary` | `#c8d6e5` | Table cells |
| `--text-muted` | `#6b8299` | Labels, subtitles |
| `--text-dim` | `#4a6278` | Hints, fine print |
| `--text-dimmer` | `#3d4f63` | Footer notes |

### Accents

| Token | Value | Usage |
|-------|-------|-------|
| `--accent-blue` | `#7fc8ff` | Primary — links, values, brand |
| `--accent-gold` | `#facc15` | Admin — titles, active states |

### Semantic / Status Colors

| Token | Value | Usage |
|-------|-------|-------|
| `--color-success` | `#4ade80` | Green — success, bullish, profit, ON |
| `--color-warning` | `#facc15` | Yellow — partial, caution |
| `--color-warning-amber` | `#f59e0b` | Amber — alerts |
| `--color-danger` | `#f87171` | Red — failed, bearish, loss, OFF |
| `--color-info` | `#7fc8ff` | Blue — pending |
| `--color-purple` | `#c084fc` | Purple — features |
| `--color-cyan` | `#06b6d4` | Cyan — secondary features |
| `--color-sky` | `#38bdf8` | Sky blue — tertiary |
| `--color-teal` | `#34d399` | Teal — accents |
| `--color-emerald` | `#10b981` | Emerald — positive accents |
| `--color-rose` | `#f43f5e` | Rose — alerts |
| `--color-indigo` | `#6366f1` | Indigo — gradients |

### Border Opacity Scale

| Level | Value | Usage |
|-------|-------|-------|
| subtle | `rgba(127,200,255,0.06)` | Cards, sections |
| light | `rgba(127,200,255,0.08)` | Table headers |
| medium | `rgba(127,200,255,0.12)` | Modals |
| strong | `rgba(127,200,255,0.15)` | Buttons, inputs |
| glow | `rgba(127,200,255,0.3)` | Hover states |

## Neon Top Line

Every page starts with a fixed 2px neon gradient:

```css
.neon-line {
  position: fixed; top: 0; left: 0; right: 0; height: 2px; z-index: 101;
  background: linear-gradient(90deg, transparent, #1E88E5 20%, #42A5F5 80%, transparent);
}
```

## Components

### Nav Bar

```css
.nav {
  position: fixed; top: 2px; left: 0; right: 0; z-index: 100;
  backdrop-filter: blur(16px); background: rgba(3,7,16,0.85);
  border-bottom: 1px solid rgba(127,200,255,0.06);
  padding: 0 24px; height: 56px;
  display: flex; align-items: center; justify-content: space-between;
}
.nav-brand {
  font-family: 'JetBrains Mono', monospace; font-weight: 700;
  font-size: 18px; color: #7fc8ff; letter-spacing: 2px; text-decoration: none;
}
.nav-links { display: flex; gap: 16px; }
.nav-links a { font-size: 14px; color: #6b8299; text-decoration: none; transition: color 0.2s; }
.nav-links a:hover, .nav-links a.active { color: #7fc8ff; }
```

### Page Layout

```css
.container { max-width: 1200px; margin: 0 auto; padding: 80px 20px 40px; }
.page-title {
  font-family: 'JetBrains Mono', monospace; font-size: clamp(24px, 4vw, 36px);
  font-weight: 700; margin-bottom: 8px;
  background: linear-gradient(135deg, #7fc8ff, #a78bfa);
  -webkit-background-clip: text; -webkit-text-fill-color: transparent;
}
.page-subtitle { color: #6b8299; font-size: 14px; margin-bottom: 24px; }
```

### Summary Card

```css
.summary-card {
  background: rgba(127,200,255,0.02); border: 1px solid rgba(127,200,255,0.06);
  border-radius: 12px; padding: 20px; transition: border-color 0.3s;
}
.summary-card:hover { border-color: rgba(127,200,255,0.15); }
.summary-label {
  font-family: 'JetBrains Mono', monospace; font-size: 11px;
  text-transform: uppercase; letter-spacing: 0.1em; color: #6b8299; margin-bottom: 8px;
}
.summary-value {
  font-family: 'JetBrains Mono', monospace; font-size: 32px; font-weight: 700;
  color: #7fc8ff; text-shadow: 0 0 30px rgba(127,200,255,0.15);
}
.summary-value.green { color: #4ade80; text-shadow: 0 0 30px rgba(74,222,128,0.15); }
.summary-value.red { color: #f87171; }
```

### Content Card / Chart Section

```css
.chart-section {
  background: rgba(127,200,255,0.02); border: 1px solid rgba(127,200,255,0.06);
  border-radius: 12px; padding: 24px; margin-bottom: 32px;
}
.section-title {
  font-family: 'JetBrains Mono', monospace; font-size: 12px;
  text-transform: uppercase; letter-spacing: 0.1em; color: #7fc8ff; margin-bottom: 16px;
}
```

### Data Table

```css
.data-table { width: 100%; border-collapse: collapse; }
.data-table th {
  font-family: 'JetBrains Mono', monospace; font-size: 11px;
  text-transform: uppercase; letter-spacing: 0.05em; color: #6b8299;
  padding: 12px 8px; text-align: left; border-bottom: 1px solid rgba(127,200,255,0.08);
}
.data-table td {
  font-family: 'JetBrains Mono', monospace; font-size: 13px;
  padding: 12px 8px; color: #c8d6e5; border-bottom: 1px solid rgba(127,200,255,0.04);
}
.data-table tr:hover td { background: rgba(127,200,255,0.02); }
```

### Badges

```css
.badge {
  display: inline-block; padding: 3px 10px; border-radius: 6px;
  font-size: 11px; font-weight: 600; font-family: 'JetBrains Mono', monospace;
}
.badge-success { background: rgba(34,197,94,0.15);  color: #4ade80; }
.badge-danger  { background: rgba(239,68,68,0.15);  color: #f87171; }
.badge-warning { background: rgba(234,179,8,0.15);  color: #facc15; }
.badge-info    { background: rgba(127,200,255,0.1);  color: #7fc8ff; }
.badge-muted   { background: rgba(107,130,153,0.15); color: #6b8299; }
```

### Buttons — Tab Switcher

```css
.tab-btn {
  background: rgba(127,200,255,0.04); border: 1px solid rgba(127,200,255,0.08);
  color: #6b8299; padding: 7px 16px; border-radius: 6px;
  font-family: 'JetBrains Mono', monospace; font-size: 11px;
  cursor: pointer; transition: all 0.2s;
}
.tab-btn:hover { border-color: rgba(127,200,255,0.2); color: #e2e8f0; }
.tab-btn.active { background: rgba(127,200,255,0.1); border-color: #7fc8ff; color: #7fc8ff; }
```

### Buttons — Color-Coded Action

Replace `COLOR_RGB` and `COLOR_HEX` with any semantic color:

```css
.action-btn {
  background: rgba(COLOR_RGB, 0.1); border: 1px solid rgba(COLOR_RGB, 0.25);
  color: COLOR_HEX; padding: 6px 16px; border-radius: 6px;
  font-size: 12px; font-family: 'JetBrains Mono', monospace;
  cursor: pointer; transition: all 0.15s;
}
.action-btn:hover { background: rgba(COLOR_RGB, 0.2); }
```

### Buttons — Toggle (ON/OFF)

```css
.toggle-btn {
  padding: 4px 14px; border-radius: 6px; font-size: 11px; font-weight: 700;
  font-family: 'JetBrains Mono', monospace; border: 1px solid rgba(127,200,255,0.15);
  cursor: pointer; transition: all 0.15s; min-width: 50px; text-align: center;
}
.toggle-btn.on  { background: rgba(74,222,128,0.15); color: #4ade80; border-color: rgba(74,222,128,0.3); }
.toggle-btn.off { background: rgba(248,113,113,0.1);  color: #f87171; border-color: rgba(248,113,113,0.2); }
```

### Buttons — CTA

```css
.btn-cta {
  padding: 10px 24px; border-radius: 10px; border: none;
  background: linear-gradient(135deg, #3b82f6, #6366f1);
  color: #fff; font-size: 14px; font-weight: 500; cursor: pointer;
}
.btn-outline {
  padding: 10px 24px; border-radius: 10px;
  background: rgba(127,200,255,0.08); color: #7fc8ff;
  border: 1px solid rgba(127,200,255,0.15);
  font-family: 'JetBrains Mono', monospace; font-size: 13px; font-weight: 600;
  cursor: pointer; transition: all 0.2s;
}
.btn-outline:hover { background: rgba(127,200,255,0.15); }
```

### Modal

```css
.modal-overlay {
  display: none; position: fixed; inset: 0; z-index: 10000;
  background: rgba(0,0,0,0.75); backdrop-filter: blur(6px);
  align-items: flex-start; justify-content: center;
  padding: 40px 20px; overflow-y: auto;
}
.modal-overlay.open { display: flex; }
.modal-body {
  background: #0d1117; border: 1px solid rgba(ACCENT_RGB, 0.15);
  border-radius: 14px; max-width: 640px; width: 100%;
  padding: 24px; position: relative;
  box-shadow: 0 20px 60px rgba(0,0,0,0.5);
}
.modal-close {
  position: absolute; top: 14px; right: 14px;
  background: none; border: none; color: #6b8299;
  font-size: 22px; cursor: pointer; padding: 4px 8px; line-height: 1;
}
.modal-title {
  font-family: 'JetBrains Mono', monospace; font-size: 16px;
  font-weight: 700; color: ACCENT_HEX;
}
```

### Form Inputs

```css
.form-input {
  background: rgba(ACCENT_RGB, 0.06); border: 1px solid rgba(ACCENT_RGB, 0.15);
  color: #e2e8f0; padding: 6px 10px; border-radius: 8px;
  font-size: 12px; font-family: 'JetBrains Mono', monospace; outline: none;
}
.form-select {
  background: #0a0e1a; color: #e2e8f0;
  border: 1px solid rgba(127,200,255,0.15); border-radius: 8px;
  padding: 6px 12px; font-family: 'JetBrains Mono', monospace; font-size: 12px;
}
```

### Status Dots

```css
.status-dot { display: inline-block; width: 8px; height: 8px; border-radius: 50%; margin-right: 6px; }
.status-dot.ok   { background: #4ade80; box-shadow: 0 0 8px rgba(74,222,128,0.5); }
.status-dot.fail { background: #f87171; }
```

### Alert Banners

```css
.banner-error {
  padding: 14px 18px; border-radius: 10px;
  background: rgba(248,113,113,0.12); border: 1px solid rgba(248,113,113,0.4);
  color: #f87171;
}
.banner-warn {
  padding: 14px 18px; border-radius: 12px;
  background: rgba(255,152,0,0.1); border: 1px solid rgba(255,152,0,0.25);
  color: #ffb74d;
}
```

### Glow Effects

```css
/* Text glow */
text-shadow: 0 0 30px rgba(127,200,255,0.15);
/* Box glow on hover */
box-shadow: 0 0 20px rgba(127,200,255,0.06);
/* Modal shadow */
box-shadow: 0 20px 60px rgba(0,0,0,0.5), 0 0 40px rgba(127,200,255,0.05);
```

## Layout Grids

| Pattern | CSS |
|---------|-----|
| Summary cards | `grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 16px` |
| 2-column | `grid-template-columns: 1fr 1fr; gap: 16px` |
| 3-column | `grid-template-columns: repeat(auto-fit, minmax(340px, 1fr)); gap: 16px` |
| Button row | `display: flex; gap: 6-8px; flex-wrap: wrap` |

## Mobile (max-width: 768px)

```css
@media (max-width: 768px) {
  .container { padding: 72px 12px 24px; }
  .summary-grid { grid-template-columns: repeat(2, 1fr); }
  .summary-value { font-size: 24px; }
  .chart-container { height: 220px; }
  .hide-mobile { display: none; }
}
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
    <div class="nav-links">
      <a href="/" class="active">PAGE_TITLE</a>
    </div>
  </nav>
  <div class="container">
    <h1 class="page-title">PAGE_TITLE</h1>
    <p class="page-subtitle">Description</p>
  </div>
</body>
</html>
```

## Rules

1. `JetBrains Mono` for ALL data, numbers, labels, section titles, badges, buttons, code
2. `Inter` for body text, paragraphs, descriptions
3. NEVER use pure white `#fff` — max is `#e2e8f0`
4. NEVER use solid black borders — always `rgba(127,200,255,...)` with low opacity
5. Cards/sections: `border-radius: 12px`, 1px border
6. Modals: `border-radius: 14px`, accent-colored border
7. Buttons: `border-radius: 6-8px`
8. Background opacity: `0.02` rest, `0.04-0.06` hover, `0.1-0.15` active
9. Border opacity: `0.06` subtle, `0.08-0.12` normal, `0.15-0.3` prominent, `0.5` active
10. Each feature gets a unique accent color from the semantic palette
11. Modals close on overlay click
12. `backdrop-filter: blur()` — nav 16-20px, modal overlays 4-8px
13. Always include the neon-line at top of every page
14. Transition speeds: `0.15s` buttons, `0.2s` links, `0.3s` cards
