---
name: ascii-mockup
description: >
  Generate mobile-first ASCII art UI mockups across 5 responsive breakpoints (iPhone 720, iPad,
  Desktop 1440, Desktop 1920, UWHD). Maps every UI element to versioned design tokens, produces
  ARIA-compliant color palettes, emits CSS custom-property stylesheets with zero hardcoded values,
  CDN-references Google Fonts, and chains with the ux-journey-mapper and frontend-design skills to
  deliver a full design-to-code workflow. Use when someone asks for wireframes, mockups, ASCII UI,
  interface design, design tokens, or responsive layout planning.
license: MIT
---

# ASCII Mockup Skill

Generate comprehensive ASCII art interface mockups that drive a complete, version-controlled
front-end design system. Every run produces:

1. **ASCII wireframes** at each responsive breakpoint
2. **Design token manifest** (`tokens.json` + `tokens.css`)
3. **Component directory scaffold** matched to the project stack
4. **ARIA-compliant color palette** with contrast scores
5. **Changelog entry** under semantic versioning
6. **Chained skill hooks** to `ux-journey-mapper` and `frontend-design`

---

## Breakpoint Reference

| ID         | Label               | Viewport (px)     | Char cols | Notes                          |
|------------|---------------------|-------------------|-----------|--------------------------------|
| `xs`       | iPhone 720 portrait | 390 × 844         | 48        | Touch targets ≥ 44px           |
| `sm`       | iPad tablet         | 768 × 1024        | 96        | Two-column grid baseline       |
| `md`       | Desktop 1440        | 1440 × 900        | 180       | 12-col grid, sidebar + content |
| `lg`       | Desktop 1920        | 1920 × 1080       | 240       | Wide content, gutter space     |
| `xl`       | UWHD (21:9)         | 3440 × 1440       | 430       | Ultra-wide, center-locked max  |

Render **all five** unless the user specifies a subset. Always start with `xs` (mobile-first).

---

## ASCII Mockup Format

Each frame is wrapped in a labeled fence:

```
╔══════════════════════════════════════════════════════╗
║  [BREAKPOINT: xs — iPhone 720 · 390px · 48 cols]     ║
╚══════════════════════════════════════════════════════╝
┌──────────────────────────────────────────────────────┐
│ [STATUS BAR]                            9:41 ▲ ●●●  │
├──────────────────────────────────────────────────────┤
│ ☰  Brand Logo                           🔔 👤        │
├──────────────────────────────────────────────────────┤
│                                                      │
│  ╔══════════════════════════════════════════════╗   │
│  ║  HERO SECTION                                ║   │
│  ║  ┌────────────────────────────────────────┐  ║   │
│  ║  │          [HERO IMAGE / VIDEO]          │  ║   │
│  ║  └────────────────────────────────────────┘  ║   │
│  ║  H1: Page Title Here                         ║   │
│  ║  Body copy — short descriptor line           ║   │
│  ║  ┌──────────────┐  ┌──────────────┐         ║   │
│  ║  │  [CTA btn 1] │  │  [CTA btn 2] │         ║   │
│  ║  └──────────────┘  └──────────────┘         ║   │
│  ╚══════════════════════════════════════════════╝   │
│                                                      │
└──────────────────────────────────────────────────────┘
```

### ASCII Symbol Conventions

| Symbol            | Meaning                             |
|-------------------|-------------------------------------|
| `╔╗╚╝║═`          | Primary container / card boundary   |
| `┌┐└┘│─`          | Secondary container / inner panel   |
| `[TEXT]`          | Interactive element label           |
| `〈 〉`            | Carousel / slider nav               |
| `▓▓▓▓░░░░`        | Progress bar (filled / empty)       |
| `●●●○○`           | Pagination dots / rating            |
| `▲▼◀▶`            | Sort / chevron direction indicators |
| `☰`               | Hamburger menu                      |
| `🔔 👤 🔍`          | Icon placeholders (semantic emoji)  |
| `···`             | Overflow / truncated content        |
| `// ANNOTATION`   | Design note inline                  |

### Layout Annotations

After each frame, add an **annotation block**:

```
// ANNOTATIONS — xs
// NAV:        sticky top, z-index var(--z-nav)
// HERO IMG:   aspect-ratio 16/9, object-fit cover, loading="lazy"
// CTA BTN 1:  primary action → var(--color-action-primary)
// CTA BTN 2:  ghost variant → var(--color-action-ghost)
// SPACING:    padding var(--space-4) each side
// FONT:       H1 → var(--type-scale-3xl), body → var(--type-scale-base)
```

---

## Design Token System

### tokens.json schema

```json
{
  "meta": {
    "name": "<project-name>",
    "version": "1.0.0",
    "date": "<ISO-8601>",
    "generator": "ascii-mockup-skill"
  },
  "color": {
    "brand": {
      "primary":   { "value": "#<hex>", "wcag_on_white": "<ratio>", "wcag_on_black": "<ratio>" },
      "secondary": { "value": "#<hex>", "wcag_on_white": "<ratio>", "wcag_on_black": "<ratio>" },
      "accent":    { "value": "#<hex>", "wcag_on_white": "<ratio>", "wcag_on_black": "<ratio>" }
    },
    "semantic": {
      "action-primary":   { "value": "{color.brand.primary}", "role": "CTA buttons, links" },
      "action-ghost":     { "value": "transparent",            "role": "Secondary CTA border" },
      "surface-base":     { "value": "{color.neutral.50}",     "role": "Page background" },
      "surface-elevated": { "value": "{color.neutral.0}",      "role": "Cards, modals" },
      "text-primary":     { "value": "{color.neutral.900}",    "role": "Body & headings" },
      "text-muted":       { "value": "{color.neutral.500}",    "role": "Captions, metadata" },
      "border-default":   { "value": "{color.neutral.200}",    "role": "Dividers, card edges" },
      "status-success":   { "value": "<hex>",                  "role": "Confirmations" },
      "status-warning":   { "value": "<hex>",                  "role": "Alerts" },
      "status-error":     { "value": "<hex>",                  "role": "Validation errors" },
      "status-info":      { "value": "<hex>",                  "role": "Informational" }
    },
    "neutral": {
      "0":   "#ffffff", "50": "#f9fafb", "100": "#f3f4f6",
      "200": "#e5e7eb", "300": "#d1d5db", "400": "#9ca3af",
      "500": "#6b7280", "600": "#4b5563", "700": "#374151",
      "800": "#1f2937", "900": "#111827", "950": "#030712"
    }
  },
  "typography": {
    "font-family": {
      "display": "'<Display Font>', serif",
      "body":    "'<Body Font>', sans-serif",
      "mono":    "'<Mono Font>', monospace",
      "cdn":     "https://fonts.googleapis.com/css2?family=<param>&display=swap"
    },
    "scale": {
      "xs":   "0.75rem",  "sm":  "0.875rem", "base": "1rem",
      "lg":   "1.125rem", "xl":  "1.25rem",  "2xl":  "1.5rem",
      "3xl":  "1.875rem", "4xl": "2.25rem",  "5xl":  "3rem",
      "6xl":  "3.75rem",  "7xl": "4.5rem"
    },
    "weight": { "regular": 400, "medium": 500, "semibold": 600, "bold": 700, "extrabold": 800 },
    "leading": { "tight": 1.25, "snug": 1.375, "normal": 1.5, "relaxed": 1.625, "loose": 2 }
  },
  "spacing": {
    "0": "0", "px": "1px", "0.5": "0.125rem", "1": "0.25rem",
    "2": "0.5rem",  "3": "0.75rem",  "4": "1rem",    "5": "1.25rem",
    "6": "1.5rem",  "8": "2rem",     "10": "2.5rem", "12": "3rem",
    "16": "4rem",   "20": "5rem",    "24": "6rem",   "32": "8rem"
  },
  "radius": {
    "none": "0", "sm": "0.25rem", "md": "0.375rem", "lg": "0.5rem",
    "xl": "0.75rem", "2xl": "1rem", "3xl": "1.5rem", "full": "9999px"
  },
  "shadow": {
    "sm":  "0 1px 2px 0 rgb(0 0 0 / 0.05)",
    "md":  "0 4px 6px -1px rgb(0 0 0 / 0.1), 0 2px 4px -2px rgb(0 0 0 / 0.1)",
    "lg":  "0 10px 15px -3px rgb(0 0 0 / 0.1), 0 4px 6px -4px rgb(0 0 0 / 0.1)",
    "xl":  "0 20px 25px -5px rgb(0 0 0 / 0.1), 0 8px 10px -6px rgb(0 0 0 / 0.1)",
    "2xl": "0 25px 50px -12px rgb(0 0 0 / 0.25)",
    "none": "none"
  },
  "breakpoint": {
    "xs": "390px", "sm": "768px", "md": "1024px", "lg": "1440px", "xl": "1920px", "2xl": "3440px"
  },
  "z-index": {
    "base": 0, "raised": 10, "dropdown": 100, "sticky": 200,
    "overlay": 300, "modal": 400, "toast": 500, "tooltip": 600
  },
  "motion": {
    "duration": { "instant": "50ms", "fast": "100ms", "normal": "200ms", "slow": "300ms", "slower": "500ms" },
    "easing": {
      "default":    "cubic-bezier(0.4, 0, 0.2, 1)",
      "in":         "cubic-bezier(0.4, 0, 1, 1)",
      "out":        "cubic-bezier(0, 0, 0.2, 1)",
      "spring":     "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
    }
  }
}
```

### tokens.css output (always emit this file — zero hardcoded values)

```css
/* =============================================================================
   DESIGN TOKENS — generated by ascii-mockup-skill v<version>
   DO NOT manually edit. Regenerate via: ascii-mockup tokens regenerate
   ============================================================================= */

/* ── Google Fonts CDN (swap for zero-FOIT) ──────────────────────────────────── */
@import url('https://fonts.googleapis.com/css2?family=<DisplayFont>:wght@700;800&family=<BodyFont>:wght@400;500;600&family=<MonoFont>&display=swap');

:root {
  /* Color — brand */
  --color-brand-primary:   <hex>;
  --color-brand-secondary: <hex>;
  --color-brand-accent:    <hex>;

  /* Color — semantic */
  --color-action-primary:   var(--color-brand-primary);
  --color-action-ghost:     transparent;
  --color-surface-base:     var(--color-neutral-50);
  --color-surface-elevated: var(--color-neutral-0);
  --color-text-primary:     var(--color-neutral-900);
  --color-text-muted:       var(--color-neutral-500);
  --color-border-default:   var(--color-neutral-200);
  --color-status-success:   <hex>;
  --color-status-warning:   <hex>;
  --color-status-error:     <hex>;
  --color-status-info:      <hex>;

  /* Color — neutral scale */
  --color-neutral-0:   #ffffff;
  --color-neutral-50:  #f9fafb;
  --color-neutral-100: #f3f4f6;
  --color-neutral-200: #e5e7eb;
  --color-neutral-300: #d1d5db;
  --color-neutral-400: #9ca3af;
  --color-neutral-500: #6b7280;
  --color-neutral-600: #4b5563;
  --color-neutral-700: #374151;
  --color-neutral-800: #1f2937;
  --color-neutral-900: #111827;
  --color-neutral-950: #030712;

  /* Typography */
  --font-display:  <DisplayFont>, serif;
  --font-body:     <BodyFont>, sans-serif;
  --font-mono:     <MonoFont>, monospace;

  --type-scale-xs:   0.75rem;
  --type-scale-sm:   0.875rem;
  --type-scale-base: 1rem;
  --type-scale-lg:   1.125rem;
  --type-scale-xl:   1.25rem;
  --type-scale-2xl:  1.5rem;
  --type-scale-3xl:  1.875rem;
  --type-scale-4xl:  2.25rem;
  --type-scale-5xl:  3rem;
  --type-scale-6xl:  3.75rem;
  --type-scale-7xl:  4.5rem;

  --font-weight-regular:   400;
  --font-weight-medium:    500;
  --font-weight-semibold:  600;
  --font-weight-bold:      700;
  --font-weight-extrabold: 800;

  --leading-tight:   1.25;
  --leading-snug:    1.375;
  --leading-normal:  1.5;
  --leading-relaxed: 1.625;
  --leading-loose:   2;

  /* Spacing */
  --space-0:    0;
  --space-px:   1px;
  --space-0\5:  0.125rem;
  --space-1:    0.25rem;
  --space-2:    0.5rem;
  --space-3:    0.75rem;
  --space-4:    1rem;
  --space-5:    1.25rem;
  --space-6:    1.5rem;
  --space-8:    2rem;
  --space-10:   2.5rem;
  --space-12:   3rem;
  --space-16:   4rem;
  --space-20:   5rem;
  --space-24:   6rem;
  --space-32:   8rem;

  /* Border radius */
  --radius-none: 0;
  --radius-sm:   0.25rem;
  --radius-md:   0.375rem;
  --radius-lg:   0.5rem;
  --radius-xl:   0.75rem;
  --radius-2xl:  1rem;
  --radius-3xl:  1.5rem;
  --radius-full: 9999px;

  /* Shadow */
  --shadow-sm:   0 1px 2px 0 rgb(0 0 0 / 0.05);
  --shadow-md:   0 4px 6px -1px rgb(0 0 0 / 0.1), 0 2px 4px -2px rgb(0 0 0 / 0.1);
  --shadow-lg:   0 10px 15px -3px rgb(0 0 0 / 0.1), 0 4px 6px -4px rgb(0 0 0 / 0.1);
  --shadow-xl:   0 20px 25px -5px rgb(0 0 0 / 0.1), 0 8px 10px -6px rgb(0 0 0 / 0.1);
  --shadow-2xl:  0 25px 50px -12px rgb(0 0 0 / 0.25);
  --shadow-none: none;

  /* Z-index */
  --z-base:     0;
  --z-raised:   10;
  --z-dropdown: 100;
  --z-sticky:   200;
  --z-overlay:  300;
  --z-modal:    400;
  --z-toast:    500;
  --z-tooltip:  600;

  /* Motion */
  --duration-instant: 50ms;
  --duration-fast:    100ms;
  --duration-normal:  200ms;
  --duration-slow:    300ms;
  --duration-slower:  500ms;

  --ease-default: cubic-bezier(0.4, 0, 0.2, 1);
  --ease-in:      cubic-bezier(0.4, 0, 1, 1);
  --ease-out:     cubic-bezier(0, 0, 0.2, 1);
  --ease-spring:  cubic-bezier(0.175, 0.885, 0.32, 1.275);
}

/* Dark mode token overrides */
@media (prefers-color-scheme: dark) {
  :root {
    --color-surface-base:     var(--color-neutral-950);
    --color-surface-elevated: var(--color-neutral-900);
    --color-text-primary:     var(--color-neutral-50);
    --color-text-muted:       var(--color-neutral-400);
    --color-border-default:   var(--color-neutral-700);
  }
}

/* Reduced motion */
@media (prefers-reduced-motion: reduce) {
  :root {
    --duration-instant: 0ms;
    --duration-fast:    0ms;
    --duration-normal:  0ms;
    --duration-slow:    0ms;
    --duration-slower:  0ms;
  }
}
```

---

## ARIA Color Compliance

For every color pair used in the design, compute and report:

| Pair                      | Foreground  | Background  | Ratio  | AA Normal | AA Large | AAA Normal | AAA Large |
|---------------------------|-------------|-------------|--------|-----------|----------|------------|-----------|
| Body text on surface      | #<fg>       | #<bg>       | N.N:1  | ✅/❌      | ✅/❌    | ✅/❌       | ✅/❌     |
| CTA button label          | #<fg>       | #<bg>       | N.N:1  | ✅/❌      | ✅/❌    | ✅/❌       | ✅/❌     |
| Muted text on surface     | #<fg>       | #<bg>       | N.N:1  | ✅/❌      | ✅/❌    | ✅/❌       | ✅/❌     |
| Status error on surface   | #<fg>       | #<bg>       | N.N:1  | ✅/❌      | ✅/❌    | ✅/❌       | ✅/❌     |

**Minimum requirements:** AA Normal (4.5:1) for all body text; AA Large (3:1) for headings and UI
components ≥ 18pt or 14pt bold. Flag anything below AA. Suggest accessible alternatives.

**WCAG 2.1 Relative Luminance formula:**
```
L = 0.2126 × R_lin + 0.7152 × G_lin + 0.0722 × B_lin
  where X_lin = (X/255)^2.2  (simplified sRGB linearisation)
Contrast ratio = (L_lighter + 0.05) / (L_darker + 0.05)
```

---

## Component Directory Scaffold

After generating mockups, propose a directory structure tuned to the detected (or specified) stack.
Default to framework-agnostic Web Components if no stack is given.

### React / Next.js
```
src/
  design-system/
    tokens/
      tokens.json          ← source of truth
      tokens.css           ← compiled CSS custom props
      tokens.ts            ← typed JS exports (const colors = {...})
    components/
      primitives/          ← Button, Input, Badge, Avatar, Icon
      layout/              ← Container, Grid, Stack, Divider
      navigation/          ← Navbar, Sidebar, Breadcrumb, Tabs
      feedback/            ← Toast, Alert, Modal, Skeleton
      data-display/        ← Card, Table, List, Stat
      forms/               ← Form, Field, Select, Checkbox, Radio
      media/               ← Image, Video, AspectRatio
    mockups/
      xs/                  ← ASCII frames per breakpoint
      sm/
      md/
      lg/
      xl/
      CHANGELOG.md         ← semantic version history of mockups
      VERSION              ← current version string
```

### Vue / Nuxt
```
src/
  design-system/
    tokens/ ...            ← same as above
    components/
      base/                ← BaseButton, BaseInput …
      layout/
      navigation/
      feedback/
      display/
      forms/
    mockups/ ...
```

### HTML / Vanilla / Web Components
```
design-system/
  tokens/
  components/
    buttons/
    cards/
    navigation/
    forms/
    layout/
  mockups/
```

---

## Versioning Protocol

Every time mockups are regenerated or tokens are changed:

1. Bump `VERSION` using SemVer:
   - **Patch** (x.x.N): annotation-only text changes
   - **Minor** (x.N.0): layout changes within existing components
   - **Major** (N.0.0): breakpoint additions, token schema changes, new sections
2. Append to `mockups/CHANGELOG.md`:

```markdown
## [1.2.0] — 2026-03-26

### Changed
- Hero section: added secondary CTA button across all breakpoints
- Token: `--color-brand-primary` updated from #2563eb → #1d4ed8

### Added
- `xl` (UWHD) breakpoint frame

### Fixed
- xs nav: hamburger touch target increased to 44px minimum
```

3. Include `<!-- mockup-version: 1.2.0 -->` as the first comment in every emitted HTML file.

---

## User-Agent Responsive Behavior

When generating HTML output (or CSS media queries), account for user-agent capabilities:

```css
/* Touch device — enlarge tap targets */
@media (pointer: coarse) {
  --min-tap-target: 44px;
}

/* Fine pointer (desktop mouse) */
@media (pointer: fine) {
  --min-tap-target: 24px;
}

/* High-DPI screens */
@media (-webkit-min-device-pixel-ratio: 2), (min-resolution: 192dpi) {
  /* Serve @2x assets via srcset; no hardcoded background-image URLs */
}

/* Print */
@media print {
  --color-surface-base:   #ffffff;
  --color-text-primary:   #000000;
  --shadow-md: none;
}
```

Explicitly call out UA-specific behaviors in annotations (e.g., iOS safe-area insets
`env(safe-area-inset-*)`, Android chrome notch handling).

---

## Performance Checklist

Embed this block in every HTML artifact generated:

```html
<!-- PERFORMANCE — ascii-mockup-skill -->
<!-- 1. FONTS: Google Fonts via CDN with display=swap (zero FOIT) -->
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=<params>&display=swap">

<!-- 2. TOKENS CSS: single file, cache-friendly, zero hardcoded values -->
<link rel="stylesheet" href="/design-system/tokens/tokens.css">

<!-- 3. IMAGES: lazy-load below fold, eager above fold -->
<!-- <img loading="lazy" decoding="async" src="…" width="…" height="…" alt="…"> -->

<!-- 4. ICONS: inline SVG sprite or icon font via CDN (e.g., Phosphor, Lucide) -->
<!-- <script src="https://unpkg.com/phosphor-icons"></script> -->

<!-- 5. CRITICAL CSS: inline above-the-fold token subset in <style> tag -->
<!-- 6. No render-blocking scripts — defer/async all JS -->
```

---

## Skill Chain Workflow

This skill integrates with:

### → ux-journey-mapper
After generating mockups, invoke the `ux-journey-mapper` skill to:
- Map each mockup screen to a journey stage (awareness → onboarding → retention)
- Tag touchpoints with the ASCII component references
- Export `.journey.md` + Mermaid swimlane auto-annotated with mockup version

### → frontend-design
After token and mockup approval, invoke `frontend-design` to:
- Receive `tokens.json` as the aesthetic foundation
- Build production HTML/CSS/JS using `tokens.css` custom properties
- Apply all ARIA color pairs from the compliance table
- Wire all breakpoints using the verified CSS variables

### → theme-factory
Optionally hand off `tokens.json` to `theme-factory` to apply the palette across slides or docs.

### Invocation hint
```
Step 1: ascii-mockup  → wireframes + tokens
Step 2: ux-journey-mapper → journey map overlaid on mockup screens
Step 3: frontend-design → production code using the token stylesheet
```

---

## Workflow — Step by Step

When this skill is invoked:

1. **Gather context** — ask for (or infer from conversation):
   - Project name and purpose
   - Target audience / primary personas
   - Preferred stack (React, Vue, HTML, etc.)
   - Brand seed colors (or generate a compliant palette)
   - Font preferences (or recommend from Google Fonts)
   - Which screens / flows to wireframe

2. **Author ARIA palette** — pick 3–5 brand colors, compute all contrast ratios,
   flag failures, suggest alternatives until all pairs are AA compliant.

3. **Emit `tokens.json`** — fill every token category with the chosen palette,
   typography, spacing, motion values.

4. **Emit `tokens.css`** — compiled from `tokens.json`, Google Fonts `@import` at top.

5. **Generate ASCII mockups** — render all 5 breakpoints, mobile-first (xs first).
   Annotate every element with its token reference.

6. **Propose component directory** — list each ASCII element as a named component
   with its directory path and reuse scope.

7. **Write CHANGELOG entry** — bump version, record what changed.

8. **Offer skill-chain** — ask user if they want to continue with
   `ux-journey-mapper` → `frontend-design`.

---

## Quality Gates

Before finalizing output, verify:

- [ ] All 5 breakpoints rendered (xs → xl)
- [ ] Every color pair in the palette has a computed contrast ratio
- [ ] No hardcoded hex/px/rem values in `tokens.css` (only `var(--*)` references after `:root`)
- [ ] Google Fonts `@import` present with `display=swap`
- [ ] Each ASCII element annotated with its token name
- [ ] `CHANGELOG.md` entry written
- [ ] `VERSION` file contains current SemVer string
- [ ] Component directory scaffold provided
- [ ] Performance checklist block included in any HTML output
- [ ] `prefers-color-scheme: dark` override block in `tokens.css`
- [ ] `prefers-reduced-motion` block in `tokens.css`

---

## Design Feedback Protocol

If the user's request has gaps or anti-patterns, provide brief feedback:

- **Inaccessible colors**: "Your requested `#ff0` on `#fff` is 1.07:1 — fails all WCAG levels. Suggest `#7a7a00` (8.5:1 on white) for body, `#ffdd00` on `#1a1a00` for display use."
- **Missing mobile consideration**: "No xs breakpoint specified — adding mobile-first as it covers 60%+ of web traffic."
- **Hardcoded fonts**: "Avoid embedding fonts as local files — Google Fonts CDN reduces load time and benefits from shared browser caching."
- **Touch target too small**: "Buttons at 32px fail WCAG 2.5.5 (Target Size) on touch devices — minimum 44×44px recommended."
- **Single breakpoint request**: "Designing only for desktop leaves ~50% of users underserved — generating all 5 breakpoints for a complete responsive system."
