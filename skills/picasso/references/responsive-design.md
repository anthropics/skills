# Responsive Design Reference

## Table of Contents
1. Breakpoints
2. Mobile-First Approach
3. Fluid Design
4. Dynamic Viewport Units
5. Container Queries
6. Touch Targets
7. Responsive Typography
8. Navigation Patterns
9. Images
10. Responsive Tables
11. Print Styles
12. Progressive Enhancement
13. Landscape and Orientation
14. Common Mistakes

---

## 1. Breakpoints

Use content-driven breakpoints, not device-driven. These are sensible defaults:

```css
/* Mobile first: no media query = mobile */
/* Small tablets / large phones */
@media (min-width: 640px) { }
/* Tablets / small laptops */
@media (min-width: 768px) { }
/* Laptops / desktops */
@media (min-width: 1024px) { }
/* Large desktops */
@media (min-width: 1280px) { }
/* Ultrawide */
@media (min-width: 1536px) { }
```

When a layout breaks before reaching a named breakpoint, add a custom one. The content dictates the breakpoint, not the other way around. Avoid more than five or six breakpoints total.

## 2. Mobile-First Approach

Start with the mobile layout (single column, stacked). Add complexity at wider breakpoints. This ensures the core experience works everywhere before enhancements.

```css
/* Base: single column */
.grid { display: grid; gap: 1rem; }

/* Tablet: two columns */
@media (min-width: 768px) {
  .grid { grid-template-columns: repeat(2, 1fr); }
}

/* Desktop: three columns */
@media (min-width: 1024px) {
  .grid { grid-template-columns: repeat(3, 1fr); }
}
```

## 3. Fluid Design

Use `clamp()` for font sizes, padding, and gaps that scale smoothly:

```css
.container {
  padding: clamp(1rem, 4vw, 3rem);
  max-width: 1200px;
  margin: 0 auto;
}
h1 {
  font-size: clamp(1.75rem, 4vw + 0.5rem, 3.5rem);
}
```

For spacing systems, combine `clamp()` with CSS custom properties so every spacing token scales together:

```css
:root {
  --space-s: clamp(0.5rem, 1.5vw, 0.75rem);
  --space-m: clamp(1rem, 3vw, 1.5rem);
  --space-l: clamp(1.5rem, 5vw, 3rem);
}
```

## 4. Dynamic Viewport Units

The classic `vh` unit does not account for browser chrome (address bar, toolbar) on mobile devices. This causes content to be hidden behind the UI. Use the newer viewport units instead:

| Unit | Meaning | Use when |
|------|---------|----------|
| `svh` | Small viewport height (browser chrome fully visible) | You want the smallest guaranteed visible area |
| `lvh` | Large viewport height (browser chrome hidden) | You want the largest possible area |
| `dvh` | Dynamic viewport height (updates live as chrome shows/hides) | You want the hero or section to always fill exactly the visible area |
| `dvw` | Dynamic viewport width | Rare, but useful for side-panel layouts on mobile browsers with edge UI |

```css
/* Full-screen hero that actually fills the screen on mobile */
.hero {
  min-height: 100dvh;
  display: grid;
  place-items: center;
}

/* Sticky footer layout that respects mobile browser chrome */
.app-shell {
  display: grid;
  grid-template-rows: auto 1fr auto;
  min-height: 100dvh;
}

/* Fallback for older browsers */
.hero {
  min-height: 100vh;
  min-height: 100dvh;
}
```

Always declare a `vh` fallback before the `dvh` value. Browser support is strong (2023+), but the fallback costs nothing.

## 5. Container Queries

For component-level responsiveness (when the component's width, not the viewport, should determine layout). This is essential for reusable components that live in different layout contexts (main content area, sidebar, modal, dashboard grid).

### Card that adapts to its container

```css
.card-container {
  container-type: inline-size;
  container-name: card;
}

/* Compact: image on top, content below */
.card {
  display: grid;
  gap: 0.75rem;
}
.card img {
  width: 100%;
  aspect-ratio: 16 / 9;
  object-fit: cover;
}

/* Wide enough: image beside content */
@container card (min-width: 400px) {
  .card {
    grid-template-columns: 200px 1fr;
  }
  .card img {
    aspect-ratio: 1;
    height: 100%;
  }
}

/* Very wide: add metadata column */
@container card (min-width: 700px) {
  .card {
    grid-template-columns: 240px 1fr 180px;
  }
}
```

### Sidebar-aware layout

```css
.main-content { container-type: inline-size; }

@container (min-width: 600px) {
  .dashboard-grid {
    grid-template-columns: repeat(2, 1fr);
  }
}
@container (min-width: 900px) {
  .dashboard-grid {
    grid-template-columns: repeat(3, 1fr);
  }
}
```

This means when the sidebar is open and the main area shrinks, the grid automatically drops columns without any viewport media query.

## 6. Touch Targets

Minimum touch target: 44x44px (WCAG) or 48x48px (Material). Apply to all interactive elements on mobile. If the visual element is smaller, use padding or `::before` pseudo-element to extend the hit area.

```css
.icon-button {
  position: relative;
  width: 24px;
  height: 24px;
}
.icon-button::before {
  content: '';
  position: absolute;
  inset: -12px; /* extends tap area to 48x48 */
}
```

Also ensure at least 8px of space between adjacent touch targets to prevent mis-taps.

## 7. Responsive Typography

Do not just shrink everything on mobile. Adjust the type scale:
- Mobile: use a smaller ratio (1.2) with a 15-16px base
- Desktop: use a larger ratio (1.25-1.333) with a 16-18px base
- Headings should scale more aggressively than body text

## 8. Navigation Patterns

- **Mobile (< 768px)**: Hamburger menu, bottom tab bar, or slide-out drawer
- **Tablet (768-1024px)**: Collapsed sidebar or icon-only navigation
- **Desktop (> 1024px)**: Full sidebar, top navigation bar, or mega-menu

## 9. Images

Use `srcset` and `sizes` for responsive images. Use `loading="lazy"` for below-the-fold images. Set `aspect-ratio` to prevent layout shift:

```css
img {
  width: 100%;
  height: auto;
  aspect-ratio: 16 / 9;
  object-fit: cover;
}
```

## 10. Responsive Tables

Tables are one of the hardest elements to make responsive. Two proven patterns:

### Pattern A: Horizontal scroll wrapper

Keeps the table structure intact. Best for data-dense tables where column relationships matter (financial data, comparison grids).

```css
.table-wrapper {
  overflow-x: auto;
  -webkit-overflow-scrolling: touch;
  border: 1px solid var(--border);
  border-radius: 0.5rem;
}
.table-wrapper table {
  min-width: 600px; /* prevents columns from crushing */
  width: 100%;
  border-collapse: collapse;
}

/* Visual hint that the table scrolls */
.table-wrapper {
  background:
    linear-gradient(to right, white 30%, transparent),
    linear-gradient(to left, white 30%, transparent),
    linear-gradient(to right, rgba(0,0,0,0.1), transparent 15px),
    linear-gradient(to left, rgba(0,0,0,0.1), transparent 15px);
  background-position: left, right, left, right;
  background-size: 40px 100%, 40px 100%, 15px 100%, 15px 100%;
  background-repeat: no-repeat;
  background-attachment: local, local, scroll, scroll;
}
```

### Pattern B: Stacked cards on mobile

Reformats each row into a standalone card. Best for user-facing lists (orders, contacts, transactions) where each row is an independent record.

```css
@media (max-width: 767px) {
  table, thead, tbody, th, td, tr {
    display: block;
  }
  thead {
    position: absolute;
    width: 1px;
    height: 1px;
    overflow: hidden;
    clip: rect(0, 0, 0, 0);
  }
  tr {
    margin-bottom: 1rem;
    border: 1px solid var(--border);
    border-radius: 0.5rem;
    padding: 0.75rem;
  }
  td {
    display: flex;
    justify-content: space-between;
    padding: 0.4rem 0;
    border-bottom: 1px solid var(--border-light);
  }
  td:last-child {
    border-bottom: none;
  }
  /* Use data attributes for labels */
  td::before {
    content: attr(data-label);
    font-weight: 600;
    margin-right: 1rem;
    flex-shrink: 0;
  }
}
```

The HTML needs `data-label` attributes on each `<td>`:

```html
<td data-label="Name">Alice Johnson</td>
<td data-label="Status">Active</td>
<td data-label="Amount">$1,240.00</td>
```

## 11. Print Styles

Always include basic print styles for pages with substantive content (articles, invoices, dashboards, reports):

```css
@media print {
  /* Remove non-essential UI */
  nav, .sidebar, .toolbar, footer, .no-print {
    display: none !important;
  }

  /* Reset backgrounds and colors for ink saving */
  body {
    background: white !important;
    color: black !important;
    font-size: 12pt;
    line-height: 1.5;
  }

  /* Prevent elements from breaking across pages */
  h1, h2, h3 {
    break-after: avoid;
  }
  table, figure, .card {
    break-inside: avoid;
  }

  /* Show link URLs inline */
  a[href^="http"]::after {
    content: " (" attr(href) ")";
    font-size: 0.85em;
    color: #555;
  }

  /* Constrain width for readability */
  .container {
    max-width: 100% !important;
    padding: 0 !important;
  }
}
```

## 12. Progressive Enhancement

Use `@supports` to deliver modern layouts to capable browsers while keeping a usable fallback:

```css
/* Fallback: flexbox grid */
.grid {
  display: flex;
  flex-wrap: wrap;
  gap: 1rem;
}
.grid > * {
  flex: 1 1 300px;
}

/* Enhancement: subgrid for aligned cards */
@supports (grid-template-rows: subgrid) {
  .grid {
    display: grid;
    grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
  }
  .grid > .card {
    display: grid;
    grid-template-rows: subgrid;
    grid-row: span 3;
  }
}
```

Other useful `@supports` checks:

```css
/* Container queries */
@supports (container-type: inline-size) {
  .widget-wrapper { container-type: inline-size; }
}

/* Has selector for advanced targeting */
@supports selector(:has(*)) {
  .form-group:has(:invalid) { border-color: red; }
}

/* Backdrop filter for frosted glass */
@supports (backdrop-filter: blur(10px)) {
  .overlay {
    backdrop-filter: blur(10px);
    background: rgba(255, 255, 255, 0.6);
  }
}
```

## 13. Landscape and Orientation

Handle orientation changes explicitly, especially for mobile devices where landscape mode drastically changes available height:

```css
/* Landscape phones: reduce vertical spacing, switch to row layout */
@media (orientation: landscape) and (max-height: 500px) {
  .hero {
    min-height: auto;
    padding: 2rem 1rem;
  }
  .onboarding-steps {
    flex-direction: row;
    overflow-x: auto;
  }
}

/* Tablet landscape: often wide enough for desktop layout */
@media (orientation: landscape) and (min-width: 768px) {
  .sidebar { display: block; }
}
```

Key considerations:
- Landscape phones have very little vertical space (typically under 400px). Do not use full-height heroes or tall modals.
- Virtual keyboards consume even more vertical space in landscape. Keep form inputs above the fold or use a scroll strategy.
- Test with `(max-height: Xpx)` in addition to orientation queries for finer control.

## 14. Common Mistakes

- **Hiding content on mobile**: Users expect the same information, just reorganized. Use progressive disclosure (expand/collapse) instead of `display: none`.
- **Unguarded `vw` text**: Using `vw` units for text without a `clamp()` minimum makes text unreadable on small screens and comically large on ultrawide.
- **Horizontal overflow**: Almost never acceptable on mobile. Test at 320px wide to catch it. Common culprits: tables, pre/code blocks, fixed-width images, long URLs.
- **Fixed elements hogging the viewport**: A fixed header + fixed bottom bar + cookie banner can consume over half the screen on a short phone.
- **Not testing real device widths**: 375px (iPhone SE), 390px (modern iPhone), 360px (common Android), 320px (stress test).
- **Ignoring the notch and safe areas**: On devices with notches or rounded corners, use `env(safe-area-inset-*)` for edge-to-edge layouts:
  ```css
  .bottom-bar {
    padding-bottom: env(safe-area-inset-bottom, 0px);
  }
  ```
- **Breakpoint-only thinking**: If you find yourself writing more than three media queries for a single component, switch to container queries or fluid sizing.
- **Forgetting hover states are absent on touch**: Use `@media (hover: hover)` to scope hover effects so they do not get stuck on touch devices.
  ```css
  @media (hover: hover) {
    .card:hover { transform: translateY(-2px); }
  }
  ```
- **Z-index wars on mobile**: Stacking contexts behave differently when fixed/sticky elements overlap modals and drawers. Establish a z-index scale in custom properties.
- **Viewport-height layouts with virtual keyboards**: On mobile, the virtual keyboard does not shrink the viewport in all browsers. Elements pinned to `100vh` can end up hidden. Use `100dvh` or listen for `visualViewport` resize events.
