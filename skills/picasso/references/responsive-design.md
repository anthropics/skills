# Responsive Design Reference

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

## 4. Container Queries

For component-level responsiveness (when the component's width, not the viewport, should determine layout):

```css
.card-container {
  container-type: inline-size;
}
@container (min-width: 400px) {
  .card { display: grid; grid-template-columns: 1fr 2fr; }
}
```

## 5. Touch Targets

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

## 6. Responsive Typography

Do not just shrink everything on mobile. Adjust the type scale:
- Mobile: use a smaller ratio (1.2) with a 15-16px base
- Desktop: use a larger ratio (1.25-1.333) with a 16-18px base
- Headings should scale more aggressively than body text

## 7. Navigation Patterns

- **Mobile (< 768px)**: Hamburger menu, bottom tab bar, or slide-out drawer
- **Tablet (768-1024px)**: Collapsed sidebar or icon-only navigation
- **Desktop (> 1024px)**: Full sidebar, top navigation bar, or mega-menu

## 8. Images

Use `srcset` and `sizes` for responsive images. Use `loading="lazy"` for below-the-fold images. Set `aspect-ratio` to prevent layout shift:

```css
img {
  width: 100%;
  height: auto;
  aspect-ratio: 16 / 9;
  object-fit: cover;
}
```

## 9. Common Mistakes

- Hiding too much content on mobile (users expect the same information, just reorganized)
- Using `vw` units for text without a `clamp()` minimum (becomes unreadable on small screens)
- Horizontal scrolling on mobile (almost never acceptable)
- Fixed-position elements that cover too much of the mobile viewport
- Not testing at actual device widths (375px for iPhone SE, 390px for modern iPhones, 360px for Android)
- Tables that overflow on mobile (use horizontal scroll wrapper or reformat as stacked cards)
