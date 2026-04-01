# Spatial Design Reference

## Table of Contents
1. Spacing Scale
2. Grid Systems
3. Visual Hierarchy
4. Whitespace
5. Layout Patterns
6. Common Mistakes

---

## 1. Spacing Scale

Use a consistent spacing scale based on a 4px unit. Never use arbitrary values like 13px or 7px.

```css
:root {
  --space-1: 0.25rem;   /* 4px  - tight inline gaps */
  --space-2: 0.5rem;    /* 8px  - icon-to-text, compact lists */
  --space-3: 0.75rem;   /* 12px - form field padding */
  --space-4: 1rem;      /* 16px - standard element spacing */
  --space-5: 1.25rem;   /* 20px - card padding */
  --space-6: 1.5rem;    /* 24px - section padding */
  --space-8: 2rem;      /* 32px - group separation */
  --space-10: 2.5rem;   /* 40px - major section gaps */
  --space-12: 3rem;     /* 48px - large section spacing */
  --space-16: 4rem;     /* 64px - page-level spacing */
  --space-20: 5rem;     /* 80px - hero-level breathing room */
  --space-24: 6rem;     /* 96px - dramatic separation */
}
```

### When to Use Which Size
- **1-2 (4-8px)**: Internal component spacing (icon + label, badge padding)
- **3-4 (12-16px)**: Component padding, list item spacing
- **5-6 (20-24px)**: Card padding, form group margins
- **8-10 (32-40px)**: Section separation within a page
- **12-16 (48-64px)**: Major content blocks, above/below fold
- **20-24 (80-96px)**: Hero areas, page-level breathing room

---

## 2. Grid Systems

### CSS Grid Defaults
```css
.grid {
  display: grid;
  grid-template-columns: repeat(auto-fill, minmax(280px, 1fr));
  gap: var(--space-6);
}
```

### 12-Column Grid
For dashboard and editorial layouts:
```css
.page-grid {
  display: grid;
  grid-template-columns: repeat(12, 1fr);
  gap: var(--space-6);
  max-width: 1200px;
  margin: 0 auto;
  padding: 0 var(--space-6);
}
```

### Asymmetric Grids
For editorial and portfolio layouts, break the 12-column grid:
```css
.editorial-grid {
  display: grid;
  grid-template-columns: 2fr 1fr;  /* 2:1 ratio */
  gap: var(--space-8);
}
.portfolio-grid {
  display: grid;
  grid-template-columns: 3fr 2fr;  /* golden-ish ratio */
  gap: var(--space-6);
}
```

---

## 3. Visual Hierarchy

Hierarchy is established through size, weight, color, and space. Not all four at once. Pick two.

### Hierarchy Techniques (in order of strength)
1. **Size difference**: The fastest way to establish priority
2. **Weight difference**: Bold vs. regular within the same size
3. **Color contrast**: Primary vs. secondary text color
4. **Spatial separation**: More space around important elements
5. **Position**: Top-left gets seen first (in LTR languages)

### Rules
- If everything is bold, nothing is bold. Limit bold to headings and key data points.
- If everything is the same size, the eye has nowhere to land. Vary size by at least 1.5x between hierarchy levels.
- Use secondary/tertiary text colors for supporting information (timestamps, metadata, helper text).
- Reduce visual weight of labels and increase weight of values in data-heavy UIs.

---

## 4. Whitespace

Whitespace is not wasted space. It is a design element.

### Internal vs. External Spacing
- **Internal**: Padding inside a component (card padding, button padding). Relates to the component's own content.
- **External**: Margin between components. Relates to the component's relationship with siblings.

### Gestalt Grouping
Elements that are closer together are perceived as related. Use tighter spacing within groups and wider spacing between groups. The ratio between intra-group and inter-group spacing should be at least 2:1 (e.g., 8px within, 24px between).

### Generous vs. Dense
- **Generous**: Marketing pages, portfolios, editorial content. Use 80-120px between major sections.
- **Dense**: Dashboards, admin panels, data tables. Use 16-32px between sections but maintain consistent rhythm.

---

## 5. Layout Patterns

### Centered Content
Max-width container with auto margins. Standard max-widths: 640px (narrow/reading), 960px (medium), 1200px (wide), 1440px (ultrawide).

### Sidebar + Main
```css
.layout {
  display: grid;
  grid-template-columns: 260px 1fr;
  min-height: 100vh;
}
```

### Sticky Header + Scrollable Content
```css
.header { position: sticky; top: 0; z-index: 10; }
.main { overflow-y: auto; }
```

### Bento Grid
Irregular grid with varied cell sizes:
```css
.bento {
  display: grid;
  grid-template-columns: repeat(4, 1fr);
  grid-auto-rows: 200px;
  gap: var(--space-4);
}
.bento .featured {
  grid-column: span 2;
  grid-row: span 2;
}
```

### Overlap/Layer
Elements that break out of the grid create visual tension:
```css
.overlap-element {
  position: relative;
  z-index: 2;
  margin-top: -3rem;  /* pulls up into previous section */
}
```

---

## 6. Common Mistakes

- Using inconsistent spacing values (17px here, 23px there)
- Centering everything on the page (creates a vertical highway with no anchor points)
- Not using max-width on content (text that spans 1400px is unreadable)
- Applying the same padding to all components regardless of their content
- Putting too many items in a row on mobile (three columns at 375px is almost never right)
- Using margin-top and margin-bottom on the same element (pick one direction, usually bottom, and stick with it throughout the project)
- Neglecting the space between the last element and the container edge
