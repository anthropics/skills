---
name: wordpress-generateblocks
description: Guide for building WordPress sites with GeneratePress theme and GenerateBlocks Pro. This skill should be used when creating full-width sections, hero layouts, responsive grids, or any page building with GenerateBlocks. Covers the critical two-layer architecture (gbp-section + gbp-section__inner), block parser requirements, Docker development, and WP-CLI operations.
license: MIT
---

# WordPress GenerateBlocks Development Guide

## Overview

This skill provides comprehensive guidance for building professional WordPress sites using GeneratePress theme with GP Premium and GenerateBlocks Pro. It covers the essential patterns, architecture decisions, and workflows needed for efficient development.

## Quick Reference

| Component | Version |
|-----------|---------|
| GeneratePress | 3.6.0 |
| GP Premium | 2.5.5 |
| GenerateBlocks | 2.1.2+ |
| GenerateBlocks Pro | 2.4.0+ |
| WordPress | 6.6+ |

## When to Use This Skill

- Creating full-width sections with colored backgrounds
- Building hero sections, feature grids, or stats displays
- Working with GenerateBlocks Element, Text, Media, or Query blocks
- Setting up WordPress Docker development environments
- Managing content via WP-CLI
- Debugging CSS layout issues in GeneratePress sites

## Critical Architecture: Full-Width Sections

**ALWAYS use the two-layer architecture for full-width sections:**

```html
<!-- Outer: Full-width background (breaks out of container) -->
<section class="gbp-section gb-element-hero001">
  <!-- Inner: Centered content (1280px max-width) -->
  <div class="gbp-section__inner gb-element-hero002">
    <!-- Content here -->
  </div>
</section>
```

### Required CSS

```css
.gbp-section {
  max-width: none !important;
  width: 100vw !important;
  margin-left: calc(50% - 50vw) !important;
  margin-right: calc(50% - 50vw) !important;
}

.gbp-section__inner {
  max-width: 1280px !important;
  margin: 0 auto !important;
  padding: 0 1.5rem !important;
}
```

### Required Page Meta

```bash
wp post meta update PAGE_ID _generate-full-width-content true --allow-root
wp post meta update PAGE_ID _generate-sidebar-layout-meta no-sidebar --allow-root
```

## Block Parser Requirement

**CRITICAL**: GenerateBlocks generates CSS at save time, not render time.

- Saving via WordPress Editor triggers the Gutenberg parser and generates CSS
- WP-CLI `wp post update --post_content` does NOT trigger the parser

**After WP-CLI content updates:**
1. Open the page in WordPress editor
2. Click "Update" button
3. This triggers CSS generation

**Workaround**: Always provide fallback CSS in your child theme's style.css.

## Core Blocks Reference

### Element (Container)
The foundational block for layouts. Replaces legacy Container block.

**Available Tags**: `section`, `article`, `aside`, `header`, `footer`, `nav`, `main`, `figure`, `div`, `span`, `ul`, `ol`, `li`, `a`

**Key Pattern**:
```javascript
{
  uniqueId: "hero001",
  tagName: "section",
  styles: {
    backgroundColor: "#f0fdf4",
    paddingTop: "4rem",
    paddingBottom: "4rem"
  },
  globalClasses: ["gbp-section"]
}
```

### Text
Rich text with typography control.

**Available Tags**: `p`, `h1`-`h6`, `a`, `button`, `span`, `div`, `figcaption`, `li`

### Media
Optimized images with link support and aspect ratio control.

### Query
Dynamic post loops using WP_Query parameters.

## Common Patterns

### Responsive Grid (No Media Queries)
```css
.grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
  gap: 2rem;
}
```

### Video 16:9 Container
```css
.video-container {
  position: relative;
  padding-bottom: 56.25%;
  height: 0;
}
.video-container iframe {
  position: absolute;
  top: 0; left: 0;
  width: 100%; height: 100%;
}
```

### 2/3 + 1/3 Layout
```css
.content-layout {
  display: grid;
  grid-template-columns: 2fr 1fr;
  gap: 3rem;
}
@media (max-width: 1024px) {
  .content-layout { grid-template-columns: 1fr; }
}
```

## Dynamic Content Tags

| Tag | Output |
|-----|--------|
| `{{ post:title }}` | Post title |
| `{{ post:excerpt }}` | Post excerpt |
| `{{ post:featured-image }}` | Featured image |
| `{{ post:date }}` | Publish date |
| `{{ post:permalink }}` | Post URL |
| `{{ post:terms }}` | Categories/tags |

## Responsive Breakpoints

| Device | Breakpoint | GenerateBlocks Suffix |
|--------|------------|----------------------|
| Mobile | < 768px | `fontSizeMobile`, `paddingMobile` |
| Tablet | 768-1024px | `fontSizeTablet`, `paddingTablet` |
| Desktop | > 1024px | Default values |

## Color Variables (GeneratePress)

```css
--contrast: #222222      /* Main text */
--contrast-2: #575760    /* Secondary text */
--base: #f0f0f0          /* Light backgrounds */
--base-3: #ffffff        /* White */
--accent: #1e73be        /* Primary color */
```

## Troubleshooting

### Sections Not Full Width
1. Check page meta: `_generate-full-width-content` = `true`
2. Verify two-layer structure (outer gbp-section + inner gbp-section__inner)
3. Add fallback CSS with `!important`

### Styles Not Applying After WP-CLI
Open page in WordPress editor and click "Update" to trigger block parser.

### Video Breaking Container
Apply 16:9 aspect ratio pattern (padding-bottom: 56.25%).

## Reference Files

For detailed information, load these reference files as needed:

- **[generateblocks.md](./reference/generateblocks.md)** - Complete blocks documentation, GP Premium modules, patterns
- **[patterns-library.md](./reference/patterns-library.md)** - Production-ready code patterns with full HTML
- **[wordpress-docker.md](./reference/wordpress-docker.md)** - Docker container management commands
- **[wp-cli.md](./reference/wp-cli.md)** - WordPress CLI operations reference
- **[css-debugging.md](./reference/css-debugging.md)** - Browser DevTools debugging guide
