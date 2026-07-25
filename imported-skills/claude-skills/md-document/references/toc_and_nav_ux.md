# Table-of-Contents and Navigation UX

**Why this exists:** The TOC is the single highest-leverage navigation aid in a long document. The design-system config offers four behaviors (`sticky-sidebar`, `collapsible-top`, `inline`, `none`); this document explains when each is right and what UX patterns the renderer implements.

## The four TOC variants

| Behavior | Use when | Renderer detail |
|---|---|---|
| **`sticky-sidebar`** (default) | Document > 800 words / 4+ H2 sections; landscape reading on desktop | Two-column CSS grid; nav is `position: sticky; top: 1.5rem`; collapses to top-of-page on viewports < 800px via media query |
| **`collapsible-top`** | Document ≤ 800 words but with > 3 sections; mobile-first | `<details open>` at top of document; user can collapse to recover vertical space |
| **`inline`** | Document is its own TOC (the bullet list at top IS the navigation) | TOC nav is suppressed; the markdown's own list serves the purpose |
| **`none`** | Short documents, focused single-section pieces | No TOC rendered at all |

Default is `sticky-sidebar` because the median document this converter sees is a multi-section spec or RFC, and the sidebar serves both as TOC and as "you are here" indicator (via scrollspy).

## Scrollspy implementation

`interactivity_injector.py` uses `IntersectionObserver` with this rootMargin:

```js
{ rootMargin: "-20% 0px -70% 0px", threshold: 0 }
```

A heading is considered "current" only when it's in the **upper-middle** of the viewport (between 20% from top and 30% from top). This matches the F-shape reading pattern (Nielsen/NN-g): users fixate on text just below the fold-line, not at the very top.

When the observer fires, the matching TOC link gets `aria-current="location"`. CSS then highlights it via:

```css
nav.toc a[aria-current="location"] {
    color: var(--md-accent);
    font-weight: 600;
    background: var(--md-accent-soft);
}
```

Both the attribute and the visual highlight are semantic — screen readers announce "current location" without us needing an extra ARIA-live region.

## Search-as-filter (not search-as-jump)

The search bar filters which H2 sections are visible. It does NOT scroll-to-match the way GitHub's `?text=foo` URL does. Reason: in a filtered view, the reader can see the structure of what survives the filter (which sections matched). A jump-to-first-match loses that structural information.

Esc clears the filter. Sticky positioning ensures the search bar stays visible during scroll.

## Sources

### 1. Jakob Nielsen / NN/g — *Table of Contents Best Practices* (2023)
The canonical reference. Establishes:
- TOC should appear at the top OR persist sticky (not just mid-document)
- Anchored links should scroll, not full-page navigate
- Current-location indication is required for documents over ~1000 words
- Depth cap at H3 (max_depth=3 default) is a usability finding — deeper hierarchies become noise

### 2. WCAG 2.2 — *Success Criterion 2.4.5: Multiple Ways* (w3.org/WAI/WCAG22)
Mandates that long pages provide more than one way to find content. The TOC + scrollspy + search trio satisfies this for any single document.

### 3. ARIA Authoring Practices — *aria-current attribute* (w3.org/WAI/ARIA/apg/practices/feedback/)
Documents the `aria-current="location"` pattern as the standard for "current page/section" indication. Screen readers (NVDA, JAWS, VoiceOver) announce it appropriately.

### 4. Vitepress / Docusaurus / mdBook — sticky-sidebar TOC implementations
All three of these documentation systems converged on the sticky-sidebar pattern as the right default for technical documents. We mirror their behavior (left or right column, sticky-positioned, scrollspy-enabled) rather than reinventing it.

### 5. GOV.UK Design System — *Inline navigation* (design-system.service.gov.uk)
For shorter pages, GOV.UK uses an inline anchor list rather than a sidebar. Validates the `inline` and `collapsible-top` behaviors as legitimate alternatives for shorter documents.

### 6. MDN Web Docs — *IntersectionObserver API* (developer.mozilla.org)
The browser primitive that makes scrollspy possible without scroll-event throttling. Available since 2017, ~95% browser support today.

## Applied to `md-document`

The renderer emits the right nav variant based on `toc.behavior`. The injector wires up scrollspy + search behavior. Every section heading H2-H{max_depth+1} gets an anchor + TOC entry; H1 is the document title (not navigation).
