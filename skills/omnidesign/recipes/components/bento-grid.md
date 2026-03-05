# Bento Grid

A flexible, variable-size card grid layout inspired by bento box design. Supports mixed card dimensions (1×1, 2×1, 1×2, 2×2) with hover lift effects, focus states, and content variations.

## When to Use

**Use bento grids for:**
- Portfolio or case study showcases
- Feature highlights with visual variety
- Product gallery with mixed content types
- Dashboard layouts with different widget sizes
- Blog or article collections with featured posts

**Don't use for:**
- Data tables (use proper table semantics)
- Uniform card lists (use standard grid)
- Content requiring strict reading order
- Mobile-first experiences (complex layouts break on small screens)

## Component Anatomy

```
┌──────────────────────────────────────────────────────┐
│  [1×1 Card]  [2×1 Card - Featured]                  │
│              [Spans 2 columns]                       │
├──────────────────────────────────────────────────────┤
│  [1×2 Card]  [1×1 Card]  [1×1 Card]                 │
│  [Spans 2    [Standard]  [Standard]                 │
│   rows]                                              │
├──────────────────────────────────────────────────────┤
│             [2×2 Card - Hero]                        │
│             [Spans 2×2 grid]                         │
└──────────────────────────────────────────────────────┘
```

## State Matrix

| State | Visual Treatment | Tokens Used |
|-------|------------------|-------------|
| **Default** | Card at rest, subtle border, shadow.card applied | `color.surface.raised`, `shadow.card`, `radius.card` |
| **Hover** | Card lifts 4px (transform: translateY(-4px)), shadow deepens, opacity 100% | `motion.hover`, `shadow.card` (elevated) |
| **Focus** | Focus ring around card (2px, inset), keyboard navigation visible | `color.focus.ring`, `space.inlineSm` |
| **Active** | Card background slightly darkened, border color strengthened | `color.surface.sunken`, `color.border.strong` |
| **Disabled** | Opacity 50%, cursor not-allowed, no hover effect | `color.text.muted`, `motion.hover` (disabled) |

## Token Usage

### Colors
- **Card Background**: `color.surface.raised` for elevated appearance
- **Card Border**: `color.border.default` for subtle separation
- **Text**: `color.text.default` for headings, `color.text.muted` for descriptions
- **Overlay**: `color.surface.overlay` with 10% opacity for hover darkening

### Spacing
- **Card Padding**: `space.cardPadding` (6px) internal spacing
- **Grid Gap**: `space.cardGap` (4px) between cards
- **Content Stack**: `space.stackMd` (4px) between card title and description

### Typography
- **Card Title**: `typography.heading.card` (xl, semibold)
- **Card Description**: `typography.body.default` or `typography.body.small`
- **Card Meta**: `typography.ui.caption` for dates, tags, or metadata

### Shadows & Radii
- **Card Radius**: `radius.card` for rounded corners
- **Card Shadow**: `shadow.card` at rest, elevated shadow on hover
- **Focus Ring**: 2px inset ring with `color.focus.ring`

## Implementation Notes

### CSS/HTML Approach

**Structure:**
```
<div class="bento-grid">
  <article class="bento-card bento-card--1x1">
    <img src="..." alt="..." class="bento-card__image">
    <div class="bento-card__content">
      <h3 class="bento-card__title">Title</h3>
      <p class="bento-card__description">Description</p>
    </div>
  </article>
  
  <article class="bento-card bento-card--2x1">
    <!-- Featured card content -->
  </article>
  
  <!-- More cards... -->
</div>
```

**Key CSS patterns:**
- Use CSS Grid with `display: grid; grid-template-columns: repeat(4, 1fr)` (4-column base)
- Apply `grid-column: span 1/2/4` and `grid-row: span 1/2` for sizing variants
- Use `transition: all 200ms ease-out` for smooth hover effects
- Apply `transform: translateY(-4px)` on hover for lift effect
- Use `box-shadow` with `shadow.card` token for depth
- Implement focus ring with `outline: 2px solid color.focus.ring; outline-offset: 2px`

**Responsive grid:**
- Desktop (1024px+): 4-column grid with full size variations
- Tablet (768px): 2-column grid, reduce card sizes (1×1 only, no 2×2)
- Mobile (375px): 1-column grid, all cards 1×1, stack vertically

**Content variations:**
- Image-only cards: Full-height image with overlay text
- Text-only cards: Heading + description + optional CTA
- Mixed cards: Image + text side-by-side or stacked
- Interactive cards: Hover reveals additional content or CTA

### React Approach

**Component structure:**
- Create `<BentoGrid>` wrapper managing grid layout and responsive behavior
- Create `<BentoCard>` component accepting `size` prop (1x1, 2x1, 1x2, 2x2)
- Use `children` prop for flexible content (image, text, CTA, etc.)
- Implement `onHover` state for lift effect and shadow elevation
- Use CSS Grid with CSS-in-JS or Tailwind for responsive sizing

**State management:**
- Track hover state per card for visual feedback
- Use CSS `:hover` and `:focus-visible` for interactive states
- Implement `useCallback` for hover handlers to prevent unnecessary re-renders
- Consider `IntersectionObserver` for lazy-loading card images

**Responsive behavior:**
- Use `useMediaQuery` hook to detect breakpoints
- Adjust grid columns and card sizes based on viewport
- Stack cards vertically on mobile, maintain grid on desktop

## Acceptance Criteria

- [ ] Grid uses CSS Grid with proper column/row spanning
- [ ] Cards support 1×1, 2×1, 1×2, and 2×2 sizes
- [ ] Hover effect lifts card 4px with shadow elevation
- [ ] Focus ring visible on keyboard navigation (2px, `color.focus.ring`)
- [ ] Card padding uses `space.cardPadding` token
- [ ] Grid gap uses `space.cardGap` token
- [ ] Responsive: 4-column desktop, 2-column tablet, 1-column mobile
- [ ] All card titles use `typography.heading.card` token
- [ ] All descriptions use `typography.body.default` or `typography.body.small`
- [ ] Card background uses `color.surface.raised` token
- [ ] Respects `prefers-reduced-motion` (no lift effect)
- [ ] All text passes color contrast ratio (4.5:1 for body, 3:1 for large text)

## Accessibility

### ARIA & Semantics
- Use `<article>` for each card (semantic content container)
- Heading hierarchy: `<h2>` or `<h3>` for card titles (depends on page context)
- Use `<img>` with descriptive `alt` text for images
- If card is clickable, use `<a>` or `<button>` with clear link text

### Keyboard Navigation
- Tab order: Left-to-right, top-to-bottom through cards
- Focus ring must be visible with 2px width, `color.focus.ring`
- Ensure focus ring has sufficient contrast against card background
- Clickable cards must be keyboard accessible (use `<a>` or `<button>`)

### Screen Readers
- Card titles must be descriptive and unique
- Image `alt` text must describe content, not just "image"
- If card contains multiple interactive elements, use `aria-label` for context
- Use `aria-current="page"` for active/selected cards

### Color & Contrast
- Text must meet WCAG AA (4.5:1 for body, 3:1 for large text)
- Don't rely on color alone to indicate card state
- Ensure sufficient contrast between card background and text
- Test with WebAIM Contrast Checker

### Motion
- Respect `prefers-reduced-motion: reduce` by disabling lift effect
- Hover animations should not auto-play
- Avoid rapid or flashing animations

### Touch Targets
- Cards must be minimum 48px × 48px for touch targets
- Maintain `space.cardGap` (4px) between cards for touch accuracy
- Ensure clickable areas are easily tappable on mobile

### Content Considerations
- Avoid relying on image alone to convey meaning
- Provide text alternative for image-heavy cards
- Ensure card order makes sense without visual layout
- Test with screen readers (NVDA, JAWS, VoiceOver)
