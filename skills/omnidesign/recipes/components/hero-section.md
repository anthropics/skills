# Hero Section

A cinematic landing page hero with compelling typography hierarchy, dual call-to-action buttons, and atmospheric background treatment. Designed to capture attention and drive conversion.

## When to Use

**Use hero sections for:**
- Landing page above-the-fold content
- Product launch announcements
- Campaign entry points
- High-impact page introductions

**Don't use for:**
- Secondary pages or internal tools
- Content-heavy pages requiring immediate scrolling
- Mobile-first experiences with limited viewport height
- Accessibility-critical interfaces (use simpler patterns)

## Component Anatomy

```
┌─────────────────────────────────────────┐
│  [Gradient/Atmospheric Background]      │
│                                         │
│         [Hero Heading]                  │
│      (typography.heading.hero)          │
│                                         │
│      [Subtitle/Subheading]              │
│    (typography.body.large, muted)       │
│                                         │
│      [Body Copy - Optional]             │
│    (typography.body.default, muted)     │
│                                         │
│  [Primary CTA] [Secondary CTA]          │
│                                         │
│  [Background Image/Gradient Overlay]    │
└─────────────────────────────────────────┘
```

## State Matrix

| State | Visual Treatment | Tokens Used |
|-------|------------------|-------------|
| **Default** | Hero text centered, CTAs at standard opacity, background at full saturation | `color.text.default`, `color.interactive.primary`, `color.surface.default` |
| **Hover (CTA)** | Primary CTA background darkens, secondary CTA gains border, slight scale (1.02x) | `color.interactive.primary.hover`, `motion.hover` |
| **Focus (CTA)** | 2px focus ring around button, keyboard navigation visible | `color.focus.ring`, `space.inlineSm` |
| **Reduced Motion** | No scale/translate animations, instant opacity changes | `motion.hover` (duration: 0ms) |
| **Dark Mode** | Text inverted to `color.text.inverted`, background darkened, contrast maintained | `color.text.inverted`, `color.surface.overlay` |

## Token Usage

### Typography
- **Hero Heading**: `typography.heading.hero` — 6xl, bold, tight line-height for maximum impact
- **Subtitle**: `typography.body.large` with `color.text.muted` — supports hero without overwhelming
- **Body Copy**: `typography.body.default` with `color.text.muted` — optional supporting text, max 120 characters

### Colors
- **Text**: `color.text.default` for primary heading, `color.text.muted` for supporting copy
- **Buttons**: Primary uses `color.interactive.primary`, secondary uses `color.interactive.secondary` with border
- **Background**: Gradient from `color.surface.default` to semi-transparent overlay

### Spacing
- **Section Padding**: `space.sectionY` (16px) top/bottom, `space.sectionX` (6px) horizontal
- **Text Stack**: `space.stackLg` (6px) between heading and subtitle, `space.stackMd` (4px) between subtitle and body
- **Button Gap**: `space.inlineMd` (4px) between primary and secondary CTA

### Shadows & Radii
- **Button Radius**: `radius.button` for CTA buttons
- **Card Shadow** (optional): `shadow.card` if hero contains a card element

## Implementation Notes

### CSS/HTML Approach

**Structure:**
```
<section class="hero">
  <div class="hero__background"></div>
  <div class="hero__content">
    <h1 class="hero__heading">Main message</h1>
    <p class="hero__subtitle">Supporting message</p>
    <p class="hero__body">Optional body copy</p>
    <div class="hero__ctas">
      <button class="button button--primary">Primary CTA</button>
      <button class="button button--secondary">Secondary CTA</button>
    </div>
  </div>
</section>
```

**Key CSS patterns:**
- Use `position: relative` on hero container, `position: absolute` on background for layering
- Apply `background: linear-gradient(135deg, color1, color2)` or `background-image: url()` with overlay
- Center content with `display: flex; flex-direction: column; align-items: center; justify-content: center`
- Use `max-width: space.containerMax` (24rem/384px) for text content to maintain readability
- Apply `prefers-reduced-motion: reduce` media query to disable animations

**Responsive considerations:**
- Desktop: Full viewport height (min-height: 100vh), centered content
- Tablet (768px): Reduce heading size to `typography.heading.page`, maintain full height
- Mobile (375px): Reduce to 60-70vh height, stack CTAs vertically, use `typography.heading.section` for heading

### React Approach

**Component structure:**
- Create a `<Hero>` wrapper component accepting `heading`, `subtitle`, `body`, `primaryCta`, `secondaryCta` props
- Use `<img>` or CSS background for background image with proper `alt` text or `aria-hidden`
- Implement CTA buttons as separate `<Button>` components with variant props (primary/secondary)
- Use CSS modules or Tailwind for styling to maintain token consistency
- Wrap in `<section>` with proper ARIA landmarks
- Consider using `IntersectionObserver` for scroll-triggered animations (fade-in on viewport entry)

**State management:**
- Track hover state on CTAs for visual feedback
- Use CSS `:hover` and `:focus-visible` for button states (prefer CSS over React state)
- Implement `prefers-reduced-motion` detection for animation preferences

## Acceptance Criteria

- [ ] Hero heading uses `typography.heading.hero` token
- [ ] Subtitle uses `typography.body.large` with `color.text.muted`
- [ ] Primary CTA uses `color.interactive.primary` with hover state
- [ ] Secondary CTA has visible border and hover treatment
- [ ] Focus ring visible on keyboard navigation (2px, `color.focus.ring`)
- [ ] Responsive: Full height on desktop, 60-70vh on mobile
- [ ] Text content max-width 384px (space.containerMax) for readability
- [ ] Background image has proper contrast with text (WCAG AA minimum)
- [ ] Respects `prefers-reduced-motion` media query
- [ ] All text passes color contrast ratio (4.5:1 for body, 3:1 for large text)

## Accessibility

### ARIA & Semantics
- Use `<section>` with `role="region"` and `aria-label="Hero section"` for landmark navigation
- Heading must be `<h1>` (only one per page)
- CTAs must be `<button>` or `<a>` with clear, descriptive text (not "Click here")

### Keyboard Navigation
- Tab order: Heading (not focusable) → Subtitle (not focusable) → Primary CTA → Secondary CTA
- Focus ring must be visible with minimum 2px width, `color.focus.ring`
- Ensure focus ring has sufficient contrast against background

### Screen Readers
- Provide `alt` text for background images or use `aria-hidden="true"` if decorative
- CTA text must be descriptive: "Get Started" not "Click"
- Use `aria-label` for icon-only buttons if present

### Color & Contrast
- Text must meet WCAG AA (4.5:1 for body, 3:1 for large text)
- Don't rely on color alone to convey information
- Ensure sufficient contrast between text and background gradient
- Test with tools like WebAIM Contrast Checker

### Motion
- Respect `prefers-reduced-motion: reduce` by disabling animations
- Animations should not auto-play; trigger on user interaction
- Avoid flashing or rapid animations (>3 per second)

### Touch Targets
- CTAs must be minimum 48px × 48px (touch-friendly)
- Maintain `space.inlineMd` (4px) gap between buttons for touch accuracy
