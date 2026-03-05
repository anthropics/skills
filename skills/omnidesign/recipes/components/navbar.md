# Navigation Bar

A responsive header component with transparent-to-solid background transition on scroll, active link styling, mobile hamburger menu, and flexible logo/nav/CTA layout.

## When to Use

**Use navbar for:**
- Primary site navigation on all pages
- Persistent header across page sections
- Brand/logo placement and recognition
- Call-to-action button placement
- Mobile menu access

**Don't use for:**
- Breadcrumb navigation (use separate component)
- Pagination (use separate component)
- Sidebar navigation (use separate component)
- Floating action buttons (use separate pattern)

## Component Anatomy

```
┌─────────────────────────────────────────────────────┐
│  [Logo]  [Nav Items]  [Secondary CTA]  [Mobile Menu]│
│                                                     │
│  Desktop Layout:                                    │
│  Logo (left) | Nav Items (center) | CTA (right)   │
│                                                     │
│  Mobile Layout:                                    │
│  Logo (left) | Hamburger Menu (right)             │
│  [Expanded Menu Overlay]                           │
│    - Nav Items (stacked)                           │
│    - Secondary CTA                                 │
└─────────────────────────────────────────────────────┘
```

## State Matrix

| State | Visual Treatment | Tokens Used |
|-------|------------------|-------------|
| **Default (Transparent)** | Background transparent, text `color.text.default`, no shadow | `color.surface.default` (transparent), `color.text.default` |
| **Scrolled (Solid)** | Background `color.surface.raised`, shadow applied, text remains `color.text.default` | `color.surface.raised`, `shadow.card`, `motion.hover` |
| **Active Link** | Text color `color.interactive.primary`, underline or bottom border | `color.interactive.primary`, `color.border.strong` |
| **Hover Link** | Text color `color.interactive.primary.hover`, slight opacity increase | `color.interactive.primary.hover`, `motion.hover` |
| **Focus Link** | Focus ring around link (2px), keyboard navigation visible | `color.focus.ring`, `space.inlineSm` |
| **Mobile Menu Open** | Overlay background `color.surface.overlay` with 80% opacity, menu slides in from right | `color.surface.overlay`, `motion.enter` |

## Token Usage

### Colors
- **Background (Transparent)**: `color.surface.default` with 0% opacity initially
- **Background (Solid)**: `color.surface.raised` after scroll threshold
- **Text**: `color.text.default` for nav items, `color.text.muted` for secondary text
- **Active/Hover**: `color.interactive.primary` and `color.interactive.primary.hover`
- **Mobile Overlay**: `color.surface.overlay` with 80% opacity

### Spacing
- **Navbar Height**: 64px (desktop), 56px (mobile) — standard touch target
- **Horizontal Padding**: `space.sectionX` (6px) on left/right
- **Nav Item Gap**: `space.inlineMd` (4px) between nav items
- **Logo Margin**: `space.inlineLg` (6px) right margin from nav items

### Typography
- **Logo**: `typography.heading.card` (xl, semibold) or custom brand font
- **Nav Items**: `typography.ui.button` (base, medium) for consistency
- **Mobile Menu Items**: `typography.body.default` for readability

### Shadows & Radii
- **Navbar Shadow**: `shadow.card` applied when scrolled (solid state)
- **Mobile Menu**: No radius on overlay, but menu content can use `radius.card`

## Implementation Notes

### CSS/HTML Approach

**Structure:**
```
<nav class="navbar" role="navigation" aria-label="Main navigation">
  <div class="navbar__container">
    <a href="/" class="navbar__logo">Logo</a>
    
    <ul class="navbar__items">
      <li><a href="/about" class="navbar__link">About</a></li>
      <li><a href="/products" class="navbar__link">Products</a></li>
      <li><a href="/blog" class="navbar__link">Blog</a></li>
    </ul>
    
    <button class="navbar__cta">Get Started</button>
    
    <button class="navbar__toggle" aria-label="Toggle menu" aria-expanded="false">
      <span class="navbar__hamburger"></span>
    </button>
  </div>
  
  <div class="navbar__mobile-menu" hidden>
    <ul class="navbar__mobile-items">
      <li><a href="/about">About</a></li>
      <li><a href="/products">Products</a></li>
      <li><a href="/blog">Blog</a></li>
      <li><button class="navbar__cta">Get Started</button></li>
    </ul>
  </div>
</nav>
```

**Key CSS patterns:**
- Use `position: fixed` or `sticky` for navbar positioning
- Apply `background: transparent` initially, transition to `color.surface.raised` on scroll
- Use `transition: background-color 200ms ease-out` for smooth background change
- Implement scroll detection with `window.addEventListener('scroll', ...)` or `IntersectionObserver`
- Use `display: flex` for horizontal layout, `justify-content: space-between` for spacing
- Hide nav items on mobile with `display: none`, show hamburger menu
- Implement mobile menu with `position: fixed`, `right: 0`, `top: navbar-height`, `width: 100vw`
- Use `transform: translateX(100%)` for off-screen menu, `translateX(0)` when open

**Scroll detection threshold:**
- Trigger solid background after 50-100px scroll (adjust based on design)
- Use `IntersectionObserver` on a sentinel element below navbar for better performance

**Active link styling:**
- Compare current URL with nav item `href` to determine active state
- Apply `color.interactive.primary` and bottom border (2px, `color.border.strong`)
- Update on page load and route changes

### React Approach

**Component structure:**
- Create `<Navbar>` wrapper managing scroll state and mobile menu visibility
- Create `<NavItem>` component for individual nav links with active state detection
- Use `useLocation()` or similar router hook to determine active link
- Implement `useEffect` with scroll listener for background transition
- Use `useState` for mobile menu open/close state

**State management:**
- Track scroll position with `useEffect` and `window.addEventListener('scroll')`
- Use `useCallback` to debounce scroll handler (throttle to 16ms for 60fps)
- Track mobile menu open state with `useState`
- Use `useLocation()` to detect active nav item

**Responsive behavior:**
- Use `useMediaQuery` hook to detect mobile breakpoint (768px)
- Show/hide nav items and hamburger menu based on breakpoint
- Adjust navbar height and padding for mobile

**Accessibility:**
- Use `<nav>` with `role="navigation"` and `aria-label="Main navigation"`
- Use `<a>` for nav items with proper `href` attributes
- Implement `aria-current="page"` for active link
- Use `aria-expanded` on hamburger button to indicate menu state
- Manage focus when mobile menu opens (trap focus inside menu)

## Acceptance Criteria

- [ ] Navbar uses `position: fixed` or `sticky` for persistent positioning
- [ ] Background transitions from transparent to `color.surface.raised` on scroll
- [ ] Scroll threshold is 50-100px (configurable)
- [ ] Active link styled with `color.interactive.primary` and bottom border
- [ ] Hover state uses `color.interactive.primary.hover` with `motion.hover`
- [ ] Focus ring visible on keyboard navigation (2px, `color.focus.ring`)
- [ ] Mobile menu hidden by default, visible on hamburger click
- [ ] Mobile menu overlay uses `color.surface.overlay` with 80% opacity
- [ ] Navbar height: 64px desktop, 56px mobile
- [ ] Horizontal padding uses `space.sectionX` token
- [ ] Nav item gap uses `space.inlineMd` token
- [ ] Logo uses `typography.heading.card` or custom brand font
- [ ] Nav items use `typography.ui.button` token
- [ ] Respects `prefers-reduced-motion` (instant background change)
- [ ] All text passes color contrast ratio (4.5:1 for body, 3:1 for large text)

## Accessibility

### ARIA & Semantics
- Use `<nav>` with `role="navigation"` and `aria-label="Main navigation"`
- Use `<a>` for nav items with descriptive link text
- Use `<button>` for hamburger menu toggle with `aria-label="Toggle menu"`
- Implement `aria-expanded="true/false"` on hamburger button
- Use `aria-current="page"` for active nav item

### Keyboard Navigation
- Tab order: Logo (not focusable) → Nav items → CTA → Hamburger menu
- Focus ring must be visible with 2px width, `color.focus.ring`
- Ensure focus ring has sufficient contrast against navbar background
- Hamburger menu must be keyboard accessible
- Mobile menu must be closable with Escape key

### Screen Readers
- Nav item text must be descriptive (not "Click here")
- Logo link must have descriptive text or `aria-label`
- Hamburger button must have `aria-label="Toggle menu"`
- Active nav item must be announced with `aria-current="page"`
- Mobile menu items must be announced when menu opens

### Color & Contrast
- Text must meet WCAG AA (4.5:1 for body, 3:1 for large text)
- Active link color must have sufficient contrast
- Ensure sufficient contrast between text and background (both transparent and solid states)
- Test with WebAIM Contrast Checker

### Motion
- Respect `prefers-reduced-motion: reduce` by disabling animations
- Background transition should be instant if reduced motion is preferred
- Mobile menu should slide without animation if reduced motion is preferred

### Touch Targets
- Navbar height minimum 56px for touch targets
- Nav items minimum 48px × 48px for touch targets
- Hamburger menu button minimum 48px × 48px
- Maintain `space.inlineMd` (4px) gap between nav items for touch accuracy

### Mobile Considerations
- Ensure navbar doesn't obscure important content
- Mobile menu should not auto-close on link click (let user decide)
- Implement focus trap in mobile menu (Tab cycles within menu)
- Close menu when user navigates to new page
