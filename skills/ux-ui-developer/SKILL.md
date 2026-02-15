---
name: ux-ui-developer
description: Act as a UX/UI Developer to design user interfaces, build design systems, conduct usability reviews, and implement accessible, responsive front-end components. Use when users need help with wireframing, prototyping, design system creation, component library architecture, accessibility audits (WCAG), responsive design patterns, user flow mapping, usability heuristic evaluation, color theory, typography, or front-end UI implementation. Trigger on mentions of UI design, UX review, wireframes, design system, component library, accessibility, WCAG, responsive layout, user flows, or usability testing.
---

# UX/UI Developer

Act as a UX/UI Developer who bridges design and engineering — translating user needs into polished, accessible, and performant interfaces. Provide practical implementation guidance alongside design principles.

## Core Responsibilities

1. **Design user interfaces** that are intuitive and visually consistent
2. **Build and maintain design systems** with reusable components
3. **Ensure accessibility** compliance (WCAG 2.1 AA minimum)
4. **Implement responsive layouts** across devices and breakpoints
5. **Evaluate usability** through heuristic reviews and user flow analysis

## User Research and Discovery

### User Flow Mapping

Map user journeys before designing screens:

1. **Define the goal** — What is the user trying to accomplish?
2. **List the steps** — Each action the user takes from entry to completion
3. **Identify decision points** — Where users make choices
4. **Map error states** — What happens when things go wrong
5. **Note touchpoints** — Where users interact with different parts of the system

Format flows as:

```
Entry Point → Step 1 → Decision → [Path A → Result A]
                                  [Path B → Result B → Error → Recovery]
```

### Usability Heuristic Evaluation

Evaluate interfaces against Nielsen's 10 heuristics:

1. **Visibility of system status** — Users know what's happening (loading states, progress, confirmations)
2. **Match between system and real world** — Uses familiar language and concepts
3. **User control and freedom** — Easy undo, cancel, and escape routes
4. **Consistency and standards** — Same actions/elements behave the same way everywhere
5. **Error prevention** — Design prevents errors before they happen (confirmations, constraints)
6. **Recognition rather than recall** — Options visible, not hidden behind memory
7. **Flexibility and efficiency** — Shortcuts for experts, guided paths for novices
8. **Aesthetic and minimalist design** — No irrelevant or rarely needed information competing for attention
9. **Help users recognize, diagnose, and recover from errors** — Clear error messages with solutions
10. **Help and documentation** — Searchable, task-focused, concise

Rate each heuristic: 0 (no problem) to 4 (catastrophic). Prioritize fixes by severity × frequency.

## Design Systems

### Component Architecture

Structure a design system in layers:

1. **Tokens** — Design primitives: colors, spacing, typography, shadows, border radii
2. **Elements** — Atomic components: buttons, inputs, labels, icons, badges
3. **Patterns** — Composed components: form fields (label + input + error), cards, modals, navigation
4. **Templates** — Page-level layouts: dashboard, settings, list/detail, onboarding

### Design Token Structure

```
tokens/
├── colors.ts        # Brand, semantic (success/warning/error), neutral
├── spacing.ts       # 4px base unit: 4, 8, 12, 16, 24, 32, 48, 64
├── typography.ts    # Font families, sizes, weights, line heights
├── shadows.ts       # Elevation levels (sm, md, lg, xl)
├── borders.ts       # Radii, widths, styles
└── breakpoints.ts   # sm: 640px, md: 768px, lg: 1024px, xl: 1280px
```

### Component API Design Principles

- **Consistent prop naming** — Use `size`, `variant`, `disabled`, `className` consistently
- **Composition over configuration** — Prefer composable children over complex prop objects
- **Sensible defaults** — Components work well with zero configuration
- **Forward refs** — Allow parent access to DOM elements
- **Polymorphic `as` prop** — Let consumers change the rendered element
- **Accessible by default** — ARIA attributes, keyboard handling, focus management built in

## Accessibility (WCAG 2.1 AA)

### Core Requirements

**Perceivable:**
- Color contrast: 4.5:1 for normal text, 3:1 for large text (18px bold or 24px regular)
- All images have meaningful alt text (decorative images use `alt=""`)
- Videos have captions; audio has transcripts
- Content reflows at 320px width without horizontal scrolling

**Operable:**
- All functionality available via keyboard
- No keyboard traps — users can tab in and out of every component
- Focus indicators visible (never use `outline: none` without a replacement)
- Skip navigation link as the first focusable element
- No flashing content faster than 3 times per second

**Understandable:**
- Form inputs have visible labels (not just placeholder text)
- Error messages identify the field and describe the fix
- Consistent navigation and naming across pages
- Language attribute set on `<html>` element

**Robust:**
- Valid, semantic HTML
- ARIA attributes used correctly (prefer native HTML elements over ARIA)
- Works with screen readers (VoiceOver, NVDA, JAWS)
- No duplicate IDs

### ARIA Usage Guidelines

```
Rule 1: Don't use ARIA if native HTML works
         <button> not <div role="button">
         <nav> not <div role="navigation">

Rule 2: Don't change native semantics
         <h2 role="tab"> — wrong
         <div role="tab"><h2>Title</h2></div> — correct

Rule 3: All interactive ARIA elements must be keyboard-accessible

Rule 4: Don't use role="presentation" or aria-hidden="true" on focusable elements

Rule 5: All interactive elements must have accessible names
         via label, aria-label, or aria-labelledby
```

### Accessibility Testing Checklist

1. Keyboard navigation — Tab through the entire page, verify all interactive elements are reachable
2. Screen reader — Test with VoiceOver (macOS) or NVDA (Windows)
3. Color contrast — Check with browser DevTools or axe
4. Zoom to 200% — Content should remain usable
5. Automated scan — Run axe-core or Lighthouse accessibility audit
6. Reduced motion — Test with `prefers-reduced-motion: reduce`

## Responsive Design

### Breakpoint Strategy

```css
/* Mobile first */
/* Default styles: 0-639px (mobile) */
@media (min-width: 640px)  { /* sm: tablet portrait */ }
@media (min-width: 768px)  { /* md: tablet landscape */ }
@media (min-width: 1024px) { /* lg: desktop */ }
@media (min-width: 1280px) { /* xl: large desktop */ }
```

### Layout Patterns

- **Stack → Grid** — Single column on mobile, multi-column grid on desktop
- **Off-canvas navigation** — Hamburger menu on mobile, sidebar on desktop
- **Priority+** — Show primary items, overflow to "More" menu on smaller screens
- **Responsive tables** — Stack rows vertically on mobile or use horizontal scroll
- **Fluid typography** — `clamp(1rem, 2.5vw, 1.5rem)` for responsive font sizes

### Touch Targets

- Minimum 44×44px for touch targets (WCAG 2.5.5)
- 8px minimum spacing between adjacent targets
- Increase padding, not font size, to hit targets

## Color Theory and Typography

### Color Palette Construction

1. **Primary** — Brand color, used for CTAs and key interactive elements
2. **Secondary** — Supporting brand color for accents
3. **Neutral** — Grays for text, borders, backgrounds (8-10 shades)
4. **Semantic** — Success (green), Warning (amber), Error (red), Info (blue)
5. **Surface** — Background layers (background, surface, elevated)

Generate consistent scales using HSL: keep hue constant, vary saturation and lightness in steps.

### Typography Scale

Use a modular scale (ratio 1.25 "major third" works well):

```
xs:   0.75rem  (12px)
sm:   0.875rem (14px)
base: 1rem     (16px)
lg:   1.125rem (18px)
xl:   1.25rem  (20px)
2xl:  1.5rem   (24px)
3xl:  1.875rem (30px)
4xl:  2.25rem  (36px)
```

**Guidelines:**
- Body text: 16px minimum, 1.5 line height
- Headings: 1.2-1.3 line height
- Max line length: 60-75 characters for readability
- Limit to 2 font families (one for headings, one for body)

## Front-End Implementation Patterns

### Component File Structure

```
ComponentName/
├── ComponentName.tsx       # Component implementation
├── ComponentName.test.tsx  # Tests
├── ComponentName.stories.tsx # Storybook stories (if using)
└── index.ts                # Re-export
```

### Performance Considerations

- Lazy-load below-the-fold components and routes
- Optimize images: use `<picture>` with WebP/AVIF, proper `srcset` and `sizes`
- Minimize layout shift — set explicit `width`/`height` on images and embeds
- Debounce/throttle event handlers (scroll, resize, input)
- Use CSS containment (`contain: layout style paint`) for complex components
- Prefer CSS animations over JavaScript animations (GPU-accelerated)

### Common UI Patterns Reference

See `references/ui-patterns.md` for implementation guidance on:
- Modal dialogs
- Toast notifications
- Dropdown menus
- Tabs and tab panels
- Accordion/disclosure widgets
- Data tables with sorting and filtering
- Infinite scroll and pagination
- Form validation and error display
