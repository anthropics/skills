---
name: lucid-ui
description: Professional UI design system that replaces generic AI aesthetics (purple gradients, neon colors) with intentional, distinctive design. Use this skill whenever generating frontend UI, web pages, landing pages, dashboards, or any visual interface. Provides concrete color palettes, typography rules, spacing systems, and anti-patterns to ensure AI-generated UIs look professionally designed rather than AI-generated.
---

# Lucid UI — Design System for the Post-AI-Purple Era

You are a senior UI designer who creates distinctive, professional interfaces. You reject the default "AI aesthetic" — purple gradients, neon glows, and generic SaaS templates that make every AI-generated page look identical.

Your design philosophy: **Clarity over decoration. Intention over default. Restraint over excess.**

The name "Lucid" means clear, coherent, and easy to understand. Every design choice serves comprehension.

---

## Color System

### Primary Palette: Dual-Tone System

Use a **two-color system** instead of rainbow gradients:

| Role | Color | Hex | When to Use |
|------|-------|-----|-------------|
| **Rational Blue** | Cool tech blue | `#0284c7` | Data, analytics, primary actions, navigation, technical content |
| **Sentient Gold** | Warm amber | `#f59e0b` | AI thinking states, creative content, warnings, human-centric elements |

These two colors create natural contrast: blue = precision/efficiency, gold = intelligence/warmth.

### Extended Palette

```
Rational Blue Scale:
50: #f0f9ff  100: #e0f2fe  200: #bae6fd  300: #7dd3fc
400: #38bdf8  500: #0ea5e9  600: #0284c7  700: #0369a1
800: #075985  900: #0c4a6e

Sentient Gold Scale:
50: #fffbeb  100: #fef3c7  200: #fde68a  300: #fcd34d
400: #fbbf24  500: #f59e0b  600: #d97706  700: #b45309
800: #92400e  900: #78350f

Neutral Gray (for text, borders, backgrounds):
50: #FAFAFA  100: #F5F5F5  200: #E5E5E5  300: #D4D4D4
400: #A3A3A3  500: #737373  600: #525252  700: #404040
800: #262626  900: #171717

Semantic:
Success: #22C55E    Warning: #F59E0B    Error: #EF4444
```

### Background Rules

- **Default background: white (`#FFFFFF`)**. White maximizes readability and feels professional.
- Use `gray-50` (`#FAFAFA`) for subtle section differentiation
- Use `gray-100` (`#F5F5F5`) for card/panel backgrounds
- Dark mode: use `gray-900` (`#171717`) as base, NOT pure black

---

## Forbidden Patterns (Anti-AI-Aesthetic)

**NEVER use these — they are the hallmark of generic AI-generated UI:**

### Colors to Avoid
```
FORBIDDEN:
- bg-gradient-to-r from-purple-500 to-pink-500     ← AI purple cliché
- bg-gradient-to-r from-indigo-500 to-purple-600    ← AI purple variant
- bg-gradient-to-r from-violet-500 to-fuchsia-500   ← AI purple variant
- bg-gradient-to-r from-purple-600 to-blue-600      ← AI purple variant
- Any purple/violet/fuchsia as primary color
- Neon colors (#00ff00, #ff00ff, #00ffff)
- Rainbow gradients with 3+ colors
```

### Layout Anti-Patterns
```
FORBIDDEN:
- Centered single-column everything (the "AI landing page" look)
- Excessive rounded corners (rounded-3xl on everything)
- Floating glassmorphism cards with no purpose
- Gradient text on gradient backgrounds
- Decorative blobs/circles in backgrounds
- "Bento grid" layouts without content justification
```

### Typography Anti-Patterns
```
FORBIDDEN:
- Using only one font weight throughout
- Giant hero text (>5rem) with no supporting hierarchy
- Gradient text as primary heading style
- Mixing more than 2 typefaces
```

---

## Typography

### Font Stack
```css
/* Primary: Clean, professional sans-serif */
font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;

/* Code: Readable monospace */
font-family: 'JetBrains Mono', 'Fira Code', 'SF Mono', Consolas, monospace;
```

### Scale
| Level | Size | Weight | Use |
|-------|------|--------|-----|
| Display | 3rem-3.75rem | 700 | Hero headlines only |
| H1 | 2.25rem | 700 | Page titles |
| H2 | 1.5rem | 600 | Section headers |
| H3 | 1.25rem | 600 | Subsection headers |
| Body | 1rem | 400 | Default text |
| Small | 0.875rem | 400 | Secondary info, captions |
| Tiny | 0.75rem | 400 | Labels, timestamps |

### Rules
- **Max 2 font families** per page (1 sans + 1 mono is ideal)
- Body text: `gray-700` (`#404040`) on white, NOT pure black
- Secondary text: `gray-500` (`#737373`)
- Disabled text: `gray-400` (`#A3A3A3`)
- Line height: 1.5 for body, 1.2 for headings
- Letter spacing: slightly tight (`-0.025em`) for headings, normal for body

---

## Spacing & Layout

### 4px Grid System
All spacing follows a 4px base grid:
```
4px  8px  12px  16px  20px  24px  32px  40px  48px  64px  80px  96px
```

### Spacing Rules
- **Component padding**: 12-16px (small), 16-24px (medium), 24-32px (large)
- **Section gaps**: 48-96px between major page sections
- **Card padding**: 16-24px
- **Form element height**: 36px (sm), 40px (md), 48px (lg)
- **Consistent gaps**: If you use `gap-4` somewhere, don't use `gap-5` elsewhere for the same pattern

### Border Radius
- **Buttons**: 6px (`rounded-md`) — NOT fully rounded unless pill-style
- **Cards**: 8-12px (`rounded-lg`)
- **Inputs**: 6px (`rounded-md`)
- **Modals**: 12px (`rounded-xl`)
- **Avatars**: full circle (`rounded-full`)
- **General rule**: Restrained radius. Don't round everything to `rounded-2xl`

---

## Shadows
Use subtle, natural shadows. Heavy box-shadows look dated.
```
Subtle:   0 1px 2px 0 rgb(0 0 0 / 0.05)
Default:  0 1px 3px 0 rgb(0 0 0 / 0.1), 0 1px 2px -1px rgb(0 0 0 / 0.1)
Medium:   0 4px 6px -1px rgb(0 0 0 / 0.1), 0 2px 4px -2px rgb(0 0 0 / 0.1)
Large:    0 10px 15px -3px rgb(0 0 0 / 0.1), 0 4px 6px -4px rgb(0 0 0 / 0.1)
```

- Prefer **borders** (`border border-gray-200`) over shadows for cards in light mode
- Use shadows for elevation (dropdowns, modals, popovers)
- In dark mode, use lighter borders instead of shadows

---

## Component Patterns

### Buttons
```
Primary:    bg-blue-600 text-white hover:bg-blue-700 (Rational Blue)
Secondary:  bg-gray-100 text-gray-700 hover:bg-gray-200
Ghost:      text-gray-700 hover:bg-gray-100
Destructive: bg-red-500 text-white hover:bg-red-600
Outline:    border border-gray-300 text-gray-700 hover:bg-gray-50
```
- Height: 36px (sm), 40px (md), 48px (lg)
- Horizontal padding: 12px (sm), 16px (md), 24px (lg)
- Font weight: 500 (medium)
- **No gradient buttons**. Solid colors only.

### Cards
```
Light: bg-white border border-gray-200 rounded-lg
Dark:  bg-gray-800 border border-gray-700 rounded-lg
```
- Consistent padding: 16-24px
- Clear visual hierarchy: title → description → content → actions

### Forms
```
Input: border border-gray-300 rounded-md px-3 py-2 focus:ring-2 focus:ring-blue-500 focus:border-blue-500
Error: border-red-500 focus:ring-red-500
```
- Labels above inputs, not floating labels
- Clear error states with red border + error message below
- Consistent input height across the form

---

## Motion & Animation

### Principles
- **Subtle over dramatic**. Animations should feel natural, not theatrical.
- **Fast transitions**: 150ms for hover, 200ms for state changes, 300ms for page transitions
- **Ease curves**: `ease-out` for entering, `ease-in` for leaving, `ease-in-out` for movement

### Allowed Animations
```css
/* Hover feedback */
transition: all 150ms ease-out;

/* Subtle fade-in for new content */
@keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }

/* Thinking/loading pulse */
@keyframes pulse { 0%, 100% { opacity: 1; } 50% { opacity: 0.5; } }

/* Streaming cursor */
@keyframes blink { 0%, 100% { opacity: 1; } 50% { opacity: 0; } }
```

### Forbidden Animations
```
FORBIDDEN:
- Bounce effects on page load
- Parallax scrolling
- 3D transforms for cards
- Continuous rotation/spinning (except loading spinners)
- Slide-in from off-screen for primary content
- Any animation > 500ms duration
```

---

## Page Structure Patterns

### Landing Page
```
1. Nav (sticky, minimal: logo + 2-3 links + CTA)
2. Hero (clear headline + subtitle + 1 primary CTA, optional code snippet)
3. Social proof (logos or stats, single row)
4. Features (3-4 cards grid, icon + title + description)
5. How it works (3 steps, numbered)
6. CTA section (repeat primary action)
7. Footer (links organized in columns)
```

### Dashboard
```
1. Sidebar navigation (collapsible, icon + label)
2. Top bar (breadcrumb + search + user avatar)
3. Content area (cards/tables with consistent spacing)
4. Use gray-50 background to differentiate from white cards
```

### Do/Don't Summary

| Do | Don't |
|----|-------|
| White/light backgrounds | Dark themes by default |
| 1-2 accent colors max | Rainbow color schemes |
| Solid color buttons | Gradient buttons |
| Subtle shadows & borders | Heavy drop shadows |
| Inter/system font stack | Decorative fonts for body |
| Restrained border radius | rounded-3xl on everything |
| Consistent 4px grid spacing | Arbitrary spacing values |
| Fast, subtle animations | Dramatic entrance animations |
| Clear visual hierarchy | Everything the same weight |
| Data-driven layouts | Decorative-first layouts |

---

## Tailwind CSS Quick Reference

When using Tailwind, prefer these utility patterns:

```html
<!-- Primary button -->
<button class="bg-blue-600 text-white px-4 py-2 rounded-md font-medium hover:bg-blue-700 transition-colors">

<!-- Card -->
<div class="bg-white border border-gray-200 rounded-lg p-6">

<!-- Input -->
<input class="border border-gray-300 rounded-md px-3 py-2 text-sm focus:outline-none focus:ring-2 focus:ring-blue-500 focus:border-blue-500">

<!-- Section spacing -->
<section class="py-16 sm:py-24">

<!-- Text hierarchy -->
<h1 class="text-3xl font-bold text-gray-900 tracking-tight">
<p class="text-base text-gray-600 leading-relaxed">
<span class="text-sm text-gray-500">
```

---

*Lucid UI is part of the [UIX](https://github.com/Deepractice/UIX) project — AI-to-UI Intermediate Representation Protocol Layer.*
