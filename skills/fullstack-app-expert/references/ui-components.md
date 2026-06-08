# UI Components & Design Systems (2025-2026)

## shadcn/ui — The Dominant Pattern

shadcn/ui is not a component library you install as a dependency — it's a collection of copy-pasteable TypeScript components built on Radix UI primitives + Tailwind CSS. You own the code completely.

### Installation & Setup
```bash
npx shadcn@latest init
npx shadcn@latest add button dialog form table
```

Components land in `components/ui/` in your project. Edit them freely. No version lock-in.

### Tailwind CSS v4 Support
shadcn/ui fully supports Tailwind CSS v4 as of 2025. Key changes with v4:
- CSS-first configuration: config moves from `tailwind.config.ts` to CSS `@theme` block
- `tailwindcss-animate` was deprecated in March 2025 — use `tw-animate-css` or `motion` instead
- CSS variables are now first-class: `--color-primary` in CSS, referenced as `text-primary` in classes
- New `@theme` directive replaces the JS config object

```css
/* globals.css — Tailwind v4 configuration */
@import "tailwindcss";

@theme {
  --color-primary: oklch(0.21 0.006 285.885);
  --color-primary-foreground: oklch(0.985 0 0);
  --radius: 0.5rem;
}
```

### Component Customization Patterns
```tsx
// Compound components pattern (common in shadcn/ui):
import { Card, CardHeader, CardTitle, CardContent } from "@/components/ui/card";

// Variant-driven with cva:
import { cva, type VariantProps } from "class-variance-authority";
const buttonVariants = cva(
  "inline-flex items-center justify-center rounded-md text-sm font-medium transition-colors",
  {
    variants: {
      variant: {
        default: "bg-primary text-primary-foreground hover:bg-primary/90",
        destructive: "bg-destructive text-destructive-foreground",
        outline: "border border-input bg-background hover:bg-accent",
      },
      size: {
        default: "h-10 px-4 py-2",
        sm: "h-9 rounded-md px-3",
        lg: "h-11 rounded-md px-8",
      },
    },
    defaultVariants: { variant: "default", size: "default" },
  }
);
```

### New in 2025: Rhea Style
shadcn/ui introduced the "Rhea" style variant — a more compact, product-focused design system for dense UIs like admin dashboards and data-heavy applications.

---

## Radix UI Primitives

Radix provides unstyled, accessible primitives that shadcn/ui builds on. Use directly when you need full styling control without shadcn/ui's opinions.

Key primitives:
- `@radix-ui/react-dialog` — modal dialogs with focus trap, Esc key, ARIA
- `@radix-ui/react-dropdown-menu` — keyboard-navigable menus
- `@radix-ui/react-select` — accessible custom selects
- `@radix-ui/react-toast` / Sonner — notifications
- `@radix-ui/react-tooltip`, `@radix-ui/react-popover`
- `@radix-ui/react-slider`, `@radix-ui/react-switch`

All primitives handle: focus management, keyboard navigation, screen reader announcements, RTL support.

---

## Tailwind CSS 4 — Key Changes

### What changed from v3 to v4:
1. **No more `tailwind.config.ts`** — configuration is CSS-native via `@theme`
2. **Automatic content detection** — no more `content: ['./src/**/*.tsx']` arrays
3. **`@import "tailwindcss"`** replaces the three-directive setup
4. **Oxide engine** (Lightning CSS) — faster builds, native CSS nesting, cascade layers
5. **New utilities**: `field-sizing-content`, `starting-style`, `not-*` variants
6. **`@utility` directive** for custom utilities: `@utility tab-4 { tab-size: 4; }`

### Migration from v3:
```bash
npx @tailwindcss/upgrade
```
Most v3 classes remain identical. Key breaking changes: `bg-opacity-*` → `bg-black/50`, `text-opacity-*` → `text-black/50`.

---

## Animation Libraries

### Framer Motion / Motion for React
Rebranded as "Motion" (motion.dev). Still the dominant React animation library.

```tsx
import { motion, AnimatePresence } from "motion/react";

// Basic animation:
<motion.div
  initial={{ opacity: 0, y: 20 }}
  animate={{ opacity: 1, y: 0 }}
  exit={{ opacity: 0, y: -20 }}
  transition={{ duration: 0.3, ease: "easeOut" }}
/>

// Layout animations (shared element transitions):
<motion.div layoutId="hero-image" />

// LazyMotion for bundle optimization (~30KB savings):
import { LazyMotion, domAnimation, m } from "motion/react";
<LazyMotion features={domAnimation}>
  <m.div animate={{ x: 100 }} />
</LazyMotion>
```

Performance notes:
- Uses Web Animations API for `transform` and `opacity` — GPU-accelerated, no re-renders
- Layout animations go through React state — limit in data-dense lists
- 46KB gzipped full, ~34KB with tree shaking, ~16KB with LazyMotion

### Motion v12 new features (2025):
- Automatic reduced-motion fallbacks (respects `prefers-reduced-motion`)
- Scroll-linked timelines via `useScroll` and ScrollTimeline API
- Improved `useAnimate` for imperative sequences

### React Spring — When to Use Instead
- Physics-based animations (spring constants, friction, mass)
- Three.js / R3F integration
- Gesture-driven interactions with precise spring physics
- 30% smaller bundle in v10 rewrite
- Choose React Spring for physics-heavy UIs; choose Motion for timeline/variant-based animations

---

## Accessibility Standards

All shadcn/ui components are WAI-ARIA compliant. Key patterns to maintain:
- Every interactive element has a keyboard interaction
- Focus management on modal open/close (`FocusTrap`, `initialFocus`)
- `aria-live` regions for dynamic content updates
- Sufficient color contrast (WCAG 2.1 AA minimum: 4.5:1 text, 3:1 UI)
- Don't disable the default focus ring — customize it with `focus-visible:` instead of removing it

---

## UI Library Comparison (2025)

| Library | Bundle | Customization | Accessibility | Best For |
|---------|--------|---------------|---------------|----------|
| shadcn/ui | Minimal (own code) | Full ownership | Excellent (Radix) | Most projects |
| Radix UI bare | ~5-15KB per primitive | Full styling control | Excellent | Design system builders |
| Mantine | ~40-60KB | Good | Good | Full-featured admin UIs |
| MUI (Material) | ~80-120KB | Limited (Material Design locked) | Good | Enterprise, Google-style |
| Chakra UI v3 | ~35KB | Good | Good | Rapid prototyping |

**Recommendation**: shadcn/ui for 90% of projects. Add Radix primitives directly for components shadcn/ui doesn't cover.
