# Implementation Quality Reference (v6.0)

Rules and guidelines that govern the QUALITY of generated output code. These rules are injected into every Gemini prompt and enforced by Phase 9.5 code quality gate.

This file exists because the cloning skill's extraction pipeline captures data with surgical precision, but without implementation rules, Gemini defaults to generic "AI slop" patterns — emoji placeholders, wrong animation libraries, layout-thrashing CSS, and inaccessible markup.

---

## Table of Contents
- Forbidden Patterns (Anti-Slop)
- Animation Tool Selection Matrix
- Animation Conflict Rules
- Performance Guardrails
- Spring & Easing Reference
- Accessibility Minimum
- TypeScript Common Gotchas
- Shared Patterns
- Animation Timing Scale
- Gemini Prompt Injection Guide

---

## Forbidden Patterns (Anti-Slop)

These patterns are the most common ways Gemini degrades clone fidelity. Each is explicitly forbidden in the Gemini prompt.

### Visual Placeholders
| Forbidden | Why | Fix |
|-----------|-----|-----|
| Emoji as image/icon placeholders | Replaces real visual content with Unicode glyphs | Use downloaded assets from Phase 1.5 or extracted SVGs from Phase 5 |
| Wireframe gray boxes (`bg-gray-200 w-full h-48`) | Substitutes for actual images | Use `<img src="/images/...">` with Phase 1.5 assets |
| Placeholder URLs (`unsplash.com`, `picsum.photos`, `placehold.co`, `via.placeholder.com`, `lorempixel.com`, `dummyimage.com`, `lorem.space`) | External URLs that break, change, or show wrong images | All assets must be local in `public/images/` |
| Generic icon names (`icon-placeholder`, `sample-icon`) | Loses the original site's icon system | Use Phase 5 extracted SVG markup or detected icon library |

### Content Placeholders
| Forbidden | Why | Fix |
|-----------|-----|-----|
| Lorem ipsum or any "Lorem" text | Original has real content — this is lazy substitution | Use exact text from Phase 6.5a HTML content extraction |
| Comments like `// Add more items here` or `// TODO` | Ships incomplete code that looks unfinished | Populate all sections with extracted content |
| Truncated content (`...` or `and more`) where original has full text | Loses real content that was successfully extracted | Use Phase 6.5a data which captures up to 20 cards and 15 paragraphs per section |

### Visual Effects Not in Original
| Forbidden | Why | Fix |
|-----------|-----|-----|
| Gratuitous neon glows or glow effects | AI models love adding `shadow-[0_0_20px_rgba(59,130,246,0.5)]` — if original doesn't have it, don't add it | Only use shadows/glows captured in Phase 2 design tokens |
| Gradient text on headings (unless original has it) | Common AI aesthetic that rarely matches originals | Check Phase 2 tokens — if no gradient detected, use solid colors |
| Oversaturated accent colors | AI tends to crank saturation to make things "pop" | Use exact hex values from Phase 2 HIGH confidence colors |
| Rounded corners that don't match (`rounded-full` vs `rounded-lg`) | Subtle but noticeable fidelity gap | Use Phase 6.5b computed measurements for exact border-radius values |

### Code Patterns
| Forbidden | Why | Fix |
|-----------|-----|-----|
| Default shadcn/Radix styling without customization | Generic component library look, not the original's | Customize to match Phase 2 design tokens exactly |
| Hardcoded `#000000` pure black (unless original uses it) | AI defaults to pure black; most sites use near-black like `#111827` or `#0f172a` | Check Phase 2 tokens — use the exact dark color captured |
| External font CDN URLs (`fonts.googleapis.com`, `fonts.gstatic.com`) | CORS blocks cross-origin fonts in development | Self-host fonts in `public/fonts/` per Phase 8.4 pipeline |

---

## Animation Tool Selection Matrix

The extraction pipeline (Phase 6) captures WHAT animations exist. This matrix determines HOW to implement them. The goal is faithful reproduction using the right tool for each animation type.

### Decision Matrix

| Animation Need | Tool | Why This Tool |
|---------------|------|---------------|
| UI enter/exit/layout transitions | Framer Motion (`AnimatePresence`, `motion.div`) | React-aware, handles component mount/unmount gracefully |
| Scroll-triggered reveals (fade in, slide up) | CSS `@keyframes` + `IntersectionObserver` | Zero-dependency, browser-optimized, no React 18 Strict Mode issues |
| Scroll storytelling with scrub (parallax tied to scroll position) | GSAP `ScrollTrigger` with `scrub: true` | Only library with true frame-accurate scroll-position binding |
| Pinned sections (content changes while section stays fixed) | GSAP `ScrollTrigger` with `pin: true` | Only library with reliable scroll pinning that handles resize |
| Hover/focus micro-interactions | CSS `:hover` and `:focus` transitions | Zero JavaScript overhead, GPU-composited by default |
| Continuous loops (spinning, pulsing, floating) | CSS `@keyframes` with `infinite` | Browser-optimized animation loop, no JS event loop involvement |
| Simple parallax (layers move at different speeds) | `IntersectionObserver` + CSS custom properties | Lightweight, no heavy library needed for simple depth effects |
| Complex timeline sequencing | GSAP `timeline()` | Only tool for coordinating 10+ animations with precise sequencing |
| 3D effects / WebGL | Three.js / React Three Fiber | GPU rendering pipeline, isolated canvas |
| Staggered entrance animations | CSS `animation-delay: calc(var(--index) * 80ms)` or Framer `staggerChildren` | CSS approach is simpler; Framer when items mount/unmount dynamically |

### How to Map Phase 6 Data to Tools

1. Phase 6 runtime recorder captures animation `type` field: `web-animation`, `gsap-to`, `gsap-from`, `style-transition`
2. Check for `scrollTrigger` in captured data:
   - Has `scrollTrigger.scrub` → GSAP ScrollTrigger
   - Has `scrollTrigger.pin` → GSAP ScrollTrigger
   - Has `scrollTrigger` without scrub/pin → CSS `@keyframes` + IntersectionObserver (simpler, same visual result)
3. No scroll trigger, just entrance animations → CSS `@keyframes` + IntersectionObserver
4. Hover-only changes in `styleTransitions` data → CSS `:hover` transitions

### Why CSS @keyframes is the Default

GSAP + React 18 Strict Mode is a known pain point. In development mode, `useLayoutEffect` runs twice, leaving elements stuck at partial opacity or mid-transform. CSS `@keyframes` animations are completely immune to this because they run in the browser's compositor thread, outside React's lifecycle.

**Rule of thumb:** Only reach for GSAP when the animation REQUIRES scroll-position binding (`scrub`) or viewport pinning (`pin`). For everything else, CSS is simpler, faster, and more reliable.

---

## Animation Conflict Rules

These are MANDATORY — violating them causes runtime bugs, not just style issues.

### Rule 1: Never Mix GSAP + Framer Motion in the Same Component

**Why it breaks:** Both libraries try to control the same DOM element's `transform` and `opacity`. They fight over style application order, causing flickering, stuck states, and animation overrides.

**Correct pattern for sites that use both:**
- GSAP for scroll-triggered sections (pinning, parallax, horizontal scroll)
- Framer Motion for UI components (modals, dropdowns, page transitions)
- Each animation library lives in separate component files

### Rule 2: Three.js / R3F Must Live in an Isolated Canvas Wrapper

**Why:** The `<Canvas>` component from React Three Fiber creates its own rendering context. It must be a `"use client"` leaf component with `React.memo` wrapping.

### Rule 3: Always Lazy-Load Heavy Animation Libraries

```tsx
// Correct: dynamic import
const gsap = await import('gsap');
const { ScrollTrigger } = await import('gsap/ScrollTrigger');

// Correct: Next.js dynamic
const ThreeScene = dynamic(() => import('./ThreeScene'), { ssr: false });
```

**Why:** GSAP is ~30KB, Three.js is ~150KB. Eager loading blocks first paint.

---

## Performance Guardrails

These rules prevent the clone from janking on scroll, stuttering on mobile, or causing layout thrashing.

### GPU-Only Animation Properties

**ONLY animate these properties** (they run on the GPU compositor thread):
- `transform` (translate, scale, rotate)
- `opacity`
- `filter` (blur, brightness)
- `clip-path`

**NEVER directly animate these** (they trigger layout recalculation):
- `width`, `height` → Use `transform: scaleX/scaleY` instead
- `top`, `left`, `right`, `bottom` → Use `transform: translateX/Y` instead
- `margin`, `padding` → Use `transform: translate` instead
- `font-size` → Use `transform: scale` instead
- `border-width` → Animate `opacity` of an overlay instead

**Why this matters:** Animating layout properties forces the browser to recalculate positions of ALL elements on every frame. At 60fps, that's 16ms per frame — layout recalculation easily takes 20-50ms, causing visible jank.

### Mobile Performance

- `prefers-reduced-motion: reduce` → Disable ALL non-essential animations
- `pointer: coarse` (touch devices) → Disable parallax and 3D tilt effects (no mouse position to track)
- Particle counts: desktop 800 max, tablet 300, mobile 100
- GSAP `pin` → Disable on viewports < 768px (pinning on mobile is janky and confusing)
- `will-change` → Apply ONLY during the animation, remove after. Never set permanently.

### React-Specific Rules

- Perpetual/looping animations: Isolate in `React.memo` leaf components (prevents parent re-renders from restarting the animation)
- Every `useEffect` with GSAP or IntersectionObserver MUST return a cleanup function:
  ```tsx
  useEffect(() => {
    const ctx = gsap.context(() => { /* animations */ }, containerRef);
    return () => ctx.revert(); // MANDATORY cleanup
  }, []);
  ```
- `"use client"` directive: Only on components that actually use browser APIs. Never on layout/page components.

---

## Spring & Easing Reference

When Phase 6 captures easing values, use them exactly. When recording is ambiguous or partial, use these production-quality fallbacks instead of Gemini's default `ease-in-out`.

### Framer Motion Springs

| Feel | Config | Use For |
|------|--------|---------|
| Snappy | `{ stiffness: 300, damping: 30 }` | Buttons, toggles, micro-interactions |
| Smooth | `{ stiffness: 150, damping: 20 }` | Modals, panels, drawer slides |
| Bouncy | `{ stiffness: 100, damping: 10 }` | Playful UI, attention-grabbing elements |
| Gentle | `{ stiffness: 80, damping: 15 }` | Page transitions, large surface movements |
| Heavy | `{ stiffness: 60, damping: 20 }` | Dramatic reveals, hero animations |

### CSS Cubic-Bezier

| Name | Value | Use For |
|------|-------|---------|
| Decelerate (enter) | `cubic-bezier(0.0, 0.0, 0.2, 1.0)` | Elements appearing/entering |
| Accelerate (exit) | `cubic-bezier(0.4, 0.0, 1.0, 1.0)` | Elements leaving/disappearing |
| Standard | `cubic-bezier(0.4, 0.0, 0.2, 1.0)` | General-purpose transitions |
| Premium | `cubic-bezier(0.215, 0.61, 0.355, 1)` | High-end, luxury feel (Easing.Out Quart) |
| Elastic | `cubic-bezier(0.68, -0.55, 0.265, 1.55)` | Overshoot/bounce effect |
| Smooth decel | `cubic-bezier(0.16, 1, 0.3, 1)` | Scroll reveals, content fade-in |
| Smooth accel | `cubic-bezier(0.7, 0, 0.84, 0)` | Content fade-out, exit animations |

### GSAP Easing Names

| Phase 6 Captured | GSAP Equivalent | Feel |
|-----------------|-----------------|------|
| `power1.out` | Gentle deceleration | Subtle, natural |
| `power2.out` | Standard deceleration | Most common, professional |
| `power3.out` | Strong deceleration | Dramatic entrance |
| `power2.inOut` | Standard ease-in-out | Smooth transitions |
| `elastic.out` | Elastic overshoot | Playful, bouncy |
| `back.out` | Slight overshoot | Springy, energetic |
| `expo.out` | Sharp deceleration | Premium, luxury |

---

## Accessibility Minimum

The clone should be at LEAST as accessible as the original. These are non-negotiable baseline requirements.

### Required in Every Clone

1. **`prefers-reduced-motion`** — Add to `globals.css`:
   ```css
   @media (prefers-reduced-motion: reduce) {
     *, *::before, *::after {
       animation-duration: 0.01ms !important;
       animation-iteration-count: 1 !important;
       transition-duration: 0.01ms !important;
       scroll-behavior: auto !important;
     }
   }
   ```

2. **No content flashing** — Never flash content more than 3 times per second

3. **Visible focus rings** — Never use `outline: none` without a replacement. Default:
   ```css
   :focus-visible {
     outline: 2px solid currentColor;
     outline-offset: 2px;
   }
   ```

4. **`aria-live` for dynamic content** — Any region that updates without page reload needs `aria-live="polite"`

5. **Keyboard navigation** — All interactive elements must be reachable via Tab key. Check the clone's accessibility tree (Phase 9.6) against the original.

---

## TypeScript Common Gotchas

These patterns cause compilation failures in strict TypeScript (which Next.js enables by default with `strict: true` in tsconfig.json). A broken build means Phase 9 verification cannot start.

### useRef Initialization
```tsx
// WRONG — TypeScript error: Expected 1 argument, got 0
const ref = useRef<HTMLDivElement>();
const timer = useRef<ReturnType<typeof setInterval>>();

// CORRECT — always pass initial value
const ref = useRef<HTMLDivElement>(null);
const timer = useRef<ReturnType<typeof setInterval>>(null);
```

**Why:** `useRef<T>()` without an argument produces `MutableRefObject<T | undefined>`, but DOM refs and timer refs are typically typed as `T | null`. Passing `null` explicitly satisfies TypeScript's strict mode.

### Event Handler Typing
```tsx
// WRONG — implicit 'any' parameter
const handleClick = (e) => { e.preventDefault(); };

// CORRECT — explicit React event type
const handleClick = (e: React.MouseEvent<HTMLButtonElement>) => { e.preventDefault(); };
```

### Optional Property Access
```tsx
// WRONG — runtime error if data is undefined
const value = props.data.name;

// CORRECT — optional chaining
const value = props.data?.name;
```

### useState with Complex Types
```tsx
// WRONG — TypeScript cannot infer the array element type from empty array
const [items, setItems] = useState([]);

// CORRECT — explicit type parameter
const [items, setItems] = useState<string[]>([]);
const [user, setUser] = useState<User | null>(null);
```

---

## Shared Patterns

When Gemini generates 3+ components with the same code pattern, it inflates bundle size and creates maintenance burden. The most common offender in cloning is the IntersectionObserver reveal pattern.

### IntersectionObserver Reveal Hook

Instead of copy-pasting this 12-line block into every component:
```tsx
// hooks/useReveal.ts
import { useEffect, useRef } from 'react';

export function useReveal(options?: IntersectionObserverInit) {
  const ref = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const el = ref.current;
    if (!el) return;

    const observer = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting) {
            entry.target.classList.add('visible');
            observer.unobserve(entry.target); // Only animate once
          }
        });
      },
      { threshold: 0.1, ...options }
    );

    el.querySelectorAll('.reveal').forEach((child) => observer.observe(child));
    return () => observer.disconnect();
  }, []);

  return ref;
}
```

**Usage in components:**
```tsx
import { useReveal } from '@/hooks/useReveal';

export default function Hero() {
  const ref = useReveal({ threshold: 0.15 });
  return (
    <section ref={ref}>
      <h1 className="reveal">Hello</h1>
    </section>
  );
}
```

### GSAP ScrollTrigger Hook

```tsx
// hooks/useScrollTrigger.ts — wraps GSAP context creation + cleanup
import { useEffect, useRef } from 'react';

export function useScrollTrigger(setup: (ctx: gsap.Context) => void) {
  const ref = useRef<HTMLDivElement>(null);

  useEffect(() => {
    if (!ref.current) return;
    const ctx = gsap.context(setup, ref.current);
    return () => ctx.revert(); // MANDATORY cleanup
  }, []);

  return ref;
}
```

**Rule of thumb:** If you're about to paste the same logic into a 3rd component, stop and make a hook.

---

## Animation Timing Scale

Consistent timing creates rhythm. Inconsistent timing (75ms here, 450ms there) creates a "Frankenstein animation" feel where no two interactions feel related.

**When Phase 6 captures real timing data from the original site, use those exact values** — even if they seem inconsistent. Cloning = faithful reproduction. This scale is a FALLBACK for when Phase 6 data is missing or ambiguous.

| Level | Duration | Use For | Easing |
|-------|----------|---------|--------|
| Micro | 100ms | Tooltips, focus rings, color changes | `ease-out` |
| Fast | 200ms | Buttons, toggles, hover lifts | `ease-out` |
| Medium | 300ms | Card reveals, panel slides, nav transitions | `cubic-bezier(0.16, 1, 0.3, 1)` |
| Slow | 500ms | Hero text entrance, section reveals | `cubic-bezier(0.16, 1, 0.3, 1)` |
| Dramatic | 800ms | Full-viewport reveals, scroll sequences | `cubic-bezier(0.215, 0.61, 0.355, 1)` |

**Stagger increments:** 50ms, 80ms, 100ms, 120ms. Pick one per animation group and use it consistently.

**Why this matters:** A constrained timing palette is what makes animations feel "designed" rather than "AI-generated." Five levels is enough to cover any UI pattern.

---

## Gemini Prompt Injection Guide

These rules are injected into the Gemini prompt built in Phase 7. They go BEFORE the REQUIREMENTS section.

### Section: FORBIDDEN PATTERNS
Include the full forbidden patterns table above, rephrased as direct instructions:
```
Do NOT use emoji as placeholders for images or icons.
Do NOT use external placeholder URLs (unsplash, picsum, placeholder.com, etc.).
Do NOT write Lorem ipsum — use the exact text provided in the HTML CONTENT section.
Do NOT add visual effects (glows, gradients, shadows) not present in the original.
Do NOT use external font CDN URLs — all fonts must be self-hosted in public/fonts/.
```

### Section: ANIMATION IMPLEMENTATION MATRIX
Include the decision matrix table. Prefix with:
```
Use the following matrix to choose animation tools. The ANIMATIONS section above
tells you WHAT animations exist. This matrix tells you HOW to implement them.
```

### Section: PERFORMANCE RULES
Include GPU-only properties list and mobile rules. Prefix with:
```
These performance rules are mandatory. Violating them causes visible jank.
```

### Section: EASING REFERENCE
Include spring and cubic-bezier tables. Prefix with:
```
When the ANIMATIONS section specifies easing values, use them exactly.
When easing data is missing or ambiguous, use these production-quality defaults.
```
