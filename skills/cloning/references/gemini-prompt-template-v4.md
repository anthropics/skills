# Gemini Prompt Template v6.0

This template shows the enhanced prompt structure for cloningv2, achieving 98-100% fidelity.

## What's New in v6.0

| Improvement | v3.0 | v6.0 |
|-------------|------|------|
| Framework Detection | None | Automatic (Tailwind, GSAP, etc.) |
| Color Confidence | All equal | HIGH/MEDIUM/LOW scoring |
| Layout Analysis | Basic | Full Grid/Flex/Z-index |
| Component Mapping | Pattern detection | ARIA + semantic analysis |
| Icon Extraction | None | Full SVG capture |
| Animation Config | Library detection | Full ScrollTrigger config |

---

## Template Structure

The v6.0 prompt follows this structure:

```markdown
# CLONE REQUEST: {url}

## SITE ANALYSIS (Pre-computed)
- Frameworks detected (CSS, Animation, Icons, Components)
- UI Patterns found (sticky nav, modals, accordions, etc.)

## LAYOUT STRUCTURE
- Primary layout method (Grid vs Flexbox)
- Grid/Flexbox configurations
- Z-index stacking layers
- Responsive breakpoints

## COMPUTED MEASUREMENTS (from extract_computed_measurements.js)
- Header: height, maxWidth, padding
- Hero h1: fontSize, lineHeight, maxWidth, letterSpacing
- Container: maxWidth, paddingLeft/Right
- Logo bar: item count, gap, item height
- Grid sections: columns, gap, child aspect-ratio
- Footer: maxWidth, padding, column layout
*Use these exact values for Tailwind classes (e.g., h-[52px], max-w-[1496px], px-8)*

## HTML CONTENT (from extract_html_content.js)
- Hero heading innerHTML (preserves <br>, <span> tags — use EXACTLY)
- Nav links: [{text, href}]
- Logo/partner images: [{src (CDN URL), alt}]
- Footer columns: [{heading, links: [{text, href}]}]
- Product cards: [{title, subtitle, imageSrc, link}]

## COMPONENT MAP
- ARIA landmarks
- Detected component patterns
- Section structure with purposes

## DESIGN SYSTEM (Confidence-Scored)
- HIGH confidence colors (brand, CTAs, hero)
- MEDIUM confidence colors (interactive elements)
- Typography with font manifest (URLs, from extract_font_assets.js)
- Font Manifest: [{family, weights, sources: [{url, format}], isVariable}]
- Body text-rendering, font-feature-settings, font-kerning
- Heading font-variation-settings
- Spacing scale
- Visual effects (shadows, radius, gradients)
- CSS variables

## ANIMATIONS (Exact Values)
- Library to use (GSAP, Framer Motion, etc.)
- Timing constants (premium easing, durations)
- ScrollTrigger configurations
- @Keyframes definitions
- Hover transitions

## ANIMATION SPECIFICATIONS (from JS Bundle Analysis)

{bundleAnalysisOutput}

### Libraries Detected (from imports, not window globals)
{libraries}

### ScrollTrigger Configurations
{scrollTriggers}

### Text Animation Configs (SplitText)
{splitTextConfigs}

### Easing Signature
{easingSignature}

### Stagger Patterns
{staggers}

### clipPath Reveals
{clipPaths}

**IMPORTANT:** When bundle analysis data is present, use it as the authoritative
source for animation implementation. Implement with GSAP (not CSS @keyframes)
when ScrollTrigger configs are found.

## SVG / ICONS
- Detected icon library
- Inline SVG count
- Logo SVG capture
- Icon examples

## FORBIDDEN PATTERNS (violations = output FAILS quality gate)
Do NOT use emoji as placeholders for images or icons — use downloaded assets from DOWNLOADED ASSETS section.
Do NOT use external placeholder URLs (unsplash.com, picsum.photos, placehold.co, via.placeholder.com, lorempixel.com, dummyimage.com, lorem.space).
Do NOT write Lorem ipsum or any placeholder text — use the exact text from HTML CONTENT section above.
Do NOT add wireframe gray boxes where images should be — use <img src="/images/..."> with local assets.
Do NOT add visual effects not present in the original (neon glows, gradient text, oversaturated colors, extra shadows).
Do NOT use default shadcn/Radix component styling without customizing to match the original's design tokens.
Do NOT include comments like "// Add more items here" or "// TODO" — all sections must be complete.
Do NOT use external font CDN URLs (fonts.googleapis.com, fonts.gstatic.com) — self-host all fonts in public/fonts/.
Do NOT use hardcoded #000000 pure black unless the DESIGN SYSTEM section shows it — use the exact dark color captured.

## ANIMATION REQUIREMENTS (NON-NEGOTIABLE when GSAP detected on original)

If the SITE ANALYSIS section shows GSAP or ScrollTrigger detected, you MUST:
1. Install gsap: add `"gsap": "^3.12.0"` to package.json dependencies
2. Use GSAP ScrollTrigger for ALL scroll-triggered animations — do NOT substitute IntersectionObserver
3. Use the EXACT patterns below — do NOT simplify or replace with CSS

### GSAP Pattern: Word-by-Word Scroll Reveal
When the original has text that reveals word-by-word on scroll:
```tsx
"use client";
import { useEffect, useRef } from "react";
import { gsap } from "gsap";
import { ScrollTrigger } from "gsap/ScrollTrigger";
if (typeof window !== "undefined") gsap.registerPlugin(ScrollTrigger);

// Split text into words, animate opacity from 0.15 to 1 with scrub
const words = containerRef.current.querySelectorAll(".word");
gsap.fromTo(words, { opacity: 0.15 }, {
  opacity: 1, stagger: 0.02, ease: "none",
  scrollTrigger: { trigger: container, start: "top 80%", end: "bottom 30%", scrub: 0.5 }
});
```

### GSAP Pattern: Auto-Cycling Tabs with Timer Bar
When the original has tabs that auto-advance with a progress indicator:
```tsx
// Use gsap.to with onUpdate for smooth progress bar, onComplete to cycle
gsap.to({ value: 0 }, {
  value: 100, duration: 6, ease: "none",
  onUpdate() { setProgress(this.targets()[0].value); },
  onComplete() { setActiveIndex((prev + 1) % tabs.length); }
});
```

### GSAP Pattern: Sticky Timeline with Scroll-Linked Active Step
When the original has a sticky sidebar that tracks scroll position:
```tsx
// One ScrollTrigger per step, updates active index on enter/enterBack
ScrollTrigger.create({
  trigger: stepElement,
  start: "top 55%", end: "bottom 45%",
  onEnter: () => setActiveIndex(i),
  onEnterBack: () => setActiveIndex(i),
});
```

### When NOT to use GSAP (CSS is fine for these):
- Simple hover transitions → CSS :hover
- Continuous loops (spinners) → CSS @keyframes infinite
- Basic fade-in on viewport entry (if original uses NO animation library) → IntersectionObserver

CONFLICT RULE: NEVER import both gsap and framer-motion in the same component file.

## PERFORMANCE RULES (mandatory — violating causes visible jank)
ONLY animate these GPU-composited properties: transform, opacity, filter, clip-path.
NEVER directly animate: width, height, top, left, margin, padding, font-size (triggers layout recalculation).
Add prefers-reduced-motion media query to globals.css.
On mobile (pointer: coarse): disable parallax and 3D tilt effects.
Use will-change ONLY during animation, remove after — never set permanently.
Isolate perpetual/looping animations in React.memo leaf components.
Every useEffect with GSAP or IntersectionObserver MUST return a cleanup function.

## EASING REFERENCE (use when extracted easing is ambiguous)
Framer Motion Springs:
- Snappy (buttons): { stiffness: 300, damping: 30 }
- Smooth (modals): { stiffness: 150, damping: 20 }
- Bouncy (playful): { stiffness: 100, damping: 10 }
- Gentle (pages): { stiffness: 80, damping: 15 }

CSS Cubic-Bezier:
- Decelerate: cubic-bezier(0.0, 0.0, 0.2, 1.0)
- Accelerate: cubic-bezier(0.4, 0.0, 1.0, 1.0)
- Standard: cubic-bezier(0.4, 0.0, 0.2, 1.0)
- Premium: cubic-bezier(0.215, 0.61, 0.355, 1)
- Elastic: cubic-bezier(0.68, -0.55, 0.265, 1.55)

When the ANIMATIONS section specifies exact easing values, use them. These are fallbacks only.

## TYPESCRIPT RULES (mandatory — violations prevent compilation)
Every `useRef` call MUST include an initial value: `useRef<HTMLDivElement>(null)`, never bare `useRef<T>()`.
Every `useState` with a non-primitive type MUST include an initial value: `useState<string[]>([])`, `useState<Data | null>(null)`.
Every event handler parameter MUST be typed: `(e: React.MouseEvent<HTMLButtonElement>)`, never bare `(e)`.
Do NOT use `any` type — use `unknown` and narrow, or define a proper interface.
All component props MUST have an interface or type alias — never inline object types in function signatures.
When accessing optional properties, use optional chaining: `data?.field` not `data.field`.

## SHARED PATTERNS (mandatory — reduces bundle size and maintenance burden)
If the same code pattern appears in 3+ components, extract it into a shared hook or utility:
- IntersectionObserver reveal pattern → extract as `useReveal()` hook in `hooks/useReveal.ts`
- GSAP ScrollTrigger setup/cleanup → extract as `useScrollTrigger()` hook in `hooks/useScrollTrigger.ts`
- Responsive breakpoint detection → extract as `useBreakpoint()` hook
- Staggered animation delay calculation → extract as utility function
Create a `hooks/` directory for shared React hooks. Each hook must include TypeScript types and cleanup logic in useEffect return.

## CONSISTENT TIMING SCALE (use when Phase 6 doesn't provide exact durations)
When Phase 6 provides exact durations from the original site, use those values faithfully.
When durations must be chosen (Phase 6 data missing or ambiguous), use this scale:
- Micro (tooltips, focus rings): 100ms
- Fast (buttons, toggles, hover): 200ms
- Medium (cards, panels, reveals): 300ms
- Slow (hero entrances, section reveals): 500ms
- Dramatic (full-viewport sequences): 800ms
All stagger delays should be multiples of 50ms (50ms, 80ms, 100ms, 150ms).
Do NOT mix arbitrary values like 75ms, 250ms, 450ms when choosing durations.

## FILES TO CREATE
- Explicit list of component files

## ANIMATION IMPLEMENTATION
- Code template for the detected animation library

## ORIGINAL HTML STRUCTURE
- Complete cleaned HTML

## REQUIREMENTS
- Exact specifications for the clone
- FONT SELF-HOSTING: Download all .woff2 files from font manifest to public/fonts/. Use local paths in @font-face (e.g., /fonts/SanaSans-Variable.woff2). NEVER use external font URLs — CORS blocks them.
- ANIMATION RULE: Default to CSS @keyframes for fade/slide/stagger. Only use GSAP if site has scroll-linked scrub or pinned sections. GSAP + React 18 Strict Mode breaks animations.
- MEASUREMENTS: Use exact values from COMPUTED MEASUREMENTS section for Tailwind classes (h-[52px], max-w-[1496px], etc.)
- HTML CONTENT: Use exact innerHTML from HTML CONTENT section — preserve <br> tags, image CDN URLs, link hrefs.
- CODE QUALITY: Output must pass Phase 9.5 quality gate — no placeholder URLs, no emoji placeholders, all referenced images must exist as local files, no mixed GSAP+Framer imports per component.
```

---

## Why Each Section Matters

### SITE ANALYSIS
Tells Gemini exactly which libraries to use. Without this, Gemini might:
- Use Framer Motion when the site uses GSAP
- Generate Bootstrap classes when the site uses Tailwind
- Miss the icon library entirely

### LAYOUT STRUCTURE
Without layout analysis:
- Gemini might use Flexbox for a Grid layout
- Z-index layers would be wrong (modals behind content)
- Responsive behavior would be guessed

### CONFIDENCE-SCORED COLORS
Brand colors matter more than generic grays:
- HIGH: Logo, primary CTA, hero background → Must be exact
- MEDIUM: Nav, buttons, cards → Should be close
- LOW: Generic borders, subtle backgrounds → Can approximate

### ANIMATION CONFIG
The most impactful improvement. v3.0 just detected "uses GSAP". v4.0 captures:
- Exact ScrollTrigger start/end values
- Stagger timing
- Easing functions (cubic-bezier values)
- Duration patterns

---

## Optimal Gemini 3 Parameters

Based on Google's recommendations:

```python
generation_config = {
    "temperature": 1.0,      # Google's recommended default
    "max_output_tokens": 65536,
    "topP": 0.95
}
```

### Why These Values?

- **temperature: 1.0** - Gemini 3 works best at its default temperature. Lower values can reduce creativity in code structure.

- **max_output_tokens: 65536** - Large enough for complex sites with many components. Gemini 3.1 Pro can output up to 65K tokens.

- **topP: 0.95** - Allows some variation while staying focused.

---

## Multimodal Content Order

Order matters for Gemini's understanding:

1. **Text prompt first** - Full context before media
2. **Scroll video (MANDATORY)** - Shows all scroll-triggered animations in motion
3. **Interaction video (MANDATORY)** - Shows component state transitions (tabs, steps, carousels)
4. **Hover video (MANDATORY)** - Shows hover state transitions
5. **Full-page desktop screenshot** - Overall layout understanding
6. **Section close-up screenshots** - Per-component detail (up to 12)
7. **Viewport screenshots** - Different responsive views (mobile, tablet, wide)
8. **Interactive state screenshots** - From Phase 0.5

IMPORTANT: Videos show the EXACT animation timing, easing, and visual effects.
Match them precisely. If a video shows a gold square sliding down a timeline,
implement that exact slide motion — not a fade, not a scale, the exact movement shown.

```python
parts = [
    {"text": prompt},
    # MANDATORY: 3 animation videos
    {"inline_data": {"mime_type": "video/webm", "data": scroll_video_base64}},
    {"inline_data": {"mime_type": "video/webm", "data": interaction_video_base64}},
    {"inline_data": {"mime_type": "video/webm", "data": hover_video_base64}},
    # Full-page + section close-ups
    {"inline_data": {"mime_type": "image/png", "data": full_page_base64}},
    # ... section close-ups
    {"inline_data": {"mime_type": "image/png", "data": section_hero_base64}},
    {"inline_data": {"mime_type": "image/png", "data": section_features_base64}},
    # ... viewport screenshots
    {"inline_data": {"mime_type": "image/png", "data": mobile_base64}},
    {"inline_data": {"mime_type": "image/png", "data": tablet_base64}},
    {"inline_data": {"mime_type": "image/png", "data": desktop_base64}},
]
```

---

## Example v4.0 Prompt (Abbreviated)

```markdown
# CLONE REQUEST: https://escape.cafe

## SITE ANALYSIS (Pre-computed)

### Frameworks Detected
- CSS: custom (minimal Tailwind patterns)
- Animation: gsap + scrollTrigger
- Icons: inline-svg
- Components: custom

### UI Patterns Found
- Has StickyNav
- Has Dropdown
- Has Carousel
- Has PricingTable

## LAYOUT STRUCTURE

### Primary Layout: flexbox

### Grid Usage
- .product-grid: columns=repeat(3, 1fr), gap=24px
- .footer-links: columns=repeat(4, 1fr), gap=32px

### Z-Index Layers
- nav.sticky: z-index=50 (position + z-index)
- .modal-backdrop: z-index=40 (position + z-index)

### Responsive Breakpoints
- 375px (min)
- 768px (min)
- 1024px (min)
- 1440px (min)

## DESIGN SYSTEM (Confidence-Scored)

### Colors (HIGH CONFIDENCE - Brand Critical)
- #F5F4F2: body.main (used 45x)
- #151515: h1.hero-title (used 120x)
- #ff2300: button.cta-primary (used 8x)

### Colors (MEDIUM CONFIDENCE - Interactive)
- #EBE9E6: div.product-card (used 24x)
- #D5D3D0: div.product-card:hover (hover state)

### Typography
- Primary Font: TWK Lausanne
- Heading Font: Garaje
- Font Weights: 200, 300, 350, 400, 700
- Font Sizes: 12px, 14px, 16px, 18px, 24px, 36px, 48px, 72px

### Font Manifest (with URLs)
- TWK Lausanne: weights [200, 300, 350, 400]
  - 200: https://escape.cafe/cdn/shop/t/9/assets/twklausanne-200-webfont.woff2
  - 300: https://escape.cafe/cdn/shop/t/9/assets/twklausanne-300-webfont.woff2
  - 350: https://escape.cafe/cdn/shop/t/9/assets/twklausanne-350-webfont.woff2
  - 400: https://escape.cafe/cdn/shop/t/9/assets/twklausanne-400-webfont.woff2
- Garaje: weights [700]
  - 700: https://escape.cafe/cdn/shop/t/9/assets/garaje-bold-webfont.woff2

## ANIMATIONS (Exact Values)

### Animation Library: gsap + scrollTrigger

### Timing Constants
- Premium Easing: cubic-bezier(0.215, 0.61, 0.355, 1)
- Durations: 0.3s, 0.4s, 0.6s, 0.8s, 1.0s
- Staggers:
  - .product-grid: stagger=0.12s
  - .footer-columns: stagger=0.15s

### ScrollTriggers / Scroll Animations
- .hero-title: start="top 80%", scrub=false
- .product-card: start="top 90%", scrub=false
- .polaroid-image: start="top bottom", scrub=true (parallax)

## FILES TO CREATE

- app/page.tsx
- app/layout.tsx
- app/globals.css
- components/Header.tsx
- components/Hero.tsx
- components/Collections.tsx
- components/BrandStory.tsx
- components/NeverRunOut.tsx
- components/Footer.tsx
- tailwind.config.ts
- package.json (with gsap dependency)

## ANIMATION IMPLEMENTATION

### GSAP Implementation Required

Use this pattern for scroll animations:
```tsx
"use client";
import { useLayoutEffect, useRef } from "react";
import gsap from "gsap";
import { ScrollTrigger } from "gsap/ScrollTrigger";

if (typeof window !== "undefined") {
  gsap.registerPlugin(ScrollTrigger);
}
// ... (full GSAP pattern)
```

## ORIGINAL HTML STRUCTURE

[Complete HTML here]
```

---

## Expected Output Quality

With the v4.0 template, Gemini produces:

| Aspect | v3.0 Output | v4.0 Output |
|--------|-------------|-------------|
| Animation library | Sometimes wrong | Always correct |
| Hover colors | Approximate | Exact hex values |
| Layout method | Often wrong | Correct Grid/Flex |
| Z-index layers | Missing | Correctly stacked |
| Font weights | Missing thin/light | All weights present |
| Icon reproduction | Generic icons | Exact SVGs |
| Responsive breakpoints | Guessed | Exact from analysis |

**Target: 98-100% visual fidelity without manual polish**

---

## Troubleshooting

### Gemini returns incomplete output
- Switch from Flash to Pro for complex sites
- Reduce HTML size if >100KB
- Split into section-by-section generation

### Animation library mismatch
- Check detect_frameworks.js output
- Verify library is actually in the page scripts

### Colors don't match
- Check HIGH confidence colors in design tokens
- Verify no color transformations (hover states)

### Layout is wrong
- Check analyze_layout.js output
- Verify Grid vs Flexbox detection is correct
- Check z-index layers for overlapping issues
