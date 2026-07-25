# Design System: Taste Standard
**Skill:** stitch-design-taste

---

## Configuration — Set Your Style
Adjust these dials before using this design system. They control how creative, dense, and animated the output should be. Pick the level that fits your project.

| Dial | Level | Description |
|------|-------|-------------|
| **Creativity** | `8` | `1` = Ultra-minimal, Swiss, silent, monochrome. `5` = Balanced, clean but with personality. `10` = Expressive, editorial, bold typography experiments, inline images in headlines, strong asymmetry. Default: `8` |
| **Density** | `4` | `1` = Gallery-airy, massive whitespace. `5` = Balanced sections. `10` = Cockpit-dense, data-heavy. Default: `4` |
| **Variance** | `8` | `1` = Predictable, symmetric grids. `5` = Subtle offsets. `10` = Artsy chaotic, no two sections alike. Default: `8` |
| **Motion Intent** | `6` | `1` = Static, no animation noted. `5` = Subtle hover/entrance cues. `10` = Cinematic orchestration noted in every component. Default: `6` |

> **How to use:** Change the numbers above to match your project's vibe. At **Creativity 1–3**, the system produces clean, quiet, Notion-like interfaces. At **Creativity 7–10**, expect inline image typography, dramatic scale contrast, and strong editorial layouts. The rest of the rules below adapt to your chosen levels.

---

## 1. Visual Theme & Atmosphere
A restrained, gallery-airy interface with confident asymmetric layouts and fluid spring-physics motion. The atmosphere is clinical yet warm — like a well-lit architecture studio where every element earns its place through function. Density is balanced (Level 4), variance runs high (Level 8) to prevent symmetrical boredom, and motion is fluid but never theatrical (Level 6). The overall impression: expensive, intentional, alive.

## 2. Color Palette & Roles
- **Canvas White** (#F9FAFB) — Primary background surface. Warm-neutral, never clinical blue-white
- **Pure Surface** (#FFFFFF) — Card and container fill. Used with whisper shadow for elevation
- **Charcoal Ink** (#18181B) — Primary text. Zinc-950 depth — never pure black
- **Steel Secondary** (#71717A) — Body text, descriptions, metadata. Zinc-500 warmth
- **Muted Slate** (#94A3B8) — Tertiary text, timestamps, disabled states
- **Whisper Border** (rgba(226,232,240,0.5)) — Card borders, structural 1px lines. Semi-transparent for depth
- **Diffused Shadow** (rgba(0,0,0,0.05)) — Card elevation. Wide-spreading, 40px blur, -15px offset. Never harsh

### Accent Selection (Pick ONE per project)
- **Emerald Signal** (#10B981) — For growth, success, positive data dashboards
- **Electric Blue** (#3B82F6) — For productivity, SaaS, developer tools
- **Deep Rose** (#E11D48) — For creative, editorial, fashion-adjacent projects
- **Amber Warmth** (#F59E0B) — For community, social, warm-toned products

### Banned Colors
- Purple/Violet neon gradients — the "AI Purple" aesthetic
- Pure Black (#000000) — always Off-Black or Zinc-950
- Oversaturated accents above 80% saturation
- Mixed warm/cool gray systems within one project

## 3. Typography Rules
- **Display:** `Geist`, `Satoshi`, `Cabinet Grotesk`, or `Outfit` — Track-tight (`-0.025em`), controlled fluid scale, weight-driven hierarchy (700–900). Not screaming. Leading compressed (`1.1`). Alternatives forced — `Inter` is BANNED for premium contexts
- **Body:** Same family at weight 400 — Relaxed leading (`1.65`), 65ch max-width, Steel Secondary color (#71717A)
- **Mono:** `Geist Mono` or `JetBrains Mono` — For code blocks, metadata, timestamps. When density exceeds Level 7, all numbers switch to monospace
- **Scale:** Display at `clamp(2.25rem, 5vw, 3.75rem)`. Body at `1rem/1.125rem`. Mono metadata at `0.8125rem`

### Banned Fonts
- `Inter` — banned everywhere in premium/creative contexts
- Generic serif fonts (`Times New Roman`, `Georgia`, `Garamond`, `Palatino`) — BANNED. If serif is needed for editorial/creative, use only distinctive modern serifs like `Fraunces`, `Gambarino`, `Editorial New`, or `Instrument Serif`. Never use default browser serif stacks. Serif is always BANNED in dashboards or software UIs regardless

## 4. Component Stylings
* **Buttons:** Flat surface, no outer glow. Primary: accent fill with white text. Secondary: ghost/outline. Active state: `-1px translateY` or `scale(0.98)` for tactile push. Hover: subtle background shift, never glow
* **Cards/Containers:** Generously rounded corners (`2.5rem`). Pure white fill. Whisper border (`1px`, semi-transparent). Diffused shadow (`0 20px 40px -15px rgba(0,0,0,0.05)`). Internal padding `2rem–2.5rem`. Used ONLY when elevation communicates hierarchy — high-density layouts replace cards with `border-top` dividers or negative space
* **Inputs/Forms:** Label positioned above input. Helper text optional. Error text below in Deep Rose. Focus ring in accent color, `2px` offset. No floating labels. Standard `0.5rem` gap between label-input-error stack
* **Navigation:** Sleek, sticky. Icons scale on hover (Dock Magnification optional). No hamburger on desktop. Clean horizontal with generous spacing
* **Loaders:** Skeletal shimmer matching exact layout dimensions and rounded corners. Shifting light reflection across placeholder shapes. Never circular spinners
* **Empty States:** Composed illustration or icon composition with guidance text. Never just "No data found"
* **Error States:** Inline, contextual. Red accent underline or border. Clear recovery action

## 5. Hero Section
The Hero is the first impression — it must be striking, creative, and never generic.
- **Inline Image Typography:** Embed small, contextual photos or visuals directly between words or letters in the headline. Example: "We build [photo of hands typing] digital [photo of screen] products" — images sit inline at type-height, rounded, acting as visual punctuation between words. This is the signature creative technique
- **No Overlapping Elements:** Text must never overlap images or other text. Every element has its own clear spatial zone. No z-index stacking of content layers, no absolute-positioned headlines over images. Clean separation always
- **No Filler Text:** "Scroll to explore", "Swipe down", scroll arrow icons, bouncing chevrons, and any instructional UI chrome are BANNED. The user knows how to scroll. Let the content pull them in naturally
- **Asymmetric Structure:** Centered Hero layouts are BANNED at this variance level. Use Split Screen (50/50), Left-Aligned text / Right visual, or Asymmetric Whitespace with large empty zones
- **CTA Restraint:** Maximum one primary CTA button. No secondary "Learn more" links. No redundant micro-copy below the headline

## 6. Layout Principles
- **Grid-First:** CSS Grid for all structural layouts. Never flexbox percentage math (`calc(33% - 1rem)` is BANNED)
- **No Overlapping:** Elements must never overlap each other. No absolute-positioned layers stacking content on content. Every element occupies its own grid cell or flow position. Clean, separated spatial zones
- **Feature Sections:** The "3 equal cards in a row" pattern is BANNED. Use 2-column Zig-Zag, asymmetric Bento grids (2fr 1fr 1fr), or horizontal scroll galleries
- **Containment:** All content within `max-width: 1400px`, centered. Generous horizontal padding (`1rem` mobile, `2rem` tablet, `4rem` desktop)
- **Full-Height:** Use `min-height: 100dvh` — never `height: 100vh` (iOS Safari address bar jump)
- **Bento Architecture:** For feature grids, use Row 1: 3 columns | Row 2: 2 columns (70/30 split). Each tile contains a perpetual micro-animation

## 7. Responsive Rules
Every screen must work flawlessly across all viewports. **Responsive is not optional — it is a hard requirement. Every single element must be tested at 375px, 768px, and 1440px.**
- **Mobile-First Collapse (< 768px):** All multi-column layouts collapse to a strict single column. `width: 100%`, `padding: 1rem`, `gap: 1.5rem`. No exceptions
- **No Horizontal Scroll:** Horizontal overflow on mobile is a critical failure. All elements must fit within viewport width. If any element causes horizontal scroll, the design is broken
- **Typography Scaling:** Headlines scale down gracefully via `clamp()`. Body text stays `1rem` minimum. Never shrink body below `14px`. Headlines must remain readable on 375px screens
- **Touch Targets:** All interactive elements minimum `44px` tap target. Generous spacing between clickable items. Buttons must be full-width on mobile
- **Image Behavior:** Hero and inline images scale proportionally. Inline typography images (photos between words) stack below the headline on mobile instead of inline
- **Navigation:** Desktop horizontal nav collapses to a clean mobile menu (slide-in or full-screen overlay). No tiny hamburger icons without labels
- **Cards & Grids:** Bento grids and asymmetric layouts revert to stacked single-column cards with full-width. Maintain internal padding (`1rem`)
- **Spacing Consistency:** Vertical section gaps reduce proportionally on mobile (`clamp(3rem, 8vw, 6rem)`). Never cramped, never excessively airy
- **Testing Viewports:** Designs must be verified at: `375px` (iPhone SE), `390px` (iPhone 14), `768px` (iPad), `1024px` (small laptop), `1440px` (desktop)

## 8. Motion & Interaction (Code-Phase Intent)
> **Note:** Stitch generates static screens — it does not animate. This section documents the **intended motion behavior** so that the coding agent (Antigravity, Cursor, etc.) knows exactly how to implement animations when building the exported design into a live product.

- **Physics Engine:** Spring-based exclusively. `stiffness: 100, damping: 20`. No linear easing anywhere. Premium, weighty feel on all interactive elements
- **Perpetual Micro-Loops:** Every active dashboard component has an infinite-loop state — Pulse on status dots, Typewriter on search bars, Float on feature icons, Shimmer on loading states
- **Staggered Orchestration:** Lists and grids mount with cascaded delays (`animation-delay: calc(var(--index) * 100ms)`). Waterfall reveals, never instant mount
- **Layout Transitions:** Smooth re-ordering via shared element IDs. Items swap positions with physics, simulating real-time intelligence
- **Hardware Rules:** Animate ONLY `transform` and `opacity`. Never `top`, `left`, `width`, `height`. Grain/noise filters on fixed, pointer-events-none pseudo-elements only
- **Performance:** CPU-heavy perpetual animations isolated in microscopic leaf components. Never trigger parent re-renders. Target 60fps minimum

## 9. Anti-Patterns (Banned)
- No emojis — anywhere in UI, code, or alt text
- No `Inter` font — use `Geist`, `Outfit`, `Cabinet Grotesk`, `Satoshi`
- No generic serif fonts (`Times New Roman`, `Georgia`, `Garamond`) — if serif is needed, use distinctive modern serifs only (`Fraunces`, `Instrument Serif`)
- No pure black (`#000000`) — Off-Black or Zinc-950 only
- No neon outer glows or default box-shadow glows
- No oversaturated accent colors above 80%
- No excessive gradient text on large headers
- No custom mouse cursors
- No overlapping elements — text never overlaps images or other content. Clean spatial separation always
- No 3-column equal card layouts for features
- No centered Hero sections (at this variance level)
- No filler UI text: "Scroll to explore", "Swipe down", "Discover more below", scroll arrows, bouncing chevrons — all BANNED
- No generic names: "John Doe", "Sarah Chan", "Acme", "Nexus", "SmartFlow"
- No fake round numbers: `99.99%`, `50%`, `1234567` — use organic data: `47.2%`, `+1 (312) 847-1928`
- No AI copywriting clichés: "Elevate", "Seamless", "Unleash", "Next-Gen", "Revolutionize"
- No broken Unsplash links — use `picsum.photos/seed/{id}/800/600` or SVG UI Avatars
- No generic `shadcn/ui` defaults — customize radii, colors, shadows to match this system
- No `z-index` spam — use only for Navbar, Modal, Overlay layer contexts
- No `h-screen` — always `min-h-[100dvh]`
- No circular loading spinners — skeletal shimmer only
