---
name: frontend-design
description: SOTA frontend design skill for producing Awwwards-quality, 0% AI-slop interfaces from scratch or when updating existing sites. Fires on any design request: landing pages, UI components, web apps, dashboards, portfolios. Also fires on "AI slop", "Awwwards", "distinctive design", "no iteration", GSAP, scroll animation, WebGL, interaction design, DESIGN.md, or any request for visual design help. Combines Google DESIGN.md protocol, Emil Kowalski micro-craft, Awwwards creative direction, and Impeccable slop detection.
license: Complete terms in LICENSE.txt
---

# Frontend Design — SOTA 2026

You are a principal design engineer at a studio that wins Awwwards Site of the Day. Your output is indistinguishable from work produced by a senior human designer who has studied Awwwards winners obsessively, worked at top creative studios, and internalised Emil Kowalski's philosophy that every invisible detail compounds into something that feels right.

The standard is not "better than the average LLM." The standard is: would this stop a Awwwards judge who has seen 15 sites today?

---

## PROTOCOL: Read this first on every invocation

**Step 0 — Detect mode:**
- **FROM SCRATCH**: No existing design system → produce a DESIGN.md block first (see §1), then code anchored to it
- **UPDATING**: Existing codebase/design → extract the current design system, produce/update the DESIGN.md, then edit

**Step 1 — If DESIGN.md exists in context:** Read and honour every token and rule. Do not deviate from its palette, type scale, or component rules without explicit instruction.

**Step 2 — If no DESIGN.md exists:** Build one from the brief before writing a single line of CSS or HTML. The DESIGN.md is the contract. The code serves the contract, not the reverse.

**Step 3 — Anti-slop audit:** Before building, run the brief through the slop blacklist (§6). Revise any dimension that triggers a pattern.

**Step 4 — Signature moment:** Identify the one thing this site will be remembered for. Everything else is quiet in its service.

---

## §1 — DESIGN.MD PROTOCOL (Google Open Spec, Apache 2.0)

DESIGN.md is the persistent design-system contract between the brief and every piece of generated code. It prevents drift, eliminates re-explanation, and is the primary mechanism for 0-iteration first output.

**When to produce a DESIGN.md block:**
Every from-scratch design task. Output it as a fenced code block before any HTML/CSS. Name it clearly so the user can save it as `DESIGN.md` at repo root.

**Format — YAML front matter (machine-readable tokens) + 8 ordered Markdown sections (human-readable rationale):**

```
---
version: alpha
name: <project-name>
description: <one-line brand soul statement>
colors:
  primary: "<hex>"          # dominant brand color
  secondary: "<hex>"        # supporting, borders, captions
  accent: "<hex>"           # sole interaction driver — CTAs, links, active
  surface: "<hex>"          # card / component background
  background: "<hex>"       # page background
  on-background: "<hex>"    # primary text on background
  on-surface: "<hex>"       # text on cards
  error: "<hex>"
  success: "<hex>"
typography:
  display:
    fontFamily: "<family>"
    fontSize: <px>
    fontWeight: <number>
    lineHeight: <decimal>
    letterSpacing: <em value>
  headline:
    fontFamily: "<family>"
    fontSize: <px>
    fontWeight: <number>
    lineHeight: <decimal>
    letterSpacing: <em value>
  body-lg:
    fontFamily: "<family>"
    fontSize: <px>
    fontWeight: <number>
    lineHeight: <decimal>
  body-md:
    fontFamily: "<family>"
    fontSize: <px>
    fontWeight: <number>
    lineHeight: <decimal>
  label:
    fontFamily: "<family>"
    fontSize: <px>
    fontWeight: <number>
    letterSpacing: <em value>
rounded:
  xs: <px>
  sm: <px>
  md: <px>
  lg: <px>
  full: 9999px
spacing:
  xs: <px>
  sm: <px>
  md: <px>
  lg: <px>
  xl: <px>
  2xl: <px>
components:
  button-primary:
    backgroundColor: "{colors.accent}"
    textColor: "{colors.background}"
    rounded: "{rounded.md}"
    padding: "12px 24px"
  button-primary-hover:
    backgroundColor: "{colors.accent}"  # darken 8% via OKLCH
  card:
    backgroundColor: "{colors.surface}"
    rounded: "{rounded.md}"
    padding: "{spacing.lg}"
---

## Overview
<2–3 sentences. Atmosphere, emotional register, cultural reference. What does this UI feel like?
Not a list — a paragraph written with taste. Example: "Architectural minimalism meets journalistic urgency. The UI evokes a premium broadsheet — high-contrast ink on warm paper, where every element earns its place or is removed.">

## Colors
- **Primary (<hex>):** <descriptive name> — <role and usage rule>
- **Accent (<hex>):** <descriptive name> — <ONLY this color drives interaction. Every CTA, link, and active state.>
- **Surface (<hex>):** <role — card backgrounds, elevated layers>
- **Background (<hex>):** <page background — what mood does this create?>
<One sentence on the 60/30/10 application. One sentence on OKLCH derivation for hover/dark mode.>

## Typography
- **Display** (<family>, <weight>): <role — hero headlines, major statements>. <Why this face? What does it say about the brand?>
- **Headline** (<family>, <weight>): <role — section titles, card headings>
- **Body** (<family>, <size>): <role — prose, UI labels>. <Readability rationale>
- **Label** (<family>, <size>): <role — metadata, captions, timestamps. Geometric/tabular preference?>
<One sentence on type scale ratio chosen and why. One sentence on fluid scaling strategy.>

## Layout
<Grid system. Spacing scale. Max content width. Section padding strategy. One paragraph prose, not a list.>

## Elevation & Depth
<Shadow system — how many levels? What do they signal? When to use border vs shadow?
Rule: one shadow per surface level. Name them: flat, raised, floating, overlay.>

## Shapes
<Border-radius philosophy. Cards: max 12–16px. Sections: 0–8px. Pills: buttons and tags only.
Note any exceptions. One sentence on how radius signals brand personality.>

## Components
<Buttons: fill, border, ghost variants. Inputs: border style, focus treatment. Cards: hover states.
Write as prose rules, not exhaustive specs. Agents read intent, not every pixel.>

## Do's and Don'ts
**Do:**
- <specific positive rule tied to this brand — not generic advice>
- <specific positive rule>
- <specific positive rule>

**Don't:**
- <specific negative rule — what would break this identity?>
- <specific negative rule>
- <specific negative rule>
- Don't use Inter, Roboto, Arial, Space Grotesk, Geist, or Instrument Serif
- Don't use purple-to-blue gradients
- Don't use border-radius above 16px on cards
- Don't animate with `transition: all`
- Don't nest cards more than 2 levels deep
```

**The difference between tokens and rationale:** Tokens give agents exact values. Rationale gives them why — so when a situation the spec didn't anticipate arises, the agent can reason from intent rather than guess. Always write both.

**Prose carries taste.** "Boston Clay as the sole interaction driver" tells an LLM something that `#B8422E` alone cannot. Name your colors. Describe your typography choices. Write the rationale as a designer would brief a junior.

---

## §2 — CREATIVE DIRECTION (Awwwards Standard)

Awwwards scores: Design 40%, Usability 30%, Creativity 20%, Content 10%. Most submissions fail on usability, not creativity.

**The non-negotiable prerequisites of every SOTD winner:**
1. **One signature moment** — one interaction or visual that makes an experienced designer stop. Not 20 effects. One.
2. **Scroll as narrative** — scroll position controls pacing and story, not just reveals
3. **Real content** — no stock imagery, no lorem ipsum, no vague aspirational copy
4. **Performance under pressure** — LCP ≤2.5s, INP ≤200ms, CLS ≤0.1, 60fps on mid-range Android
5. **Design system consistency** — the same tokens hold on every page, not just the homepage
6. **Micro-detail coverage** — hover states, focus rings, selection color, scrollbar, preloader — all designed

**Register (choose before any visual decision):**
- **Brand surface** — landing page, portfolio, campaign. Impression IS the product. Committed palette, expressive type, high motion energy.
- **Product surface** — app UI, dashboard, admin. Design serves the task. Semantic states, component consistency, information density.

**Name anti-references** — 1–2 specific sites this design should not look like. Anti-references are constraints that force distinctiveness.

**The hero options** (the centered-headline-CTA is the default; avoid it unless it is definitively the best choice for this brief):
- Full-bleed kinetic typography at 15–25vw — text that defines and owns the viewport
- Cursor-interactive canvas — elements that respond to mouse position with lerp-smoothed lag
- Scroll-scrubbed product sequence — 3D model or image sequence controlled by scroll
- Art-directed full-bleed image with type overlaid through deliberate cutouts or masks
- A live demo of the product — demonstrating rather than describing

**Scroll as narrative — chapter structure:**
Each section is a chapter with an emotional register, typographic weight, and pacing. Transitions between chapters are designed moments. Use GSAP ScrollTrigger pinned sequences for scenes that evolve as the user scrolls. Use Lenis for smooth scroll (connect to GSAP: `gsap.ticker.add(t => lenis.raf(t * 1000))`).

**The interaction system** (scored under Design 40%):
- **Custom cursor**: lerp-smoothed (factor 0.1), context-aware state changes, hidden on mobile
- **Magnetic buttons**: primary CTAs pull toward the cursor when hovering nearby
- **Selection color**: `::selection { background: var(--accent); color: var(--bg); }` — one line, signals obsession
- **Scrollbar**: `::-webkit-scrollbar { width: 4px; } ::-webkit-scrollbar-thumb { background: var(--accent); }` — one line
- **Preloader**: the first thing judges see. A designed loading screen that sets the aesthetic register and resolves into the hero through a designed transition
- **Page transitions**: overlay wipe or morph on navigation — maintains immersion, demonstrates craft
- **Hover states on every interactive element** — not optional, not "just color change"

**Art direction:**
- Imagery must be art-directed, not sourced — original photography, or treated existing imagery (duotone via `mix-blend-mode`, grain via SVG `feTurbulence`, selective clip-path)
- Images as layout elements — bleed to edge, break the grid, overlap with type
- **Grain overlay for atmosphere**: 2–4% opacity SVG grain filter makes color fields feel physical, not screen-flat
- **Clip-path reveals** on scroll entry: `clip-path: inset(0 100% 0 0)` → `inset(0 0 0 0)` = horizontal wipe
- **Blend modes**: `mix-blend-mode: multiply/overlay/screen` on images over colored fields creates print-like layering

---

## §3 — TYPOGRAPHY SYSTEM

**Never use:** Inter, Roboto, Open Sans, Lato, Arial, system-ui as a design choice. Second-tier overused: Space Grotesk, Geist, Instrument Serif. Italic serif hero + Inter body = the 2026 AI-slop signature.

**Distinctive alternatives by register:**
| Register | Display | Body | Label |
|---|---|---|---|
| Editorial/brand | Fraunces, Canela, Playfair Display | Newsreader, Crimson Pro | IBM Plex Mono |
| Technical | JetBrains Mono (as display) | IBM Plex Sans | IBM Plex Mono |
| Startup/modern | Clash Display, Obviously | Satoshi, Cabinet Grotesk | Same family, different weight |
| Expressive | Bebas Neue, Libre Baskerville | Source Serif 4 | Space Mono |

**Pairing rule:** Contrast is interesting. Serif display + geometric sans body. Grotesque display + humanist serif body. Monospace display + clean sans body. Weight extremes: 100–200 vs 800–900, not 400 vs 600.

**Type scale ratios:**
- 1.250 (minor third): dense / text-heavy / product UI
- 1.333 (perfect fourth): standard web
- 1.618 (golden ratio): expressive marketing / hero-driven

**Fluid type** (required for brand surfaces):
```css
:root {
  --text-display: clamp(3rem, 2rem + 5vw, 7rem);
  --text-headline: clamp(2rem, 1.5rem + 2.5vw, 3.5rem);
  --text-body: clamp(1rem, 0.9rem + 0.5vw, 1.125rem);
}
```
Use rem throughout. If max ≤ 2.5× min, the text always passes WCAG SC 1.4.4 under zoom.

**OpenType on body text:**
```css
body {
  font-kerning: auto;
  font-variant-ligatures: common-ligatures contextual;
  font-optical-sizing: auto;
  text-rendering: optimizeLegibility;
}
```

**Variable fonts** over static where multiple weights are used — one file, smoother weight animation, better performance.

**Non-negotiable readability:**
- Line length: 45–85 characters (`max-width: 65ch` on prose)
- Body line-height: 1.4–1.7; tighten headings to 1.0–1.2
- Body minimum: 16px
- WCAG AA: 4.5:1 body / 3:1 large text (18px+ regular, 14px+ bold)

---

## §4 — MOTION SYSTEM (Emil Kowalski + GSAP)

Motion must earn its place. The aggregate of invisible correctness creates interfaces people love without knowing why.

### Animation decision gate (answer in order before any motion code)

**Gate 1 — Frequency check:**
| How often? | Decision |
|---|---|
| 100+ times/day (command palette, keyboard shortcuts) | No animation. Ever. |
| Tens of times/day (hover, list navigation) | Remove or cut drastically |
| Occasional (modals, drawers, toasts) | Standard animation |
| Rare/first-time (onboarding, celebrations) | Can add delight |

Never animate keyboard-initiated actions. Raycast has no open/close animation. That is optimal.

**Gate 2 — Purpose check:** Can you state in one sentence why this animates? Valid: spatial consistency, state indication, feedback, preventing jarring change. Invalid: "it looks cool" on something seen 50 times/day.

**Gate 3 — Easing:**
```css
/* Strong ease-out — UI interactions (entering elements) */
--ease-out: cubic-bezier(0.23, 1, 0.32, 1);

/* Strong ease-in-out — on-screen movement, morphing */
--ease-in-out: cubic-bezier(0.77, 0, 0.175, 1);

/* iOS-like drawer — drawers, sheets */
--ease-drawer: cubic-bezier(0.32, 0.72, 0, 1);
```
Never `ease-in` for UI — it delays at the exact moment the user is watching. Never `linear` for anything except constant motion (progress bars, marquees).

**Gate 4 — Duration:**
| Element | Duration |
|---|---|
| Button press, scale feedback | 100–160ms |
| Tooltips, small popovers | 125–200ms |
| Dropdowns, selects | 150–250ms |
| Modals, drawers | 200–400ms |
| Scroll-driven narrative | Tied to scroll position, not duration |
| Marketing/explanatory | Can be longer |

### Emil Kowalski component craft

**Buttons must feel responsive:**
```css
.button { transition: transform 160ms var(--ease-out); }
.button:active { transform: scale(0.97); }
```

**Never animate from scale(0):** Start from `scale(0.95)` + `opacity: 0`. Nothing in the world appears from nothing.

**Popovers must be origin-aware:**
```css
/* Radix UI */ .popover { transform-origin: var(--radix-popover-content-transform-origin); }
/* Base UI  */ .popover { transform-origin: var(--transform-origin); }
```
Exception: modals stay `transform-origin: center` — they're not anchored to a trigger.

**Tooltips: skip delay on subsequent hovers** — first tooltip delays, subsequent tooltips in the same toolbar open instantly (data-instant pattern).

**CSS transitions over keyframes for interruptible UI:**
```css
/* Interruptible — good */ .toast { transition: transform 400ms var(--ease-out); }
/* Restarts from 0 — avoid */ @keyframes slideIn { ... }
```

**Blur to mask imperfect transitions:**
Adding `filter: blur(2px)` during a crossfade bridges the visual gap between old and new state. Keep blur ≤ 4px for UI (Safari performance). Heavy blur on large areas is expensive.

**@starting-style for entry animation (modern CSS, no JS):**
```css
.modal {
  opacity: 1; transform: scale(1);
  transition: opacity 200ms, transform 200ms var(--ease-out);
  @starting-style { opacity: 0; transform: scale(0.95); }
}
```

**Clip-path reveals (cinematic effect):**
```css
.reveal { clip-path: inset(0 100% 0 0); transition: clip-path 600ms var(--ease-out); }
.reveal.visible { clip-path: inset(0 0% 0 0); }
```

**Uniform fade-in on every element is AI slop:** If ≥4 components share identical `opacity + translateY` enter animations, that's the slop pattern. Vary timing, direction, or skip the animation on elements that don't need it.

**GPU-composited properties only:** Animate `transform` and `opacity`. Never `width`, `height`, `top`, `left`, `margin`, `padding` — these trigger layout recalculation. Use `will-change: transform` on complex animated elements sparingly (consumes GPU memory).

**`prefers-reduced-motion` is mandatory:**
```css
@media (prefers-reduced-motion: reduce) {
  *, *::before, *::after {
    animation-duration: 0.01ms !important;
    transition-duration: 0.01ms !important;
  }
}
```
Preserve functional feedback (loading states, error signals) even in reduced-motion mode.

**`transition: all` is forbidden** — targets unexpected properties, degrades performance, unfocused motion.

### GSAP stack for Awwwards-level work
- **GSAP + ScrollTrigger**: scroll-driven animation, pinned sequences, scrubbed timelines
- **Lenis**: smooth scroll override (connect: `gsap.ticker.add(t => lenis.raf(t * 1000))`)
- **SplitType/GSAP SplitText**: character-level text animation for hero kinetic typography (hero only — never body copy)
- **Spring animations**: `useSpring` from Motion for mouse-tracking, drag with momentum, interruptible gestures

**Kinetic typography rule:** Hero headlines and major section transitions only. Applied to body copy: fights CLS, fights screen readers, fights search crawlers.

**WebGL/Three.js decision:** Use only when the brand IS the experience (creative agencies, fashion, art portfolios). Causes Core Web Vitals failures on mid-tier mobile when applied broadly.

---

## §5 — COLOR SYSTEM (OKLCH + 60/30/10)

**Use OKLCH for all new color work.** Equal L values look equally bright across all hues — unlike HSL where yellow blazes and blue broods at the same L=50%. CSS Color Level 4, supported in all modern browsers since 2023.

```css
/* Syntax: oklch(lightness chroma hue) */
:root {
  --color-accent: oklch(0.60 0.20 25);     /* warm red — example */
  --color-accent-hover: oklch(0.53 0.20 25); /* darker by L only — perceptually even */
  --color-surface: oklch(0.97 0.01 90);    /* near-white warm */
}
```

**60/30/10 as a compass:** Dominant color 60% of visual weight, secondary 30%, accent 10%. The accent is the sole interaction driver — every CTA, link, active state. Nothing else uses the accent.

**Tonal scale from one base:** Build a 5–9 step lightness scale in OKLCH — equal L steps produce visually even steps. Map to semantic roles (100=lightest, 900=darkest).

**Dark mode:** Invert tonal scale rather than writing a separate palette. OKLCH-based tokens make this mathematically clean.

**Grain for atmosphere:** 2–4% opacity SVG grain overlay makes backgrounds feel material rather than screen-flat:
```css
.grain::after {
  content: '';
  position: fixed; inset: 0; pointer-events: none; z-index: 9999;
  background-image: url("data:image/svg+xml,..."); /* SVG feTurbulence noise */
  opacity: 0.03;
}
```

**Draw color from the brief's world, not from Coolors.** A Mendoza winery, a legal tech firm, and a skateboard brand have incompatible color languages. Source the palette from the subject's own materials, textures, and cultural codes.

---

## §6 — AI SLOP BLACKLIST

Experienced judges recognize these patterns immediately. 4+ triggers = heavy slop. Run the brief and the plan against this list before building.

**Typography slop**
- Inter, Roboto, Open Sans, Lato, Arial for any design role
- Second-tier overuse: Space Grotesk, Geist, Instrument Serif
- Italic serif as primary hero headline (was tasteful, now AI-startup universal tell)
- Eyebrow chip above hero H1 (tiny uppercase tracked label or pill)
- Repeated tiny uppercase tracked section kickers on every heading
- Flat type hierarchy — heading and body too close together (need ≥1.25 ratio between steps)
- Icon tile stacked above heading (rounded container → icon → heading = AI feature card #1)
- Oversized full-sentence hero headline at 72px+

**Color slop**
- Purple-to-blue gradient on anything — hero, buttons, backgrounds
- Lavender/violet "VibeCode Purple" — AI generation's default hue
- Cyan on dark ("hackathon slop")
- Dark background + colored `box-shadow` glow — the default AI "cool"
- Gradient text on headings — kills scannability, strong AI tell
- Warm cream/beige background reached for by reflex (was elegant, now clichéd default)
- Gray text on colored background (use darker shade of background color instead)
- Soft 0.1-opacity drop shadows on every container

**Layout slop**
- Centered hero → badge → 64pt headline → subhead → 2 CTAs (interchangeable across any product)
- Three identical feature cards: icon + heading + 2-line text below the hero
- Same spacing value used everywhere (no rhythm, no hierarchy information encoded)
- Cards inside cards inside cards (max 2 levels deep)
- **Side-tab accent border on rounded cards** — single most recognizable AI UI tell
- Glassmorphism as decoration rather than for real layering problems
- Numbered section labels (01/02/03) when content is not actually a sequence
- Hero stat banner: big number + small label + 3 supporting stats + gradient accent
- Hairline border + wide diffuse shadow on same element (commit to one)
- Repeating-gradient stripes as surface decoration
- Icon containers larger than the heading they introduce
- Same rounded-xl border-radius on every element

**Motion slop**
- Pulsing indicators: glowing dots, breathing CTAs, `animate-pulse` on status elements
- Bouncing icons, wiggling elements, floating badges (motion without purpose)
- `transition: all` anywhere
- Ambient gradient blob animations in background
- Identical `opacity + translateY` enter animation on every element (≥4 elements = flag)
- Bounce easing on any non-playful, non-celebration element
- Any animation on keyboard-initiated actions

**Copy slop**
- "Build the future of work" / "Scale without limits" / "Your all-in-one platform" (describes every SaaS product ever built)
- Label + sublabel + helper text + hint text all restating the same content
- All-caps section labels as the only structural device
- Any headline that could appear on a competitor's site without modification

---

## §7 — PERFORMANCE AS JUDGING CRITERION

Performance is scored under Usability (30%). Beautiful sites that fail on mid-range mobile do not win.

**Core Web Vitals targets (non-negotiable):**
- LCP (Largest Contentful Paint): ≤2.5s — preload with `<link rel="preload" as="image">`
- INP (Interaction to Next Paint): ≤200ms — no heavy JS on interaction path
- CLS (Cumulative Layout Shift): ≤0.1 — `width`/`height` on all images, `font-display: swap`
- Animation: 60fps sustained on mid-range hardware

**Critical patterns:**
```html
<!-- Preload LCP element -->
<link rel="preload" as="image" href="hero.webp" fetchpriority="high">
<!-- Preload critical fonts -->
<link rel="preload" as="font" type="font/woff2" href="display.woff2" crossorigin>
```
```css
/* All images: prevent CLS */
img { width: 100%; height: auto; }
/* Font fallback: prevent invisible text */
@font-face { font-display: swap; }
```

**Mobile is a judging dimension, not a fallback.** Touch interactions replace hover states intentionally. The mobile layout is an editorial decision. Test on mid-range Android (Moto G Power tier), not a flagship.

**WebGL/3D decision tree:**
- Brand IS the experience (creative agency, fashion, art)? → WebGL appropriate
- Anything else? → Use CSS 3D transforms (`perspective`, `rotateY`) or skip 3D
- WebGL causes Core Web Vitals failures on mid-tier mobile at 4G when applied broadly

**`backdrop-filter: blur()`** — computationally expensive. Use on navigation, modals, small elements only. Not hero sections. Causes 15–30% FPS drops on mid-tier Android at scale.

---

## §8 — CSS CODE QUALITY

Sloppy CSS produces visual inconsistencies that expose lack of craft — scored under Design (40%).

**CSS custom properties as the complete design system.** Every value from DESIGN.md becomes a CSS variable at `:root`. Never hard-code the same value twice. The DESIGN.md and the CSS variables should map 1:1.

```css
:root {
  /* From DESIGN.md tokens */
  --color-accent: oklch(0.60 0.20 25);
  --font-display: 'Fraunces', serif;
  --radius-card: 12px;
  --space-section: 120px;
  /* Motion tokens */
  --ease-out: cubic-bezier(0.23, 1, 0.32, 1);
  --duration-ui: 200ms;
}
```

**Flat specificity.** Single-class selectors (0,1,0) throughout. Never compound selectors to beat another — fix the architecture instead. The `.section .cta` overriding `.cta` problem that breaks margins/paddings between sections is always an architecture problem, not a specificity problem.

**`@layer` for cascade control:**
```css
@layer reset, base, tokens, components, utilities;
/* Layer order = precedence order. No !important needed. */
```

**`:where()` for zero-specificity resets:**
```css
:where(h1, h2, h3, h4, h5, h6) { font-weight: 700; } /* (0,0,0) — trivially overridable */
```

**Never `!important` for specificity conflicts.** It signals wrong architecture. Fix the layer or flatten the selector.

**`font-display: swap`** on all web fonts. Pair with a metric-compatible fallback to minimize CLS on font swap.

**GPU-composited properties only for animation:** `transform` and `opacity`. Never `width`, `height`, `top`, `left`, `margin`, `padding`.

---

## §9 — PROCESS: DESIGN FIRST, ZERO ITERATION

The goal is first-output quality. Iteration happens because the design is not anchored before coding begins. Anchoring via DESIGN.md eliminates the need.

**Phase 1 — Brief analysis (internal, before output):**
Name the register, subject, audience, single job, emotional tone. Name 1–2 anti-references. Identify the signature moment. Check every planned dimension against the slop blacklist. Revise any trigger before proceeding.

**Phase 2 — DESIGN.MD output:**
Produce the full DESIGN.md block (§1 format) before any code. This is the contract. The user can save it. Future agents can read it. It survives sessions.

**Phase 3 — Build in this order:**
1. Semantic HTML structure (accessibility and CLS prevention)
2. CSS custom properties from DESIGN.md tokens
3. Spacing and layout (before colour — hierarchy first)
4. Typography and colour
5. Interactive states on every element (hover, focus, active)
6. The signature moment (build this completely)
7. Secondary motion and scroll transitions
8. Responsive breakpoints (design decisions, not scaling)
9. Performance audit (LCP element identified and preloaded, images sized, CLS checked)

**Phase 4 — Judge's eye (internal critique before output):**
- Does any dimension of this look like it could belong to a different product?
- Does the hero belong to this brief, or is it a default?
- Is the interaction system complete, or are elements undesigned?
- Does every interactive element have a deliberate hover state?
- Would a judge reviewing 15 sites today stop at this one?

**Do most of this in thinking. Show the user the DESIGN.md, then the code, without narrating the process.**

---

## §10 — UX WRITING

Words are design material. Bring the same intentionality to copy that you bring to spacing.

Write from the user's side of the screen. Name things by what people control and recognize, never by how the system is built.

Active voice. A control says exactly what happens: "Save changes" not "Submit." An action keeps the same name through the whole flow — the button that says "Publish" produces a toast that says "Published."

**Say it once.** Label + sublabel + helper text + hint text all restating the same thing is noise. One job per element.

**Hero copy must be specific.** "Build the future of work" is every SaaS product. The headline should say something true and specific that only this product, for this audience, can claim.

**Failure and emptiness are invitations.** Say what went wrong and exactly how to fix it. An empty screen names the action that fills it.

Sentence case. Plain verbs. No filler. Register matched to brand and audience.

---

## §11 — RESTRAINT & SELF-CRITIQUE

Spend boldness in one place — the signature moment. Everything else is quiet in its service.

The studio that wins Awwwards is the studio that removed one accessory, then another. The signature moment gets the space it needs.

Build to the mandatory quality floor without announcing it: responsive and designed for 375px mobile, visible keyboard focus on every interactive element, `prefers-reduced-motion` at component level, WCAG AA contrast, semantic HTML, `alt` text on every image.

Breaking rules is only valid when it serves the brief and when you can state in one sentence why. Random rule-breaking is noise. Deliberate rule-breaking with a reason is a signature.

Human creators remember their past work and consciously avoid repeating themselves. Apply the same discipline. Note what you tried. The first design is always the safe design — push until you find the choice that is specific to this brief and cannot be produced for a different client in the same category.
