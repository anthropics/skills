---
name: landing
description: "Generates a premium single-page HTML landing page with 3D CSS animations, GSAP scroll effects, and mouse-parallax depth. Forcing intake (product + elevator pitch, audience register, brand overrides, tone) locks down positioning before any copy or markup is written, so the page reflects the actual product rather than generic boilerplate. Use whenever the user says 'landing for X', 'create a landing page', 'build a landing page', 'make a landing page for X', 'I need a web page for Y', or provides product/service details and wants a polished website. Also triggers on 'promotional page', 'product page', 'one-pager', 'web presence', 'sales page'. Outputs a single self-contained HTML file (Claude Code) or HTML artifact (Claude.ai). Supports configurable brand colors via CSS custom property overrides."
license: MIT
metadata:
  source_spec: "megaprompts/04-landing-megaprompt.md"
  build_pattern: "Path B (direct conversion)"
  distinct_from: "product-team/skills/landing-page-generator (different output format + optimization target)"
  version: 1.0.0
---

# Landing — Premium HTML Landing Page Generator

> **Distinct from `product-team/skills/landing-page-generator/`.** That skill outputs Next.js TSX components optimized for conversion / lead-gen. THIS skill outputs a single self-contained `.html` file optimized for premium visual experience with GSAP animations. Pick by use case.

Generate a polished, self-contained `.html` landing page from a text prompt or brief. The output is ONE HTML file: all CSS inline in `<style>`, all JS inline in `<script>`, only external dependencies being Google Fonts + GSAP via CDN. The page is visually distinctive, animated, and production-quality.

## Invocation Triggers

- "create a landing page"
- "build a landing page"
- "make a landing page for X"
- "I need a web page for Y"
- "promotional page"
- "product page"
- "one-pager"
- "web presence"
- "sales page"
- "landing for X"

## Delivery Mode

In **Claude Code CLI**, write the file to disk at the specified path. In **Claude.ai web**, create an HTML artifact with the same content.

## Phase 0: Grill-Me Intake (4 forcing questions, one at a time)

Dependency-ordered. Each question carries explicit "why I'm asking". Stop condition: max 4.

### Q1 (root) — Product / Service

> **What's the product or service? Give me the name + a 1–2 sentence elevator pitch — what does it do, and who's it for?**
>
> *Why I'm asking:* The headline, subtext, and feature copy all derive from this. "App for productivity" produces generic boilerplate; "Async standup tool for remote engineering teams who hate Zoom" produces a landing page that converts.

**Refuse mush.** If user gives just a name with no pitch, push back once: "What does it do? Who's it for?" If still no pitch after push-back, deliver with explicit "generic positioning" caveat.

### Q2 (depends on Q1) — Audience Register

> **Who's the audience? Pick one:**
>
> 1. **Technical buyers** (engineers, ops, security)
> 2. **Business buyers** (PMs, execs, ops leaders)
> 3. **Consumers** (general public, hobbyists)
> 4. **Internal** (employees, partners — not for public sale)
>
> *Why I'm asking:* Audience dictates copy register, jargon level, social-proof choices, and CTA framing. Technical buyers want specifics; consumers want benefits; internal pages can skip persuasion.

Forcing choice.

### Q3 (always) — Brand Overrides

> **Brand colors / fonts to override the default (dark navy + teal + Inter)? Provide as: primary HEX, accent HEX, optional bg HEX. Or say "default" if you want the polished default.**
>
> *Why I'm asking:* The default is intentionally beautiful, but matching your brand makes the page feel native to your existing site. Even just a primary color override goes a long way.

Accept "default" or partial overrides (e.g., just primary). If only primary provided, derive accent algorithmically (lighten / darken).

### Q4 (depends on Q1) — Tone

> **Tone — pick one:**
>
> 1. **Professional** — confident, restrained, B2B-friendly
> 2. **Playful** — warm, light, occasional humor
> 3. **Authoritative** — expert, data-forward, trust-building
> 4. **Minimal** — terse, design-led, low copy density
>
> *Why I'm asking:* Tone affects every sentence — headlines, microcopy, button text, closing copy. Picking upfront prevents tonal whiplash across sections.

Forcing choice. **Recommended default:** professional if Q2 = technical/business; playful if Q2 = consumer; minimal if the product is design-led.

**Stop condition:** After Q4, commit and generate. No follow-up questions during generation.

## Content Extraction (with Fallback Strategy)

From Q1's elevator pitch, derive:
- **Hero headline** — punchy version of "what it does" (8–12 words)
- **Hero subtext** — version of "who it's for + payoff" (1–2 sentences)
- **3–6 feature bullets** — distilled from pitch + audience (Q2) + tone (Q4)
- **CTA text** — action-oriented, matches tone
- **Closing copy** — short, emotive, matches tone

**Fallback when input is sparse:** invent compelling content from product-name semantics + audience register. Flag inferred content with a comment in the HTML source (`<!-- inferred: ... -->`). Don't stall waiting for more input.

## Brand System Specification

### Default Color Palette (Dark Navy + Teal)

```css
:root {
  --navy:       #0A1628;
  --navy-mid:   #0D1F38;
  --teal:       #00D4AA;
  --teal-glow:  rgba(0, 212, 170, 0.12);
  --amber:      #F5A623;
  --off-white:  #F7F7F2;
  --text-muted: rgba(247, 247, 242, 0.68);
  --card-bg:    rgba(0, 212, 170, 0.06);
  --card-border:rgba(0, 212, 170, 0.15);
}
```

### Override Pattern

When Q3 provides custom brand values, the skill substitutes them into the `:root` block:

```
Brand override:
- primary: #FF6B35    →  --navy / hero bg
- accent:  #2EC4B6    →  --teal / CTA / highlights
- bg:      #011627    →  --navy-mid / section bg
- text:    #FDFFFC    →  --off-white
```

If only primary provided, derive accent algorithmically (lighten 15% for accent; darken 8% for navy-mid; convert to rgba at 0.12 alpha for glow). Use `scripts/brand_palette_validator.py` for the deterministic derivation.

See [`references/brand_system_design.md`](references/brand_system_design.md) for color theory + WCAG + algorithmic palette derivation canon.

### Typography

- **Font family:** Inter (via Google Fonts)
- **Weight scale:** 400 (body), 500 (eyebrow), 600 (links), 700 (subtitle), 800 (H1 + H2)
- **Size scale:**
  - Hero H1: 68–82px
  - Section H2: 52–62px
  - Card titles: 22px
  - Body: 17–19px
  - Eyebrow: 13px (uppercase, letter-spaced)
  - CTA button: 18px (500 weight)

### Components (Must Specify CSS)

- `.btn-primary` — CTA button with hover state (lift + brightness)
- `.feature-card` — card with hover lift (translateY(-6px) + border-brighten)
- `.eyebrow` — letter-spaced (0.2em) uppercase category label

## Section 1: Hero

- `min-height: 100vh`, flex-centered content
- Optional eyebrow label above H1
- H1 (68–82px, 800 weight)
- Subtitle (17–19px, 1–2 sentences)
- CTA button (.btn-primary)
- Scroll-down indicator (animated chevron, CSS bounce)
- **Depth layers** (mouse parallax):
  - `.hero-shapes-back` — large blurred circles, absolute-positioned, low opacity
  - `.hero-shapes-mid` — smaller shapes, sharper edges, higher opacity
  - Content layer (H1 + subtitle) — moves subtly in same direction as mouse

## Section 2: Features

- 3 columns default (`repeat(3, 1fr)` grid)
- Responsive:
  - 2 columns at 900px breakpoint
  - 1 column at 580px breakpoint
- Each card:
  - SVG icon (28px, stroke=var(--teal), no fill)
  - Title (22px, 700 weight)
  - Description (15–16px, --text-muted)
- Hover state:
  - `transform: translateY(-6px)`
  - `border-color: var(--teal)` (brighten from --card-border)
  - `transition: 0.3s ease`

## Section 3: Closing CTA

- Full-width, `background: var(--navy-mid)`
- `padding: 120px 24px`, text-align: center
- Large closing headline (52–62px, 800 weight)
- Short subtext (--text-muted, 1–2 sentences)
- CTA button with ambient radial-gradient glow behind it:
  ```css
  background: radial-gradient(circle, var(--teal-glow) 0%, transparent 70%);
  ```

## Animation Patterns

See [`references/gsap_animation_patterns.md`](references/gsap_animation_patterns.md) for the canon. Five patterns required:

### 1. Hero Entrance (GSAP timeline)

```js
// MUST use gsap.set() FIRST to prevent FOUC
gsap.set([".eyebrow", ".hero h1", ".hero .subtitle", ".btn-primary", ".scroll-down"], {
  opacity: 0,
  y: 30
});

const tl = gsap.timeline({ defaults: { ease: "power3.out" } });
tl.to(".eyebrow", { opacity: 1, y: 0, duration: 0.6 })
  .to(".hero h1", { opacity: 1, y: 0, duration: 0.8 }, "-=0.3")
  .to(".hero .subtitle", { opacity: 1, y: 0, duration: 0.6 }, "-=0.5")
  .to(".btn-primary", { opacity: 1, y: 0, duration: 0.5 }, "-=0.3")
  .to(".scroll-down", { opacity: 1, y: 0, duration: 0.4 }, "-=0.2");
```

### 2. Mouse Parallax

```js
const hero = document.querySelector(".hero");
hero.addEventListener("mousemove", (e) => {
  const x = (e.clientX / window.innerWidth - 0.5) * 2;
  const y = (e.clientY / window.innerHeight - 0.5) * 2;
  gsap.to(".hero-shapes-back", { x: x * 45, y: y * 22, duration: 0.8 });
  gsap.to(".hero-shapes-mid",  { x: x * 22, y: y * 11, duration: 0.8 });
  gsap.to(".hero .container",  { x: x * 8,  y: y * 5,  duration: 0.8 });
});
```

### 3. Scroll-Triggered Feature Cards

```js
gsap.set(".feature-card", { opacity: 0, y: 55, rotateX: 18 });

ScrollTrigger.batch(".feature-card", {
  start: "top 80%",
  onEnter: batch => gsap.to(batch, {
    opacity: 1, y: 0, rotateX: 0,
    duration: 0.8,
    stagger: 0.11,
    ease: "power2.out"
  })
});
```

### 4. Floating Decorative Shapes (CSS keyframes — NOT GSAP)

CSS handles ambient continuous motion (smoother, cheaper than GSAP for indefinite animations):

```css
@keyframes floatA {
  0%, 100% { transform: translate(0, 0) rotate(0deg); }
  50%      { transform: translate(20px, -30px) rotate(8deg); }
}
@keyframes floatB { /* different duration + rotation */ }
@keyframes floatC { /* different duration + rotation */ }

.hero-shapes-back .shape-a { animation: floatA 12s ease-in-out infinite; }
```

### 5. Scroll Indicator (CSS bounce)

```css
@keyframes bounce {
  0%, 100% { transform: translateY(0); }
  50%      { transform: translateY(8px); }
}
.scroll-down { animation: bounce 2s ease-in-out infinite; }
```

## Required CDN Dependencies

```html
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap" rel="stylesheet">
<script src="https://cdnjs.cloudflare.com/ajax/libs/gsap/3.12.2/gsap.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/gsap/3.12.2/ScrollTrigger.min.js"></script>
```

NO other external CSS or JS files. All custom CSS in `<style>`, all custom JS in `<script>` blocks within the same HTML file.

See [`references/single_file_html_discipline.md`](references/single_file_html_discipline.md) for the inline-only rationale.

## Layout Rules

- **Container max-width:** 1200px, centered
- **Section padding:** `120px 24px` (vertical 120, horizontal 24, scales down on mobile)
- **Responsive breakpoints:**
  - 900px → features grid 3-col → 2-col
  - 580px → all grids → 1-col; H1 scales down to ~52px
- **Viewport meta:** `<meta name="viewport" content="width=device-width, initial-scale=1">`

## Output Spec

- **Path:** `${OUTPUT_DIR}/<product-name-kebab>.html`
- **Default `${OUTPUT_DIR}`:** `./landing-pages/`
- **Filename:** lowercase kebab-case from product name ("Quill AI" → `quill-ai.html`). Use `scripts/kebab_slug_generator.py` for deterministic slug generation + duplicate detection.
- **Self-contained:** all CSS in `<style>`, all JS in `<script>`, only Google Fonts + GSAP CDN external.

## Validation (Post-Generation)

Run `scripts/html_validator.py --file ${OUTPUT_DIR}/<slug>.html` after generation. Checks:

- All 3 required sections present (`.hero`, `.features`, `.closing-cta`)
- CDN deps present (Inter + GSAP + ScrollTrigger)
- `gsap.set()` initial states precede any `gsap.timeline` or `gsap.to` (FOUC prevention)
- Responsive breakpoints at 900px + 580px
- No external `<link rel="stylesheet">` other than Google Fonts
- No external `<script src=>` other than GSAP CDN
- `<meta name="viewport">` present
- All animated elements have initial-state declarations

## Error Handling

| Situation | Behavior |
|---|---|
| Input is just a name with no context | Invent compelling content from name semantics + audience register; flag as `<!-- inferred -->` in HTML source |
| Input file is large or PDF | Read fully before generating; don't truncate |
| Brand colors insufficient (only 1 HEX provided) | Use as primary; derive secondary/accent algorithmically (lighten/darken via brand_palette_validator.py) |
| Features count not specified | Default to 4 |
| Output dir doesn't exist | Create it |
| Existing file at output path | Append timestamp suffix or ask user (kebab_slug_generator.py flags duplicates) |
| html_validator returns FAIL | Regenerate ONLY the failing sections in one targeted pass; do NOT abandon the file |

## Portability

- **Claude Code CLI:** Native — writes HTML file directly to filesystem.
- **Claude.ai web:** Native — produces HTML as an artifact instead of file.

## Tooling

| Script | Role |
|---|---|
| `scripts/brand_palette_validator.py` | Validates HEX format, checks WCAG AA contrast, generates derived palette from primary (algorithmic lighten/darken). |
| `scripts/kebab_slug_generator.py` | Product name → kebab-case filename + duplicate detection in output dir. |
| `scripts/html_validator.py` | Post-generation structural check: 3 sections, CDN deps, gsap.set() initial states, responsive breakpoints, no external files. |

## References

- [`references/brand_system_design.md`](references/brand_system_design.md) — color theory + WCAG + algorithmic palette derivation (7+ sources)
- [`references/gsap_animation_patterns.md`](references/gsap_animation_patterns.md) — entrance timeline + ScrollTrigger reveals + mouse parallax + CSS floats + scroll indicator (7+ sources)
- [`references/single_file_html_discipline.md`](references/single_file_html_discipline.md) — why inline + CDN-only externals + accessibility minimums + no-build rationale (7+ sources)

## Anti-Patterns To Reject

- Hardcoded absolute paths in output directory
- Single brand palette without override documentation
- Outlining before writing — write in one pass
- External CSS or JS files (must be inline; only Google Fonts + GSAP CDN allowed)
- Skipping `gsap.set()` initial states (causes FOUC)
- More than 6 features in default grid (becomes unscannable)
- Brand-specific content references in the skill itself

---

**Version:** 1.0.0
**Source spec:** [`megaprompts/04-landing-megaprompt.md`](../../../../megaprompts/04-landing-megaprompt.md)
**Build pattern:** Path B (direct conversion). Distinct from `product-team/skills/landing-page-generator/`.
