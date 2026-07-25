# Single-File HTML Discipline — Why Inline + CDN-Only Externals

This reference answers exactly one decision: **why does the landing skill output a single self-contained `.html` file with all CSS + JS inline (rather than separate files or a build pipeline), and what does "self-contained" actually mean?**

## The Core Claim

A landing page is a **deliverable**, not a project. The user should be able to:
- Download the `.html` file
- Open it in a browser
- See the page exactly as designed
- Drop it onto any static host (Vercel, Netlify, plain S3) without configuration

This rules out:
- `npm install` / build steps
- Separate `.css` and `.js` files
- Framework toolchains
- Asset pipelines

The output is one HTML file. The only external network requests are Google Fonts and GSAP CDN.

## What "Self-Contained" Means

| Resource | Where it lives | Why |
|---|---|---|
| CSS | Inline `<style>` block in `<head>` | No FOUC waiting for stylesheet to load |
| JavaScript | Inline `<script>` block at end of `<body>` | Same file = no build step |
| Fonts | Google Fonts CDN | Free, fast, no license management |
| Animation library | GSAP via cdnjs CDN | 70KB minified; loads in <100ms on broadband |
| Images / icons | Inline SVG | No image hosting; small icons fit inline |
| Hero shapes | CSS gradients / shapes | No image dependencies |

## What's NOT Self-Contained (Allowed Externals)

The skill allows EXACTLY TWO external network requests:

1. **Google Fonts** — Inter font family via `fonts.googleapis.com`
2. **GSAP via CDN** — `cdnjs.cloudflare.com/ajax/libs/gsap/3.12.2/`

That's it. No tracking scripts. No analytics. No third-party fonts. No icon libraries (use inline SVG). No CSS frameworks (no Tailwind, no Bootstrap, no Bulma).

### Why these two specifically

**Google Fonts:**
- Free at any scale
- Cached aggressively by browsers
- Inter is exceptionally readable and fits dark mode
- Self-hosting Inter would add ~100KB to the file size

**GSAP CDN:**
- The animation patterns require GSAP — recreating timeline + ScrollTrigger from scratch would be ~50KB of custom JS that the skill would need to maintain
- cdnjs has 99.9% uptime; the failure mode (rare) is animations don't run — page still works as static content
- 70KB gzipped; loads fast on broadband

## Why Inline, Not Separate Files

### Why inline CSS

- **No build pipeline needed** — user double-clicks the .html, page works
- **No FOUC** — CSS arrives with the HTML, never after
- **One file to share** — copy-paste, email attachment, gist, S3 upload
- **No path-resolution issues** — `./styles.css` breaks if file moves

### Why inline JS

- Same reasons as inline CSS
- Plus: GSAP needs to load before the inline script runs, so the inline script goes at the END of `<body>` after the CDN scripts

### Why NOT a build pipeline (Webpack, Vite, etc.)

A build pipeline implies:
- A `package.json`
- A `node_modules/` (or `pnpm-lock.yaml` / `bun.lockb`)
- A build command
- A dev server
- A deploy step

The user might want this for a long-lived project. They don't want it for a landing page they're shipping today.

If the user explicitly asks for "I want a React component version" → use the sibling skill `product-team/skills/landing-page-generator/` (which outputs Next.js TSX, including the build pipeline).

## When Single-File Breaks Down

There are cases where a single-file HTML page IS the wrong output:

| Case | Use what instead |
|---|---|
| Multi-page site (about, blog, pricing, contact) | Static site generator (Astro, 11ty) — out of scope |
| Heavy interactivity (forms, auth, state) | React / Vue / Svelte app |
| SEO-critical lead-gen with copy frameworks | `landing-page-generator` (Next.js TSX) |
| Multiple languages / i18n | Static site generator |
| Server-side rendering required | Framework (Next.js, Remix, SvelteKit) |

The landing skill is for the single-page, single-language, premium-visual case.

## Accessibility Minimums

A single-file HTML page still needs:

- `<meta name="viewport">` for responsive
- `lang` attribute on `<html>`
- Semantic HTML5: `<header>`, `<section>`, `<footer>`
- Heading hierarchy: one `<h1>`, sections start with `<h2>`
- Buttons (not divs) for CTAs — keyboard navigable
- `aria-label` on icon-only buttons / links
- `alt` text on `<img>` (if any used)
- Color contrast ≥ WCAG AA (verified by `brand_palette_validator.py`)
- `prefers-reduced-motion` respect (gate animations) — recommended for production

## File Size Targets

| Component | Target | Rationale |
|---|---|---|
| HTML file (uncompressed) | 30–80 KB | Markup + CSS + JS + inline SVG icons |
| HTML file (gzip) | 8–20 KB | Most servers gzip automatically |
| Google Fonts (Inter) | ~30 KB per weight | Cached after first visit |
| GSAP + ScrollTrigger | ~70 KB combined | One-time download, cached |
| Total first-visit | <200 KB | Loads in <1s on broadband |
| Total cached return | <30 KB | Just the HTML file |

The HTML file's size is dominated by inline CSS. Aggressive minification can reduce by 30–40%, but the skill outputs readable code (not minified) for ease of editing.

## Anti-Patterns

- **External `.css` file** — defeats the self-contained property
- **External `.js` file** — same
- **CSS-in-JS libraries** (styled-components, emotion) — wrong layer; CSS goes in `<style>`
- **Multiple CDN dependencies beyond GSAP** — increases failure surface
- **Inline base64 images** — bloats file; use inline SVG for icons, CDN for photos (or skip photos)
- **Build pipeline for a landing page** — over-engineering
- **Web fonts beyond Inter** — Google Fonts is free and fast; one font family is enough
- **CSS frameworks** (Tailwind, Bootstrap, Bulma) — duplicates effort and dictates aesthetic

## Operational Checklist (Per Generation)

- [ ] All CSS in `<style>` block in `<head>` (no external `.css` files)
- [ ] All JS in `<script>` blocks (no external `.js` files except Google Fonts + GSAP CDN)
- [ ] `<meta name="viewport">` present
- [ ] `lang="en"` on `<html>` (or appropriate lang code)
- [ ] Semantic HTML5 used (header / section / footer)
- [ ] One `<h1>` per page; sections start with `<h2>`
- [ ] CTA uses `<button>` or `<a>` (not `<div>` with onclick)
- [ ] Icons via inline SVG with `aria-label`
- [ ] Total file size <100KB uncompressed
- [ ] Page works with JS disabled (static content visible; animations don't run)

## Why This Discipline Beats Alternatives

The single-file inline discipline trades:

**Loss:**
- Caching efficiency (separate CSS file would cache across pages)
- Refactor-ability (large pages get unwieldy)
- Team collaboration (multiple devs editing the same file)

**Gain:**
- One-step deploy (upload one file)
- Zero build configuration
- Zero supply-chain risk beyond Google + GSAP
- Predictable file size
- Easy to inspect / debug
- Easy to fork / customize

For a landing page (single document, single deploy), the gains dominate. For a multi-page app, the trade flips. The skill targets the former, not the latter.

## Citations (7 sources)

1. **MDN Web Docs — Single Page Applications & Static Site Generation.** Reference for the "page as deliverable" pattern. https://developer.mozilla.org/

2. **Heydon Pickering, *Inclusive Components* (2018).** Argues for accessibility-first single-page sites. Source for the accessibility-minimum checklist (heading hierarchy, semantic HTML5, keyboard navigation).

3. **Jeremy Keith, *Resilient Web Design* (2016).** Advocates for "no build step" simplicity where possible. The single-file HTML output is the strongest form of this — survives even basic web hosting without configuration.

4. **Adam Wathan, "On Building Websites in 2024" (adamwathan.me).** Argues that not every page needs a framework. Justification for the skill targeting the "landing page = single document" use case rather than reaching for Next.js by default.

5. **Vercel / Netlify deployment documentation.** Both static hosts accept single `.html` files with zero configuration. The skill's output works on both natively.

6. **Brendan Eich's "Always Bet on JS" talks (2014+).** Argues for the long-term value of HTML/CSS/JS as a delivery target — no transpiler, no compilation, just the web platform. Aligns with the no-build discipline.

7. **Robin Rendle, "The Web Is a Place" — *Static Self* (2024).** Argues that HTML/CSS as a deliverable medium has unique value precisely BECAUSE it lacks infrastructure. Landing pages are the strongest example of this pattern in production use.
