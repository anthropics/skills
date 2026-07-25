---
name: "landing-page-generator"
description: "Generates high-converting landing pages as complete Next.js/React (TSX) components with Tailwind CSS. Creates hero sections, feature grids, pricing tables, FAQ accordions, testimonial blocks, and CTA sections using proven copy frameworks (PAS, AIDA, BAB). Outputs SEO meta tags, structured data, and performance-optimised code targeting Core Web Vitals (LCP < 1s, CLS < 0.1). Use when the user asks to create a landing page, marketing page, homepage, single-page site, lead capture page, campaign page, promo page, or conversion-optimised web page — or when they want to A/B test landing page variants or replace a static page with one designed to convert."
---

# Landing Page Generator

Generate high-converting landing pages from a product description. Output complete Next.js/React components with multiple section variants, proven copy frameworks, SEO optimization, and performance-first patterns. Not lorem ipsum — actual copy that converts.

**Target:** LCP < 1s · CLS < 0.1 · FID < 100ms  
**Output:** TSX components + Tailwind styles + SEO meta + copy variants

---

## Core Capabilities

- 5 hero section variants (centered, split, gradient, video-bg, minimal)
- Feature sections (grid, alternating, cards with icons)
- Pricing tables (2–4 tiers with feature lists and toggle)
- FAQ accordion with schema markup
- Testimonials (grid, carousel, single-quote)
- CTA sections (banner, full-page, inline)
- Footer (simple, mega, minimal)
- 4 design styles with Tailwind class sets

---

## Generation Workflow

Follow these steps in order for every landing page request:

1. **Gather inputs** — collect product name, tagline, audience, pain point, key benefit, pricing tiers, design style, and copy framework using the trigger format below. Ask only for missing fields.
2. **Analyze brand voice** (recommended) — if the user has existing brand content (website copy, blog posts, marketing materials), run it through `marketing-skill/skills/content-production/scripts/brand_voice_analyzer.py` to get a voice profile (formality, tone, perspective). Use the profile to inform design style and copy framework selection:
   - formal + professional → **enterprise** style, **AIDA** framework
   - casual + friendly → **bold-startup** style, **BAB** framework
   - professional + authoritative → **dark-saas** style, **PAS** framework
   - casual + conversational → **clean-minimal** style, **BAB** framework
3. **Select design style** — map the user's choice (or infer from brand voice analysis) to one of the four Tailwind class sets in the Design Style Reference.
4. **Apply copy framework** — write all headline and body copy using the chosen framework (PAS / AIDA / BAB) before generating components. Match the voice profile's formality and tone throughout.
5. **Generate sections in order** — Hero → Features → Pricing → FAQ → Testimonials → CTA → Footer. Skip sections not relevant to the product.
6. **Validate against SEO checklist** — run through every item in the SEO Checklist before outputting final code. Fix any gaps inline.
7. **Output final components** — deliver complete, copy-paste-ready TSX files with all Tailwind classes, SEO meta, and structured data included.

---

## Triggering This Skill

```
Product: [name]
Tagline: [one sentence value prop]
Target audience: [who they are]
Key pain point: [what problem you solve]
Key benefit: [primary outcome]
Pricing tiers: [free/pro/enterprise or describe]
Design style: dark-saas | clean-minimal | bold-startup | enterprise
Copy framework: PAS | AIDA | BAB
```

---

## Design Style Reference

| Style | Background | Accent | Cards | CTA Button |
|---|---|---|---|---|
| **Dark SaaS** | `bg-gray-950 text-white` | `violet-500/400` | `bg-gray-900 border border-gray-800` | `bg-violet-600 hover:bg-violet-500` |
| **Clean Minimal** | `bg-white text-gray-900` | `blue-600` | `bg-gray-50 border border-gray-200 rounded-2xl` | `bg-blue-600 hover:bg-blue-700` |
| **Bold Startup** | `bg-white text-gray-900` | `orange-500` | `shadow-xl rounded-3xl` | `bg-orange-500 hover:bg-orange-600 text-white` |
| **Enterprise** | `bg-slate-50 text-slate-900` | `slate-700` | `bg-white border border-slate-200 shadow-sm` | `bg-slate-900 hover:bg-slate-800 text-white` |

> **Bold Startup** headings: add `font-black tracking-tight` to all `<h1>`/`<h2>` elements.

---

## Copy Frameworks

**PAS (Problem → Agitate → Solution)**
- H1: Painful state they're in
- Sub: What happens if they don't fix it
- CTA: What you offer
- *Example — H1:* "Your team wastes 3 hours a day on manual reporting" / *Sub:* "Every hour spent on spreadsheets is an hour not closing deals. Your competitors are already automated." / *CTA:* "Automate your reports in 10 minutes →"

**AIDA (Attention → Interest → Desire → Action)**
- H1: Bold attention-grabbing statement → Sub: Interesting fact or benefit → Features: Desire-building proof points → CTA: Clear action

**BAB (Before → After → Bridge)**
- H1: "[Before state] → [After state]" → Sub: "Here's how [product] bridges the gap" → Features: How it works (the bridge)

---

## Representative Component: Hero (Centered Gradient — Dark SaaS)

Use this as the structural template for all hero variants. Swap layout classes, gradient direction, and image placement for split, video-bg, and minimal variants.

```tsx
export function HeroCentered() {
  return (
    <section className="relative flex min-h-screen flex-col items-center justify-center overflow-hidden bg-gray-950 px-4 text-center">
      <div className="absolute inset-0 bg-gradient-to-b from-violet-900/20 to-transparent" />
      <div className="pointer-events-none absolute -top-40 left-1/2 h-[600px] w-[600px] -translate-x-1/2 rounded-full bg-violet-600/20 blur-3xl" />
      <div className="relative z-10 max-w-4xl">
        <div className="mb-6 inline-flex items-center gap-2 rounded-full border border-violet-500/30 bg-violet-500/10 px-4 py-1.5 text-sm text-violet-300">
          <span className="h-1.5 w-1.5 rounded-full bg-violet-400" />
          Now in public beta
        </div>
        <h1 className="mb-6 text-5xl font-bold tracking-tight text-white md:text-7xl">
          Ship faster.<br />
          <span className="bg-gradient-to-r from-violet-400 to-pink-400 bg-clip-text text-transparent">
            Break less.
          </span>
        </h1>
        <p className="mx-auto mb-10 max-w-2xl text-xl text-gray-400">
          The deployment platform that catches errors before your users do.
          Zero config. Instant rollbacks. Real-time monitoring.
        </p>
        <div className="flex flex-col items-center gap-4 sm:flex-row sm:justify-center">
          <Button size="lg" className="bg-violet-600 text-white hover:bg-violet-500 px-8">
            Start free trial
          </Button>
          <Button size="lg" variant="outline" className="border-gray-700 text-gray-300">
            See how it works →
          </Button>
        </div>
        <p className="mt-4 text-sm text-gray-500">No credit card required · 14-day free trial</p>
      </div>
    </section>
  )
}
```

---

## Other Section Patterns

### Feature Section (Alternating)

Map over a `features` array with `{ title, description, image, badge }`. Toggle layout direction with `i % 2 === 1 ? "lg:flex-row-reverse" : ""`. Use `<Image>` with explicit `width`/`height` and `rounded-2xl shadow-xl`. Wrap in `<section className="py-24">` with `max-w-6xl` container.

### Pricing Table

Map over a `plans` array with `{ name, price, description, features[], cta, highlighted }`. Highlighted plan gets `border-2 border-violet-500 bg-violet-950/50 ring-4 ring-violet-500/20`; others get `border border-gray-800 bg-gray-900`. Render `null` price as "Custom". Use `<Check>` icon per feature row. Layout: `grid gap-8 lg:grid-cols-3`.

### FAQ with Schema Markup

Inject `FAQPage` JSON-LD via `<script type="application/ld+json" dangerouslySetInnerHTML={{ __html: JSON.stringify(schema) }} />` inside the section. Map FAQs with `{ q, a }` into shadcn `<Accordion>` with `type="single" collapsible`. Container: `max-w-3xl`.

### Testimonials, CTA, Footer

- **Testimonials:** Grid (`grid-cols-1 md:grid-cols-3`) or single-quote hero block with avatar, name, role, and quote text.
- **CTA Banner:** Full-width section with headline, subhead, and two buttons (primary + ghost). Add trust signals (money-back guarantee, logo strip) immediately below.
- **Footer:** Logo + nav columns + social links + legal. Use `border-t border-gray-800` separator.

---

## SEO Checklist

- [ ] `<title>` tag: primary keyword + brand (50–60 chars)
- [ ] Meta description: benefit + CTA (150–160 chars)
- [ ] OG image: 1200×630px with product name and tagline
- [ ] H1: one per page, includes primary keyword
- [ ] Structured data: FAQPage, Product, or Organization schema
- [ ] Canonical URL set
- [ ] Image alt text on all `<Image>` components
- [ ] robots.txt and sitemap.xml configured
- [ ] Core Web Vitals: LCP < 1s, CLS < 0.1
- [ ] Mobile viewport meta tag present
- [ ] Internal linking to pricing and docs

> **Validation step:** Before outputting final code, verify every checklist item above is satisfied. Fix any gaps inline — do not skip items.

---

## Performance Targets

| Metric | Target | Technique |
|---|---|---|
| LCP | < 1s | Preload hero image, use `priority` on Next/Image |
| CLS | < 0.1 | Set explicit width/height on all images |
| FID/INP | < 100ms | Defer non-critical JS, use `loading="lazy"` |
| TTFB | < 200ms | Use ISR or static generation for landing pages |
| Bundle | < 100KB JS | Audit with `@next/bundle-analyzer` |

---

## Common Pitfalls

- Hero image not preloaded — add `priority` prop to first `<Image>`
- Missing mobile breakpoints — always design mobile-first with `sm:` prefixes
- CTA copy too vague — "Get started" beats "Learn more"; "Start free trial" beats "Sign up"
- Pricing page missing trust signals — add money-back guarantee and testimonials near CTA
- No above-the-fold CTA on mobile — ensure button is visible without scrolling on 375px viewport

---

## Related Skills

- **Brand Voice Analyzer** (`marketing-skill/skills/content-production/scripts/brand_voice_analyzer.py`) — Run before generation to establish voice profile and ensure copy consistency
- **UI Design System** (`product-team/ui-design-system/`) — Generate design tokens from brand color before building the page
- **Competitive Teardown** (`product-team/competitive-teardown/`) — Competitive positioning informs landing page messaging and differentiation
