---
source: https://github.com/firecrawl/skills/tree/main/skills/workflows/firecrawl-website-design-clone
name: firecrawl-website-design-clone
description: Extract any website's design system into an agent-ready DESIGN.md using Firecrawl scrape evidence. Use when the user wants colors, fonts, spacing, components, layout patterns, or brand/UI guidance from a website so AI agents can create new websites, clone a look, or build pages inspired by that design.
license: ISC
metadata:
  author: firecrawl
  version: "0.1.0"
  homepage: https://www.firecrawl.dev
  source: https://github.com/firecrawl/firecrawl-workflows
inputs:
  - name: FIRECRAWL_API_KEY
    description: Firecrawl API key for hosted Firecrawl requests when the workflow runs through the CLI or API.
    required: true
---

# Firecrawl Website Design Clone

Use this when the user wants one URL turned into a practical design system file agents can use immediately.

Default outcome: **extract any website's design system in one line** and format it as `DESIGN.md`.

The skill should feel like a thin workflow around Firecrawl scrape: gather the page's visible content, structure, metadata, links, and available visual signals, then synthesize those findings into a clean design-system markdown file.

## Onboarding Interview

Infer the source URL, target stack, and whether implementation is requested from context. If the user gives a URL and asks for a design system, proceed immediately.

Ask at most 1-3 concise questions only if blocked, such as the website URL, whether to output only `DESIGN.md` or also implement, or a required target stack.

Use the host agent's normal prompt or modal UI. Do not name a harness-specific question function.

## Firecrawl Collection Plan

Use Firecrawl through the CLI or equivalent tool surface. Always start with two parallel scrapes of the supplied URL:

1. The `branding` and `images` formats together for structured design tokens and the full set of page images.
2. A full-page screenshot for visual context.

Example:

```bash
firecrawl scrape "https://example.com" --format branding,images -o ".firecrawl/example-branding.json" --pretty &
firecrawl scrape "https://example.com" --full-page-screenshot -o ".firecrawl/example-screenshot.png" &
wait
```

Combining `branding` and `images` in one call still costs a single credit and is required: the `branding` block only surfaces curated brand assets (`logo`, `favicon`, `ogImage`, `logoHref`), so without `images` the agent will miss the page's actual content imagery (heroes, product shots, carousel slides, feature visuals, illustrations, accessory photos, end-of-page artwork, and similar). On a product page like `tesla.com/cybertruck` the `branding` block has no hero — only `images` returns the main Cybertruck hero (e.g. `Cybertruck-Hero-Desktop-NA-SA-APAC.png`) and the rest of the page's photography.

If the screenshot scrape returns a remote image URL (e.g. signed storage link) instead of a local file, download it to the same `.firecrawl/` path so `DESIGN.md` can reference a stable local asset.

Use the structured `branding` output as the primary source for colors, typography, components, brand assets (logo, favicon, ogImage), personality, and confidence notes. Use the `images` list as the source of truth for the page's content imagery — hero photography, product shots, carousels, feature visuals, illustrations, and decorative graphics. Use the screenshot as the primary visual reference for layout, hierarchy, and overall feel. Add supplemental formats only when these are insufficient for the final artifact.

Collect:

- branding data for colors, typography, spacing, buttons, logos, brand imagery, personality, and confidence
- the full `images` list for hero, product, feature, and section imagery beyond the curated brand assets
- a full-page screenshot saved locally in `.firecrawl/` so it can be embedded in `DESIGN.md`
- page markdown for headings, copy hierarchy, CTAs, navigation, and section order when needed
- metadata and links for brand, product, and page-purpose clues when needed
- HTML only when the branding output, images list, and screenshot are insufficient to infer classes, font names, CSS variables, or component structure
- related pages only when the user asks for a broader site system

Do not over-crawl by default. The first version should be useful from a single representative page.

## What To Extract

Infer and document the site's design language:

- colors: primary, secondary, accents, backgrounds, borders, text, states
- typography: font families if detectable, type scale, weights, line heights, heading/body treatment
- spacing: container widths, section rhythm, grid gaps, padding scale, density
- layout: page structure, hero patterns, cards, grids, nav, footer, responsive assumptions
- components: buttons, inputs, cards, badges, nav items, pricing blocks, testimonials, feature rows, forms
- imagery and icons: style, shape language, illustration/photo treatment, logo constraints; pull representative hero, product, feature, and section images from the full `images` list rather than relying on `branding.images`, which only carries `logo`, `favicon`, `ogImage`, and `logoHref`
- motion and interaction: hover states, transitions, animation style when observable or inferable
- voice and content patterns: CTA wording, heading style, product copy rhythm

When a value cannot be measured exactly from scrape output, label it as inferred and give a practical approximation.

## Parallel Work

If appropriate, use sub-agents or equivalent parallel task runners. Natural splits include one page per researcher for multi-page sites, or one reviewer each for colors, typography, spacing, and components.

Each parallel researcher should return source URLs, extracted evidence, inferred design tokens, and confidence notes.

## Final Deliverable

Create or return a `DESIGN.md` with this structure. Embed the full-page screenshot near the top so a coding agent gets visual context alongside the tokens.

```markdown
# DESIGN.md: [Source Site]

## Source
- URL: [source URL]
- Capture date: [date]
- Evidence: [scrape/screenshot/html/links used]

## Reference Screenshot
![Full-page screenshot of [Source Site]](./.firecrawl/[source]-screenshot.png)

Use this screenshot as the visual source of truth for layout, hierarchy, density, and feel. Tokens below describe the same page in machine-readable form.

## Design Summary
[Short description of the visual language and what an agent should recreate]

## Design Tokens

### Colors
[Named color roles with hex values when known; mark inferred values clearly]

### Typography
[Fonts, fallback recommendations, scale, weights, heading/body rules]

### Spacing And Layout
[Spacing scale, containers, grids, radius, shadows, borders]

## Components
[Buttons, cards, nav, forms, hero, feature sections, pricing, footer, etc.]

## Page Patterns
[Section order, common layouts, responsive behavior]

## Content Style
[Voice, CTA style, heading patterns, copy density]

## Agent Build Instructions
[Concrete instructions an AI coding agent can follow to create a new site in this style]

## Rerun Inputs
workflow: firecrawl-website-design-clone
source_url: [url]
target_stack: [stack]
output: DESIGN.md
```

If the user asks to implement, first produce or update `DESIGN.md`, then use it as the source of truth for the build.

## Quality Bar

- Do not imply the user has rights to third-party logos, images, trademarks, or copy.
- Prefer reusable design tokens over one-off observations.
- Distinguish observed facts from inferred approximations.
- Keep the output compact enough that another agent can paste it into context and build from it.
- Preserve source URLs and scrape artifacts for review.
