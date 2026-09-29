---
name: extract-design
description: "Extract the full design language from any website URL. Produces 8 output files including AI-optimized markdown, visual HTML preview, Tailwind config, React theme, shadcn/ui theme, Figma variables, W3C design tokens, and CSS variables. Also runs WCAG accessibility scoring. Use when user says 'extract design', 'get design system', 'design language', 'design tokens', 'what colors/fonts does this site use', or '/extract-design'."
---

# Extract Design Language

Extract the complete design language from any website URL. Uses Playwright to crawl the live DOM and produces 8 output files covering colors, typography, spacing, shadows, components, breakpoints, animations, and accessibility.

The primary output is an AI-optimized markdown file structured for LLM consumption — feed it back to Claude to faithfully recreate any website's visual design from scratch.

## Prerequisites

The tool is available via npx (no install required):

```bash
npx designlang <url>
```

## Process

1. **Run the extraction** on the provided URL:

```bash
npx designlang <url> --screenshots
```

Additional options:
- Multi-page crawling: `npx designlang <url> --depth 3`
- Dark mode extraction: `npx designlang <url> --dark`
- Both: `npx designlang <url> --depth 3 --dark --screenshots`

2. **Read the generated markdown file** to understand the design:

```bash
cat design-extract-output/*-design-language.md
```

3. **Present key findings** to the user:
   - Primary color palette with hex codes
   - Font families in use
   - Spacing system (base unit if detected)
   - WCAG accessibility score and failing color pairs
   - Component patterns found
   - Notable design decisions (shadows, radii, gradients)

4. **Offer next steps:**
   - Copy `*-tailwind.config.js` into their project
   - Import `*-variables.css` into their stylesheet
   - Paste `*-shadcn-theme.css` into globals.css for shadcn/ui users
   - Import `*-theme.js` for React/CSS-in-JS projects
   - Import `*-figma-variables.json` into Figma for designer handoff
   - Open `*-preview.html` in a browser for a visual overview
   - Use the markdown file as context for AI-assisted development

## Output Files (8)

| File | Purpose |
|------|---------|
| `*-design-language.md` | AI-optimized markdown — the full design system for LLMs |
| `*-preview.html` | Visual HTML report with swatches, type scale, shadows, a11y score |
| `*-design-tokens.json` | W3C Design Tokens format |
| `*-tailwind.config.js` | Ready-to-use Tailwind CSS theme extension |
| `*-variables.css` | CSS custom properties |
| `*-figma-variables.json` | Figma Variables import format |
| `*-theme.js` | React/CSS-in-JS theme object |
| `*-shadcn-theme.css` | shadcn/ui theme CSS variables |

## Additional Commands

- **Compare two sites:** `npx designlang diff <urlA> <urlB>` — outputs markdown and HTML comparison
- **View history:** `npx designlang history <url>` — shows how a site's design evolves over time

## What It Extracts

- **Colors** — full palette with primary/secondary/accent/neutral classification, gradients
- **Typography** — font families, type scale, heading/body styles, weight distribution
- **Spacing** — all unique values with automatic base-unit detection
- **Border Radii** — unique values labeled xs through full
- **Box Shadows** — parsed and classified by visual weight
- **CSS Variables** — all `:root` custom properties, categorized
- **Breakpoints** — media query breakpoints with standard labels
- **Animations** — transitions, easing functions, durations, keyframes
- **Components** — buttons, cards, inputs, links with base styles
- **Accessibility** — WCAG 2.1 contrast ratios for all fg/bg color pairs

## Examples

Extract Stripe's design system:
```bash
npx designlang https://stripe.com
# → 28 colors, sohne-var font, 651 CSS vars, 94% WCAG score
```

Compare Vercel and Stripe:
```bash
npx designlang diff https://vercel.com https://stripe.com
# → diff.md + diff.html showing color, typography, and a11y differences
```

Extract with screenshots and dark mode:
```bash
npx designlang https://github.com --dark --screenshots --depth 3
```

## Links

- GitHub: https://github.com/Manavarya09/design-extract
- npm: https://www.npmjs.com/package/designlang
