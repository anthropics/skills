---
name: design-zn
description: Apply world-class brand design systems to your UI code. Use this skill when building interfaces that need to match a specific brand's visual identity — including Vercel, Cursor, Framer, Stripe, Supabase, Figma, Notion, Airbnb, Spotify, and 46 other top brands. Provides color palettes, typography, spacing, component rules, and dark-mode tokens for each brand so Claude generates pixel-accurate, brand-consistent UI code every time.
---

# Design-ZN: Brand Design System Collection

This skill provides production-ready design system specifications for **50 top global brands**, enabling Claude to generate UI code that is visually consistent with each brand's identity.

## What It Contains

Each brand subdirectory includes:
- **`DESIGN.md`** — Full design system specification: colors, typography, spacing, border-radius, shadows, component patterns
- **`CLAUDE.md`** — AI coding rules that enforce brand consistency
- **`preview.html`** — Visual token reference (light theme)
- **`preview-dark.html`** — Visual token reference (dark theme)

## Supported Brands

| # | Brand | # | Brand | # | Brand |
|---|-------|---|-------|---|-------|
| 01 | Vercel | 18 | Raycast | 35 | HashiCorp |
| 02 | Cursor | 19 | IBM | 36 | Zapier |
| 03 | Framer | 20 | OpenCode | 37 | Renault |
| 04 | Coinbase | 21 | Lamborghini | 38 | Mistral |
| 05 | Supabase | 22 | ClickHouse | 39 | MongoDB |
| 06 | Revolut | 23 | PostHog | 40 | Expo |
| 07 | Clay | 24 | VoltAgent | 41 | Figma |
| 08 | Ferrari | 25 | BMW | 42 | Sanity |
| 09 | SpaceX | 26 | Miro | 43 | Webflow |
| 10 | Lovable | 27 | Composio | 44 | Warp |
| 11 | Sentry | 28 | NVIDIA | 45 | Together AI |
| 12 | Wise | 29 | Ollama | 46 | Replicate |
| 13 | Tesla | 30 | Resend | 47 | Stripe |
| 14 | Airtable | 31 | Runway | 48 | Notion |
| 15 | ElevenLabs | 32 | Linear | 49 | Airbnb |
| 16 | Kraken | 33 | Minimax | 50 | Spotify |
| 17 | Mintlify | 34 | xAI | | |

## How to Use

### Step 1 — Choose a brand

Identify which brand's design system you want to apply (e.g., `01-vercel`, `47-stripe`).

### Step 2 — Copy design files to your project

```bash
# Example: apply Vercel's design system
cp skills/design-zn/01-vercel/DESIGN.md ./DESIGN.md
cp skills/design-zn/01-vercel/CLAUDE.md ./CLAUDE.md
```

### Step 3 — Ask Claude to build the UI

With `CLAUDE.md` in your project root, Claude will automatically enforce the brand's design rules on every UI generation request:

```
Build a dashboard using the design system defined in DESIGN.md
```

### Step 4 — Preview tokens (optional)

Open `preview.html` or `preview-dark.html` in a browser to see all design tokens visualized.

## Design Rules Enforced by Each Brand's CLAUDE.md

| Rule | Description |
|------|-------------|
| **Colors** | Only hex values from the brand's palette — no arbitrary color literals |
| **Typography** | Only font families and sizes defined in the spec |
| **Components** | Buttons, cards, forms follow brand-specific patterns |
| **Spacing** | Base unit (typically 8px) and scale from the spec |
| **Border Radius** | Per-component values from the spec |

## Quick Install (npx)

Each brand's design file is also available via:

```bash
npx getdesign@latest add vercel
```

Replace `vercel` with the brand slug (e.g., `stripe`, `notion`, `airbnb`).
