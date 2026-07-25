# Typography Pairing

**Why this exists:** The onboarding wizard offers 12 Google Fonts and asks the user to pick a heading + body pair. Most users don't have strong opinions on type. This document codifies the pairs that work without further thought, so the wizard can recommend confidently and the converters can render coherently.

## Safe pairs

| Pair | Use for | Reason |
|---|---|---|
| `Inter` + `Inter` | Technical docs, dashboards | Single family across heading/body — clean, neutral, OpenType-rich |
| `Inter` + `Source Sans 3` | Long-form reports | Sans-on-sans pairing; Source Sans is more readable at body size |
| `Source Serif 4` + `Source Sans 3` | Editorial / narrative | Adobe's Source family — designed as a coherent system |
| `Playfair Display` + `Lora` | Magazine-style | Serif heading with personality; serif body that pairs |
| `Merriweather` + `Open Sans` | Long-form reading | Editorial serif + neutral sans body; oldest-and-safest pair |
| `IBM Plex Sans` + `IBM Plex Sans` | Technical + brand | Plex is designed for documentation; coherent across weights |
| `JetBrains Mono` + (Inter or Source Sans 3) | Engineering notebooks | Mono headings signal a coding/terminal context |

## Sources

### 1. Ellen Lupton — *Thinking with Type* (Princeton Architectural Press, 2010)
Foundational. The "stress, weight, and contrast" framework for pairing: the heading and body should share at least one of {stress angle, x-height, terminal style} and contrast in at least one of {weight, scale}. Every recommended pair above satisfies this.

### 2. Tim Brown — *Combining Typefaces* (Five Simple Steps, 2013)
The "concord / contrast / conflict" framework. Concord (same family) is always safe — hence the Inter+Inter and IBM Plex Sans+IBM Plex Sans pairs. Contrast is rewarding when done with intent (Playfair + Lora). Conflict is what users should avoid; the wizard's curated list rules out conflict pairs.

### 3. Erik Spiekermann — *Stop Stealing Sheep & Find Out How Type Works* (Adobe Press, 2013, 3rd ed.)
Argues that body type carries 95% of the visual weight in a document. The wizard prioritizes body font choice over heading font choice in the recommendation framing.

### 4. Google Fonts — *Pairings* and *Featured Pairs* (fonts.google.com)
The 12 fonts in `SAFE_FONTS` are pulled from Google Fonts' own curated catalog, biased toward families with multiple weights and broad language coverage. All available under the SIL Open Font License — no licensing concerns.

### 5. IBM Design Language — *Plex Family Documentation* (ibm.com/design/language/typography/type-basics)
Documents the "designed as a system" pattern: Plex Sans, Serif, Mono share metrics and x-height, so any combination renders coherently. We surface Plex Sans for users who want IBM-style technical documents.

### 6. Adobe Fonts — *Source Sans, Source Serif, Source Code* (fonts.adobe.com/foundries/adobe-originals)
Same "designed as a system" idea: Source family was created by Adobe to be a coherent triple. We surface Source Sans 3 and Source Serif 4 (the current versions, with extended Cyrillic and Vietnamese coverage).

### 7. Marcin Wichary — *The Hardest Working Font in Manhattan* (figma.com/blog, 2023)
A case study on choosing Inter for the Figma marketing site. Reinforces Inter as a reasonable default for technical-yet-broad audiences.

## What about display fonts, script fonts, decorative fonts?

Excluded from the wizard's options. Decorative fonts work for the first 200 words and exhaust the reader thereafter — they're a marketing-page choice, not a document choice. If the user wants a decorative heading, they can set `typography.heading_font` to any Google Font name manually after onboarding (the field accepts any string).

## What about variable fonts?

Inter, Roboto, Source Sans 3, Source Serif 4, IBM Plex Sans, and JetBrains Mono are all available as variable fonts on Google Fonts. The converters use the `wght@400;600` slice by default — sufficient for body + bold heading — to keep CDN payload small. Users who want a wider weight range can override the Google Fonts URL directly in the generated HTML.

## Type scale

`typography.scale_ratio` (default 1.25 = major third) drives a modular scale: body = 1rem, h6 = 1rem × 1.25, h5 = 1rem × 1.25², etc. Defaults:

| Ratio | Name | Effect |
|---|---|---|
| 1.125 | Major second | Tight; good for dense reference docs |
| 1.2 | Minor third | Standard for technical writing |
| **1.25** | **Major third** | Default; balanced for long-form reading |
| 1.333 | Perfect fourth | Editorial; pronounced hierarchy |
| 1.5 | Perfect fifth | Magazine-style with bold headings |

Each converter applies the scale based on this single ratio — no per-level overrides.

## Applied to markdown-html

The converters emit a `<link>` to Google Fonts at document head and apply the typography choice via CSS:

```css
:root {
  --md-font-heading: 'Source Serif 4', Georgia, serif;
  --md-font-body: 'Source Sans 3', system-ui, sans-serif;
  --md-scale: 1.25;
}
body { font-family: var(--md-font-body); }
h1, h2, h3, h4, h5, h6 { font-family: var(--md-font-heading); }
```

The system fallback in each `font-family` declaration means the document still reads well if Google Fonts is blocked.
