# Design Token Canon

**Why this exists:** This skill ships 12 CSS custom properties — small by design-system standards. This document explains why 12 is enough, the taxonomy the tokens follow, and the canon they derive from.

## The 12-token taxonomy

| Layer | Tokens | Purpose |
|---|---|---|
| **Surface** | `--md-bg`, `--md-surface`, `--md-border`, `--md-code-bg` | Vertical layering: page bg → cards/callouts → hairlines → fenced code |
| **Text** | `--md-text`, `--md-text-muted` | Body + secondary (captions, metadata) |
| **Accent** | `--md-accent`, `--md-accent-soft` | Brand emphasis (CTA, callout headers); soft for hover backgrounds |
| **Link** | `--md-link`, `--md-link-hover` | Hyperlink + hover state; iteratively contrast-walked |
| **Semantic** | `--md-success`, `--md-warn` | Inline status, callouts, review severity |

Twelve covers every visual decision a long-form document needs. More tokens (e.g. Material Design's hundreds) optimize for design systems that span many UIs; markdown-html spans one artifact type (a generated HTML file) so we don't need the extra.

## Sources

### 1. Salesforce Lightning Design System — *Tokens* (lightningdesignsystem.com)
First widely-adopted token system at scale. Established the layered taxonomy: surface → text → border → accent → semantic. Markdown-html's 12 tokens follow the same layering, scoped down to document-rendering needs.

### 2. Adobe Spectrum — *Color Foundations* (spectrum.adobe.com)
Documents the four roles a brand color plays: bg, accent, text, semantic. Validates the decision to derive accent from primary rather than treat them as independent (Spectrum: "accent should be a tinted, brightness-adjusted variant of the brand color").

### 3. Material Design 3 — *Color Roles* (m3.material.io)
Token taxonomy of `primary`/`onPrimary`/`primaryContainer`/`onPrimaryContainer` etc. We deliberately simplify: a long-form document doesn't need surface containers within accent containers. The 12-token system is the Material taxonomy collapsed to what document rendering actually requires.

### 4. Sara Soueidan — *Color Tokens for Accessible Color Systems* (sarasoueidan.com, 2022)
Argues for contrast-walked link colors: a link in brand accent often fails the 4.5:1 floor against bg; the system must lighten or darken until it passes. Our `_ensure_link_contrast()` is the direct implementation.

### 5. Style Dictionary (amzn.github.io/style-dictionary)
The industry-standard token transformation tool — takes JSON tokens and emits CSS / Swift / Kotlin / Flutter. We deliberately ship JSON tokens compatible with Style Dictionary in case a user wants to extend; we don't depend on it.

### 6. CSS Custom Properties (MDN)
The native browser primitive for runtime-themable styles. Inlining `:root { --md-bg: #...; }` into the generated `<style>` block means the user can override any token by adding their own `:root` override in a custom-CSS section of the document (escape hatch).

### 7. Material Design 2 — *Type Scale* and *Color System* (material.io archive)
Original 8-point grid + modular type scale + tonal palette. We use a smaller subset (just modular scale via `typography.scale_ratio`, default 1.25 = major third) and 12 tokens; same philosophy.

## Why not 8? Why not 50?

- **8 tokens** (the original landing-skill palette) — covers a landing page (hero bg, accent CTA, card bg, card border, off-white text, muted text, glow). Documents need link, link-hover, code-bg, success, and warn that landing doesn't.
- **50 tokens** (Material Design 3 / IBM Carbon) — covers a multi-surface UI with elevated containers, interactive states, focus rings, disabled states. A document is a single surface with text — most of those tokens never render.

Twelve is the smallest number that covers every visual decision a long-form document, code review, or slide deck must make, without inventing decisions the document doesn't have.

## Applied to markdown-html

Every converter inlines the user's `derived_palette` into a `:root { }` block at the top of `<style>`. Every other CSS rule references the variables — no hard-coded colors anywhere. This makes the converters honestly customizable: change `brand.primary` and re-onboard, all 12 tokens re-derive, and the document re-renders with a different brand without any code change.
