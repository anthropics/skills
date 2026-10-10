---
version: alpha
name: Pinterest-design-analysis
description: |
  A photography-first discovery system organized around the Pinterest Red CTA, the masonry pin grid, and a soft warm-cream chrome that gets out of the imagery's way. The home page is a content-discovery tool wearing the chrome of a magazine publisher: 70px display headlines, friendly Pin Sans typography, fully-rounded pill buttons (16px) on a cream-tinted neutral palette, and a sticky red "Sign up" CTA that anchors every viewport. Pin imagery is the system's load-bearing visual element — square, portrait, and landscape pins tile in a column-based masonry grid where each tile is a fully-rounded 16px-radius card, separated by tight 8px gutters. The chrome is otherwise quiet: warm grays, true whites, and a single saturated red — no decorative gradients, no atmospheric backgrounds, no shadows beyond a soft modal scrim.

colors:
  primary: "#e60023"
  on-primary: "#ffffff"
  primary-pressed: "#cc001f"
  ink: "#000000"
  ink-soft: "#211922"
  body: "#33332e"
  charcoal: "#262622"
  mute: "#62625b"
  ash: "#91918c"
  stone: "#c8c8c1"
  hairline: "#dadad3"
  hairline-soft: "#e5e5e0"
  on-secondary: "#000000"
  secondary-bg: "#e5e5e0"
  secondary-pressed: "#c8c8c1"
  canvas: "#ffffff"
  surface-soft: "#fbfbf9"
  surface-card: "#f6f6f3"
  surface-elevated: "#ffffff"
  on-dark: "#ffffff"
  on-dark-mute: "rgba(255,255,255,0.7)"
  surface-dark: "#262622"
  focus-outer: "#435ee5"
  focus-inner: "#ffffff"
  accent-pressed-blue: "#617bff"
  accent-purple: "#7e238b"
  accent-purple-deep: "#6845ab"
  success-deep: "#103c25"
  success-pale: "#c7f0da"
  error: "#9e0a0a"
  error-deep: "#cc001f"

typography:
  display-xl:
    fontFamily: Pin Sans
    fontSize: 70px
    fontWeight: 600
    lineHeight: 1.1
    letterSpacing: -1.2px
  display-lg:
    fontFamily: Pin Sans
    fontSize: 44px
    fontWeight: 700
    lineHeight: 1.15
    letterSpacing: -0.8px
  heading-xl:
    fontFamily: Pin Sans
    fontSize: 28px
    fontWeight: 700
    lineHeight: 1.2
    letterSpacing: -1.2px
  heading-lg:
    fontFamily: Pin Sans
    fontSize: 22px
    fontWeight: 600
    lineHeight: 1.25
    letterSpacing: 0
  heading-md:
    fontFamily: Pin Sans
    fontSize: 18px
    fontWeight: 600
    lineHeight: 1.3
    letterSpacing: 0
  body-md:
    fontFamily: Pin Sans
    fontSize: 16px
    fontWeight: 400
    lineHeight: 1.4
    letterSpacing: 0
  body-strong:
    fontFamily: Pin Sans
    fontSize: 16px
    fontWeight: 600
    lineHeight: 1.4
    letterSpacing: 0
  body-sm:
    fontFamily: Pin Sans
    fontSize: 14px
    fontWeight: 400
    lineHeight: 1.4
    letterSpacing: 0
  body-sm-strong:
    fontFamily: Pin Sans
    fontSize: 14px
    fontWeight: 700
    lineHeight: 1.4
    letterSpacing: 0
  caption-md:
    fontFamily: Pin Sans
    fontSize: 12px
    fontWeight: 500
    lineHeight: 1.5
    letterSpacing: 0
  caption-sm:
    fontFamily: Pin Sans
    fontSize: 12px
    fontWeight: 400
    lineHeight: 1.4
    letterSpacing: 0
  link-md:
    fontFamily: Pin Sans
    fontSize: 16px
    fontWeight: 600
    lineHeight: 1.4
    letterSpacing: 0
  button-md:
    fontFamily: Pin Sans
    fontSize: 14px
    fontWeight: 700
    lineHeight: 1
    letterSpacing: 0
  button-sm:
    fontFamily: Pin Sans
    fontSize: 12px
    fontWeight: 700
    lineHeight: 1
    letterSpacing: 0

rounded:
  none: 0px
  sm: 8px
  md: 16px
  lg: 32px
  full: 9999px

spacing:
  xxs: 4px
  xs: 6px
  sm: 8px
  md: 12px
  lg: 16px
  xl: 24px
  xxl: 32px
  section: 64px

components:
  button-primary:
    backgroundColor: "{colors.primary}"
    textColor: "{colors.on-primary}"
    typography: "{typography.button-md}"
    rounded: "{rounded.md}"
    padding: 6px 14px
    height: 40px
  button-primary-pressed:
    backgroundColor: "{colors.primary-pressed}"
    textColor: "{colors.on-primary}"
    typography: "{typography.button-md}"
    rounded: "{rounded.md}"
  button-secondary:
    backgroundColor: "{colors.secondary-bg}"
    textColor: "{colors.on-secondary}"
    typography: "{typography.button-md}"
    rounded: "{rounded.md}"
    padding: 6px 14px
    height: 40px
  button-secondary-pressed:
    backgroundColor: "{colors.secondary-pressed}"
    textColor: "{colors.on-secondary}"
    typography: "{typography.button-md}"
    rounded: "{rounded.md}"
  button-tertiary:
    backgroundColor: "transparent"
    textColor: "{colors.ink}"
    typography: "{typography.button-md}"
    rounded: "{rounded.md}"
  button-icon-circular:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    rounded: "{rounded.full}"
    size: 40px
  button-pill-on-image:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    typography: "{typography.button-md}"
    rounded: "{rounded.full}"
    padding: 8px 14px
  button-disabled:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ash}"
    rounded: "{rounded.md}"
  search-bar:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    typography: "{typography.body-md}"
    rounded: "{rounded.full}"
    padding: 11px 15px
    height: 48px
  search-bar-focused:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    rounded: "{rounded.full}"
  text-input:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    typography: "{typography.body-md}"
    rounded: "{rounded.md}"
    padding: 11px 15px
    height: 44px
  text-input-focused:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    rounded: "{rounded.md}"
  pin-card:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    rounded: "{rounded.md}"
    padding: 0px
  pin-card-large:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    rounded: "{rounded.lg}"
    padding: 0px
  pin-overlay-pill:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    typography: "{typography.button-sm}"
    rounded: "{rounded.full}"
    padding: 6px 12px
  filter-chip:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    typography: "{typography.button-md}"
    rounded: "{rounded.full}"
    padding: 8px 16px
  filter-chip-active:
    backgroundColor: "{colors.ink}"
    textColor: "{colors.on-dark}"
    typography: "{typography.button-md}"
    rounded: "{rounded.full}"
  category-tile:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    typography: "{typography.body-strong}"
    rounded: "{rounded.md}"
    padding: 16px
  feature-card:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    typography: "{typography.heading-xl}"
    rounded: "{rounded.md}"
    padding: 32px
  feature-card-soft:
    backgroundColor: "{colors.surface-card}"
    textColor: "{colors.ink}"
    typography: "{typography.heading-xl}"
    rounded: "{rounded.md}"
    padding: 32px
  modal-card:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    typography: "{typography.body-md}"
    rounded: "{rounded.lg}"
    padding: 32px
  hero-cta-strip:
    backgroundColor: "{colors.surface-dark}"
    textColor: "{colors.on-dark}"
    typography: "{typography.heading-xl}"
    rounded: "{rounded.none}"
    padding: 48px 32px
  primary-nav:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.ink}"
    typography: "{typography.body-strong}"
    rounded: "{rounded.none}"
    height: 64px
  footer-section:
    backgroundColor: "{colors.canvas}"
    textColor: "{colors.mute}"
    typography: "{typography.body-sm}"
    rounded: "{rounded.none}"
    padding: 32px 24px
  link-inline:
    textColor: "{colors.ink-soft}"
    typography: "{typography.link-md}"
---

## Overview

Pinterest's marketing system is built around a single instructional principle: get out of the photograph's way. The chrome is a quiet warm-cream neutral palette (`{colors.surface-soft}`, `{colors.surface-card}`, `{colors.canvas}`) carrying typography in Pinterest's proprietary Pin Sans face, with Pinterest Red (`{colors.primary}` — `#e60023`) reserved exclusively for the "Sign up" CTA, the active-tab indicator, and the sticky top-nav anchor. Every other surface is allowed to fade behind the imagery — pin tiles, category tiles, content thumbnails, profile shots — that constitutes the actual product.

The design system has two distinct surface modes that alternate down the home page: the **hero/CTA chrome** (cream surfaces, large 70px Pin Sans display headlines, alternating left/right photo-illustrated feature cards) and the **content masonry** (a column-based grid of 16px-radius pin cards on `{colors.surface-card}` with no internal padding — the pin is the card). The search results page is almost pure masonry: a tight column grid of pin imagery in mixed aspect ratios, with a small filter-chip strip at the top and the sticky red Sign-up CTA in the upper-right corner. The `create.pinterest.com` business surface inverts the grid back to a more traditional editorial layout but keeps every other rule of the system: Pin Sans, cream chrome, red CTA, 16px-radius pills.

The system's signature gesture is **shape geometry**: 16px radius (`{rounded.md}`) for nearly every surface — buttons, inputs, pin cards, feature cards — and 32px radius (`{rounded.lg}`) reserved for pin-card-large and modal cards. There are exactly three radius values in active use: 16px, 32px, and pill (9999px). The system never goes flat (sharp corners) and never goes radius-medium — those two values are the entire shape vocabulary.

**Key Characteristics:**
- Single-accent CTA: Pinterest Red (`{colors.primary}`) carries every primary action; everything else is monochrome
- Pin Sans proprietary typography across every text role from `{typography.display-xl}` (70px) down to `{typography.caption-sm}` (12px) — no serif, no monospace anywhere
- Two-radius shape system: `{rounded.md}` (16px) for most components, `{rounded.lg}` (32px) for large cards and modals, `{rounded.full}` for circular elements
- Masonry pin grid as the load-bearing visual element — column-based layout where each pin's natural aspect ratio is preserved
- Warm-cream neutral chrome (`{colors.surface-card}` — #f6f6f3) that softly recedes behind imagery without competing
- Sticky top nav with the always-red Sign-up CTA anchored in the upper-right at every breakpoint
- Modal overlay (login/signup) using a soft scrim over the page content rather than a navigation jump

## Colors

> **Source pages:** `/` (home), `/search/pins/?q=bold lip` (search results), `create.pinterest.com/` (creator marketing), `create.pinterest.com/product-features/how-to-create-boards/` (creator article). The chrome palette is identical across all four pages.

### Brand & Accent
- **Pinterest Red** (`{colors.primary}` — `#e60023`): the brand's only highly-saturated color. Sign-up CTAs, sticky top-nav anchor, active state in tab strips, and the brand wordmark.
- **Pinterest Red Pressed** (`{colors.primary-pressed}` — `#cc001f`): pressed state for the primary button — a single notch deeper than brand red.

### Surface
- **Canvas** (`{colors.canvas}` — `#ffffff`): true white. The base surface for the primary nav, modals, feature cards, and content body.
- **Soft Surface** (`{colors.surface-soft}` — `#fbfbf9`): faintly cream-tinted off-white used for the page body wash on the home page hero.
- **Surface Card** (`{colors.surface-card}` — `#f6f6f3`): warm-cream card and pin-tile background. Carries category tiles, search-bar default fill, button-secondary default, and pin-card backgrounds.
- **Secondary BG** (`{colors.secondary-bg}` — `#e5e5e0`): the gray-cream used for `{component.button-secondary}` ("I already have an account") fill — a notch deeper than `{colors.surface-card}`.
- **Secondary Pressed** (`{colors.secondary-pressed}` — `#c8c8c1`): pressed state for the secondary button.
- **Surface Dark** (`{colors.surface-dark}` — `#262622`): warm near-black used in the rare dark CTA strip on `create.pinterest.com`.
- **Hairline** (`{colors.hairline}` — `#dadad3`): 1px row dividers, footer column rules.
- **Hairline Soft** (`{colors.hairline-soft}` — `#e5e5e0`): lighter inline divider; doubles as the secondary-button background.

### Text
- **Ink** (`{colors.ink}` — `#000000`): primary headlines, button text, primary nav links.
- **Ink Soft** (`{colors.ink-soft}` — `#211922`): inline-link color in body prose. The brand's only "color" beyond Pinterest Red used in chrome — a near-black with a faint warm cast.
- **Body** (`{colors.body}` — `#33332e`): default paragraph text on `{colors.canvas}`.
- **Charcoal** (`{colors.charcoal}` — `#262622`): subtly softer body where pure ink is too heavy.
- **Mute** (`{colors.mute}` — `#62625b`): metadata text, footer links, secondary captions.
- **Ash** (`{colors.ash}` — `#91918c`): disabled button text, placeholder text in inputs.
- **Stone** (`{colors.stone}` — `#c8c8c1`): least-emphasis utility text, disabled-state borders.
- **On Dark** (`{colors.on-dark}` — `#ffffff`): primary text on `{colors.surface-dark}`.

### Semantic
- **Error** (`{colors.error}` — `#9e0a0a`): validation messages, destructive confirmation copy.
- **Error Deep** (`{colors.error-deep}` — `#cc001f`): deepened error background where the regular error tone needs more contrast. Note: this matches the primary-pressed value but in error context represents semantic destructiveness.
- **Success Deep** (`{colors.success-deep}` — `#103c25`): in-product success messaging.
- **Success Pale** (`{colors.success-pale}` — `#c7f0da`): pale success-pill background.
- **Focus Outer** (`{colors.focus-outer}` — `#435ee5`): the system's focus-ring blue — appears as a 2px outer outline around focused inputs and buttons.
- **Focus Inner** (`{colors.focus-inner}` — `#ffffff`): white inner gap inside the focus-ring stack.

### Editorial Accents (used sparingly inside content imagery and category badges)
- **Accent Pressed Blue** (`{colors.accent-pressed-blue}` — `#617bff`): pressed state for blue informational badges and editorial pin chips.
- **Accent Purple** (`{colors.accent-purple}` — `#7e238b`): editorial recommendation badge, in-product "Pinterest Predicts" callout.
- **Accent Purple Deep** (`{colors.accent-purple-deep}` — `#6845ab`): paired dark for purple lockups and "Performance+" iconography.

## Typography

### Font Family
**Pin Sans** is Pinterest's proprietary geometric sans-serif used across every text role on every page. It carries weights 400 (regular), 500 (medium), 600 (semibold), and 700 (bold), and falls back through a long stack — `-apple-system` → `system-ui` → `Segoe UI` → `Roboto` → `Helvetica Neue` → `Arial` plus emoji fallbacks. The face's distinctive trait is its tight letter-spacing at display sizes (-1.2px on `{typography.display-xl}` and `{typography.heading-xl}`), which gives 70px headlines a confident, friendly density rather than the airy spread of more conventional display geometric sans faces.

### Hierarchy

| Token | Size | Weight | Line Height | Letter Spacing | Use |
|---|---|---|---|---|---|
| `{typography.display-xl}` | 70px | 600 | 1.1 | -1.2px | Marketing hero headline ("Create the life you love on Pinterest") |
| `{typography.display-lg}` | 44px | 700 | 1.15 | -0.8px | "Where your content can thrive" creator hero |
| `{typography.heading-xl}` | 28px | 700 | 1.2 | -1.2px | Section heading ("Bring your favorite ideas to life", "Pinterest for your brand") |
| `{typography.heading-lg}` | 22px | 600 | 1.25 | 0 | Sub-section heading, modal title ("Welcome to Pinterest") |
| `{typography.heading-md}` | 18px | 600 | 1.3 | 0 | Card title, in-grid pin label |
| `{typography.body-md}` | 16px | 400 | 1.4 | 0 | Body copy, modal body, default paragraph |
| `{typography.body-strong}` | 16px | 600 | 1.4 | 0 | Inline emphasis, primary nav link, form label |
| `{typography.body-sm}` | 14px | 400 | 1.4 | 0 | Footer copy, in-grid pin metadata, helper text |
| `{typography.body-sm-strong}` | 14px | 700 | 1.4 | 0 | Search-result count label, table-header text |
| `{typography.caption-md}` | 12px | 500 | 1.5 | 0 | Caption text, link metadata |
| `{typography.caption-sm}` | 12px | 400 | 1.4 | 0 | Smallest utility text, copyright |
| `{typography.link-md}` | 16px | 600 | 1.4 | 0 | Inline anchor link in body prose |
| `{typography.button-md}` | 14px | 700 | 1 | 0 | Standard primary/secondary button label |
| `{typography.button-sm}` | 12px | 700 | 1 | 0 | Compact pill chip, in-card button |

### Principles
The system has an unusually steep size jump between display and body — `{typography.display-xl}` (70px) drops directly to `{typography.body-md}` (16px) on the home hero with no intermediate tier between. The negative tracking on the largest tiers (-1.2px / -0.8px) creates a tighter, more confident headline than a default geometric sans would deliver, and the body copy sits at a generous 1.4 line-height to keep multi-line descriptions breathing.

### Note on Font Substitutes
Pin Sans is proprietary. The closest open-source substitute is **Inter** (weights 400 / 500 / 600 / 700) — its geometry, x-height, and metric balance match Pin Sans within ~3% at body sizes. **Manrope** is a strong secondary substitute for the display tier where slightly tighter letterspacing helps the 70px headline feel weighted. Apply -1.2px tracking on the substitute at display sizes regardless of which substitute is chosen.

## Layout

### Spacing System
- **Base unit:** 8px (with finer 4/6/7px steps available for tight inline gaps in pill buttons and chips).
- **Tokens (front matter):** `{spacing.xxs}` (4px) · `{spacing.xs}` (6px) · `{spacing.sm}` (8px) · `{spacing.md}` (12px) · `{spacing.lg}` (16px) · `{spacing.xl}` (24px) · `{spacing.xxl}` (32px) · `{spacing.section}` (64px).
- **Universal section rhythm:** every page in the set uses `{spacing.section}` (64px) as the vertical gap between major content blocks. Pin grids use `{spacing.sm}` (8px) gutters between tiles — the tightest grid gutter in the system, designed so imagery effectively touches across columns.
- **Modal padding:** `{component.modal-card}` uses 32px internal padding (`{spacing.xxl}`) on all sides.

### Grid & Container
- **Max width:** ~1280px content area at desktop with 24px gutters (~48px at ultrawide).
- **Pin masonry grid:** auto-fitting column-based layout — 5–6 columns at ultrawide, 4 columns at desktop, 3 at tablet, 2 at mobile-landscape, 1 at mobile. Each tile preserves its natural aspect ratio (square / 2:3 / 3:4 / 4:5 portrait — never landscape because pins are vertically-oriented). Gutters are `{spacing.sm}` (8px) horizontal and vertical.
- **Home hero feature row:** asymmetric 2-column split where text and imagery alternate left/right down the page (text-left + image-right, then image-left + text-right, etc.).
- **Footer:** 4-column link grid at desktop, collapsing to 2-up at tablet, 1-up at mobile.

### Whitespace Philosophy
Whitespace is generous on the marketing surfaces and tight on the discovery surfaces. The home page sits sections 64px apart with photo-illustrated feature cards using 32px internal padding, while the search results page collapses to an 8px-gutter masonry grid that tiles imagery edge-to-edge. The system reads as two tools sharing the same chrome: a magazine (hero / feature / CTA / footer) and a search engine (top nav / filter row / pin grid / load more).

## Elevation & Depth

| Level | Treatment | Use |
|---|---|---|
| 0 — Flat | No border, no shadow | Default for pin cards, feature cards, footer — the dominant treatment |
| 1 — Hairline border | 1px solid `{colors.hairline}` | Inputs, footer column dividers, in-list rows |
| 2 — Modal scrim + soft shadow | Modal sits on a dark scrim over the page content with a soft 16px ambient shadow | Login / signup modal, image preview modal |
| 3 — Pin hover lift | (intentionally undocumented per system policy) | n/a |

Pinterest's system has effectively no shadow elevation in its content surfaces. Pin cards sit flat on the canvas; the only "elevation" appears on the modal layer where a 16px ambient shadow paired with a 50%-opacity scrim lifts the modal above the page content.

### Decorative Depth
Depth comes entirely from the imagery itself, not from CSS effects:
- **Pin photography** carries cinematic depth through composition (food photography, fashion close-ups, interior shots) — the design lets each tile's image speak rather than adding chrome to it.
- **Category tile thumbnails** in the home page's feature rows use Pinterest's own pin imagery as composition assets, often with a small `{component.pin-overlay-pill}` ("Cherry red", "Preppy look", "Earthy space inspo") overlaid in the corner of the image.
- **Modal scrim** — a 50%-opacity dark overlay over the entire page content when the login modal opens, with a 16px ambient shadow underneath the modal card lifting it to the visual top.

## Shapes

### Border Radius Scale

| Token | Value | Use |
|---|---|---|
| `{rounded.none}` | 0px | Footer, primary nav, page sections — all flat structural surfaces |
| `{rounded.sm}` | 8px | Rare medium-radius surface (e.g., editorial tooltip) |
| `{rounded.md}` | 16px | Buttons, inputs, pin cards, feature cards, category tiles — the dominant component radius |
| `{rounded.lg}` | 32px | Large pin cards, modal cards — used sparingly for "big" content surfaces |
| `{rounded.full}` | 9999px | Search bar, filter chips, pin overlay pills, icon-circular buttons, avatars |

The radius vocabulary is essentially three values: 16px for most things, 32px for big cards and modals, and pill for circular elements. There are no sharp-cornered buttons or sharp-cornered pin cards.

### Photography Geometry
- **Pin imagery:** mixed aspect ratios — square (1:1), portrait (3:4, 2:3, 4:5), and rare landscape — preserved at their natural ratio inside `{rounded.md}` (16px) corners on small tiles and `{rounded.lg}` (32px) on large feature pins.
- **Category tile thumbnails:** square (1:1) with `{rounded.md}` corners.
- **Avatar circles:** 32–48px at `{rounded.full}` for in-pin attribution and profile chips.
- **Feature card imagery:** typically 4:5 portrait on home-page category cards, with the photo occupying ~60% of the card and the headline + CTA stacked beneath.

## Components

> **No hover states documented** per system policy. Each spec covers Default and Active/Pressed only.

### Buttons

**`button-primary`** — the universal Pinterest CTA
- Background `{colors.primary}` (Pinterest Red), text `{colors.on-primary}`, type `{typography.button-md}`, padding `6px 14px`, height ~40px, rounded `{rounded.md}` (16px).
- Used for "Sign up", "Join Pinterest for free", "Get started" — every primary action across every surface in the system.
- Pressed state lives in `button-primary-pressed` — background drops to `{colors.primary-pressed}` (`#cc001f`).

**`button-secondary`** — gray-cream alternative
- Background `{colors.secondary-bg}` (`#e5e5e0`), text `{colors.on-secondary}`, type `{typography.button-md}`, padding `6px 14px`, height ~40px, rounded `{rounded.md}`.
- "I already have an account", "Continue", "Cancel" — second-tier actions paired with the red primary.
- Pressed state lives in `button-secondary-pressed` — background drops to `{colors.secondary-pressed}`.

**`button-tertiary`** — ghost link
- Background transparent, text `{colors.ink}`, type `{typography.button-md}`, rounded `{rounded.md}`.
- Used for low-emphasis actions inside dialogs ("Read the docs", "Learn more →" with a small chevron).

**`button-icon-circular`** — circular icon button
- Background `{colors.surface-card}`, icon `{colors.ink}`, rounded `{rounded.full}`, size 40px.
- Carousel paddles, modal close button, and small floating action buttons in pin imagery.

**`button-pill-on-image`** — small overlay pill on photography
- Background `{colors.canvas}`, text `{colors.ink}`, type `{typography.button-md}`, rounded `{rounded.full}`, padding `8px 14px`.
- The signature "Cherry red" / "Preppy look" / "Earthy space inspo" overlay pill that anchors the corner of category-tile pin imagery.

**`button-disabled`**
- Background `{colors.surface-card}`, text `{colors.ash}` — flat soft-cream.

### Filter & Tab Chips

**`filter-chip`** + **`filter-chip-active`**
- Default: background `{colors.surface-card}`, text `{colors.ink}`, type `{typography.button-md}`, rounded `{rounded.full}`, padding `8px 16px`.
- Active: background `{colors.ink}`, text `{colors.on-dark}` — the chip flips fully inverted on selection.
- Used across the search results page filter strip ("Beauty makeup", "Lipstick", "Editorial makeup"...).

### Inputs & Forms

**`text-input`** + **`text-input-focused`**
- Default: background `{colors.canvas}`, text `{colors.ink}`, 1px solid `{colors.ash}`, type `{typography.body-md}`, padding `11px 15px`, height ~44px, rounded `{rounded.md}`.
- Focused: 2px `{colors.ink}` inner border + 4px `{colors.focus-outer}` outer outline — the signature double-ring focus signal.
- Used across the login/signup modal for email, password, birthdate, country fields.

**`search-bar`** + **`search-bar-focused`**
- Default: background `{colors.surface-card}`, text `{colors.ink}`, type `{typography.body-md}`, padding `11px 15px`, height ~48px, rounded `{rounded.full}`.
- Focused: same dimensions, background flips to `{colors.canvas}` with a 1px `{colors.ash}` border.
- Anchored in the center of the primary nav with a magnifier glyph at the left edge and "Search for ideas, fashion..." placeholder.

### Cards & Containers

**`pin-card`** — the standard masonry pin tile
- Container: background `{colors.surface-card}`, rounded `{rounded.md}` (16px), padding 0.
- Layout: full-bleed image at the card's natural aspect ratio with no internal padding. Optional `{component.pin-overlay-pill}` anchored to one corner of the image, optional 32px circular avatar with profile name in `{typography.body-sm-strong}` overlaid at the bottom-left.

**`pin-card-large`** — the home-page feature pin
- Identical to `pin-card` but rounded `{rounded.lg}` (32px) — used for the large editorial pins that anchor home-page feature rows.

**`pin-overlay-pill`** — anchored chip on pin imagery
- Background `{colors.canvas}`, text `{colors.ink}`, type `{typography.button-sm}`, rounded `{rounded.full}`, padding `6px 12px`.
- Floats over a pin's bottom-left or top-left corner with the search-term label that surfaces if the pin matches a search ("Cherry red", "Preppy look", "Earthy space inspo").

**`category-tile`**
- Background `{colors.surface-card}`, rounded `{rounded.md}`, padding 16px.
- 3- or 4-up grid of small category thumbnails inside the home-page "Bring your favorite ideas to life" section. Each tile contains a category icon or composition photograph + a short label in `{typography.body-strong}`.

**`feature-card`** + **`feature-card-soft`**
- Standard: background `{colors.canvas}`, rounded `{rounded.md}`, padding 32px. Pairs a 4:5 portrait pin image (left or right) with a `{typography.heading-xl}` headline + body copy + `{component.button-primary}` red CTA.
- Soft: background `{colors.surface-card}` for the alternating-row variant where the cream surface is needed to break up content.

**`modal-card`** — login/signup overlay
- Background `{colors.canvas}`, rounded `{rounded.lg}` (32px), padding 32px.
- Layout: title in `{typography.heading-lg}` ("Welcome to Pinterest"), subtitle in `{typography.body-md}`, stacked `{component.text-input}` fields (Email, Password, Birthdate, Country), primary `{component.button-primary}` "Continue", small "Already a member? Log in" link below.
- Floats over a 50%-opacity scrim covering the entire page content with a 16px ambient shadow.

**`hero-cta-strip`** — dark CTA strip on `create.pinterest.com`
- Background `{colors.surface-dark}`, text `{colors.on-dark}`, type `{typography.heading-xl}`, padding `48px 32px`, rounded `{rounded.none}`.
- Sits at the top of the creator marketing page with a single `{component.button-primary}` red CTA on the right.

### Navigation

**`primary-nav`**
- Background `{colors.canvas}`, text `{colors.ink}`, height ~64px, type `{typography.body-strong}`, rounded `{rounded.none}`, with a 1px `{colors.hairline}` bottom rule on inner pages (no rule on the home hero).
- Layout (desktop home): Pinterest red wordmark at left + "Explore" link, centered `{component.search-bar}`, right cluster ("About / Businesses / Create / Log in" + the always-red `{component.button-primary}` "Sign up" CTA).
- Layout (search results): Pinterest red P-logo at left, centered search bar with the active query, right cluster ("Log in" + red Sign-up button).

**Top Nav (Mobile)**
- Hamburger menu icon at left, P-logo at center, search-glyph + Sign-up CTA at right. Search bar collapses into the magnifier icon and expands to full-width when tapped.

### Footer

**`footer-section`**
- Background `{colors.canvas}`, text `{colors.mute}` in `{typography.body-sm}`, padding `32px 24px`, rounded `{rounded.none}`, with a 1px `{colors.hairline}` top rule.
- Layout: 4-column link grid (Get the app — iOS / Android · Quick Links — Explore / Shop / Users / Collections / Shopping · Pinterest for · About — Privacy / Terms / Help Center) with column headers in `{typography.body-sm-strong}` and link lists in `{typography.body-sm}` `{colors.mute}`.
- Bottom row: Pinterest red wordmark + "© 2026 Pinterest" in `{typography.caption-sm}` `{colors.mute}`.

### Inline

**`link-inline`** — body-prose anchor link
- `{colors.ink-soft}` text with no underline by default. Pinterest's only "color" beyond brand red on chrome — a near-black warm tint used inline to differentiate links from body without color contrast.

## Do's and Don'ts

### Do
- Reserve `{colors.primary}` (Pinterest Red) for primary CTAs, the active-tab indicator, and the brand wordmark only. It is never decorative.
- Use `{rounded.md}` (16px) on every interactive element and standard card; reserve `{rounded.lg}` (32px) for large pin cards and modals; reserve `{rounded.full}` for circular elements (search bar, chips, avatars).
- Stage every pin image inside a `{component.pin-card}` with no internal padding — the photograph IS the card.
- Stack content sections at `{spacing.section}` (64px) rhythm; tighten pin grids to `{spacing.sm}` (8px) gutters so imagery effectively touches.
- Use `{component.pin-overlay-pill}` to anchor a search-term tag in the corner of a category-tile pin photograph — the system's signature decorative gesture.
- Build hierarchy from font weight (400 → 600 → 700) and size, not from color tinting. Body stays `{colors.body}` regardless of section context.
- Apply -1.2px letter-spacing on `{typography.display-xl}` and `{typography.heading-xl}`. The negative tracking is part of the brand voice.

### Don't
- Don't use sharp-cornered buttons or cards. There are no `{rounded.none}` interactive elements in the system.
- Don't introduce drop shadows on cards. The only shadow in the system is the 16px ambient under `{component.modal-card}`.
- Don't pad `{component.pin-card}` internally. The image is full-bleed; metadata sits over the image as an overlay pill, not below it.
- Don't replace `{colors.primary}` with another red. The brand red is precise — `#e60023`.
- Don't use `{colors.ink-soft}` (the body-prose link tint) outside of inline body anchor links. It is not a chrome color.
- Don't introduce a third radius value between 16px and 32px. The system jumps directly from md to lg with nothing in between.

## Responsive Behavior

### Breakpoints

| Name | Width | Key Changes |
|---|---|---|
| ultrawide | 1920px+ | Pin grid expands to 5–6 columns; content max-width holds at ~1280px |
| desktop-large | 1440px | Default — 4-column pin grid, full primary nav |
| desktop | 1280px | Same layout with narrower outer gutters |
| desktop-small | 1024px | Pin grid collapses to 3 columns; sub-nav remains horizontal |
| tablet | 768px | Pin grid collapses to 2 columns; primary nav becomes hamburger drawer; search bar becomes icon-only |
| mobile | 480px | Single-column pin grid; hero `{typography.display-xl}` scales 70px → ~44px |
| mobile-narrow | 320px | Hero further scales to ~36px; section padding tightens to 32px |

### Touch Targets
All interactive elements meet WCAG AA (≥ 44×44px). `{component.button-primary}` and `{component.button-secondary}` sit at ~40px height with 14px horizontal padding (effective ~40×80px tappable). `{component.search-bar}` sits at 48px. `{component.text-input}` sits at 44px. `{component.filter-chip}` is ~36–40px height with 16px padding — extends to 44px tappable via inline padding. `{component.button-icon-circular}` is exactly 40×40 with extended hit-target padding to 48×48 inside the parent.

### Collapsing Strategy
- **Primary nav:** desktop horizontal cluster → tablet hamburger drawer at 768px. The red Sign-up CTA stays visible at every breakpoint.
- **Search bar:** desktop centered (~480px wide) → tablet compressed (~320px) → mobile collapses to a magnifier icon that expands to a full-width overlay on tap.
- **Pin masonry grid:** 5/6-up → 4-up → 3-up → 2-up → 1-up at 1920, 1024, 768, and 480px. Gutters drop from 8px to 6px on mobile.
- **Home feature row:** desktop alternating left/right 2-column → tablet vertical stack with text above image → mobile single-column with full-bleed image.
- **Modal:** desktop centered ~480px-wide card → mobile full-width sheet with rounded `{rounded.lg}` top-only and bottom-anchored CTA.
- **Section padding:** `{spacing.section}` (64px) desktop → 48px tablet → 32px mobile.
- **Hero headline:** `{typography.display-xl}` (70px) at desktop, scaling 56px / 44px / 36px down the breakpoint stack.
- **Footer:** 4-up link columns → 2-up at tablet → full accordion at mobile (each header becomes a tap-to-expand row).

### Image Behavior
- Pin imagery preserves natural aspect ratio at every breakpoint; the column count changes, not the aspect.
- Category tile thumbnails maintain 1:1 across all sizes.
- Hero feature imagery uses art-direction crops on mobile (4:5 portrait → square) so the subject stays centered when the layout collapses to single-column.
- All non-critical imagery is lazy-loaded as the user scrolls into the next grid row.

## Iteration Guide

1. Focus on ONE component at a time. Pull its YAML entry and verify every property resolves.
2. Reference component names and tokens directly (`{colors.primary}`, `{component.button-primary-pressed}`, `{rounded.md}`) — do not paraphrase.
3. Run `npx @google/design.md lint DESIGN.md` after edits — `broken-ref`, `contrast-ratio`, and `orphaned-tokens` warnings flag issues automatically.
4. Add new variants as separate component entries (`-pressed`, `-disabled`, `-focused`) — do not bury them inside prose.
5. Default body to `{typography.body-md}`; reach for `{typography.body-strong}` for emphasis; reserve `{typography.display-xl}` strictly for top-of-page hero headlines.
6. Keep `{colors.primary}` scarce — at most one Pinterest-red CTA per fold (counting nav, hero, and feature-card CTAs together).
7. When introducing a new component, ask whether it can be expressed with the existing pin-card + 16px-radius + cream-surface vocabulary before adding new tokens. The system's strength is that it almost never needs new ones.

## Known Gaps

- **Mobile screenshots not captured** — responsive behavior synthesizes Pinterest's known mobile pattern (hamburger drawer, single-column grid, hero downscale) from desktop evidence and the documented breakpoint stack.
- **Hover states not documented** by system policy.
- **Pin-detail close-up (single pin overlay)** is not in the captured set — the in-product Pin detail view (with comments, related pins, save board picker) likely introduces components not documented here.
- **Authenticated chrome** (logged-in home feed, board pages, profile pages) not in the captured pages — the captured surfaces are the logged-out marketing and search experience.
- **Pinterest mobile app screens** not in the system documented here — this is the web-only chrome.
- **Form validation states** (success / error inline messages) not documented; only the focused-state field is captured.
