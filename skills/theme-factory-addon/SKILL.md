---
name: theme-factory-addon
description: Expansion pack of 100 curated color and font themes for the theme-factory skill, organized into 14 categories spanning seven aesthetic families (Earthy, Feminine, Coastal, Bold, Boho, Vintage, Luxury), Iconic Brands (Facebook, Instagram, Tesla, Nike, McDonald's, Spotify, Google, Netflix, Coca-Cola), developer/editor/terminal themes (Dracula, Nord, Gruvbox, Tokyo Night, Catppuccin, Solarized, Monokai, One Dark, Synthwave 84), Master Painters (Rothko, Pollock, Picasso, Rembrandt, Van Gogh, Monet, Klimt, Vermeer, Hokusai, Matisse, Frida Kahlo, Mondrian), and Directors & Cinematographers (Spielberg, Scorsese, Nolan, Deakins, Kubrick, Tarantino, Fincher, Villeneuve). Use ALONGSIDE theme-factory to style slides, docs, reports, or HTML when its 10 built-in themes are not enough, or when the user asks for a boho, luxury, vintage, brand, code-editor, dark/terminal, fine-art, or cinematic look. Each theme provides a hex palette, a header/body font pairing, and a light or dark mode.
license: Apache-2.0
triggers:
  - "more themes"
  - "additional themes"
  - "theme addon"
  - "boho theme"
  - "luxury theme"
  - "vintage theme"
  - "aesthetic theme"
  - "brand theme"
  - "brand colors"
  - "code theme"
  - "editor theme"
  - "dark theme"
  - "terminal theme"
---

# Theme Factory Add-On

An **expansion pack** for the upstream `theme-factory` skill. It does not replace
theme-factory — it extends its theme library with 100 additional professionally
curated themes, each in the *exact same file format* as the built-in themes, so
they apply through the identical workflow.

## Relationship to theme-factory

- **theme-factory** ships 10 built-in themes + a `theme-showcase.pdf` and owns
  the application workflow (show options → confirm choice → apply colors/fonts).
- **theme-factory-addon** (this skill) adds 100 more themes under `themes/`.
- When a user wants to theme an artifact, treat the two libraries as **one
  combined catalogue**. Offer the built-in 10 *and* these 100. Apply whichever
  the user picks using theme-factory's normal application process.

## What it adds (100 themes, 14 categories)

**Earthy & Grounded** — Mountain Air · Desert Dunes · Serene Nature · Mellow Greens
**Feminine & Soft** — Soft Crimson · Beautiful Blush · Sunset Lovers · Salty Pink
**Coastal & Calm** — High Seas · Calm Sapphire · Around the Riverbend · Sandy Shores
**Bold & Fun** — Summer Daze Pink · Joyful Boho · Fresh Fusion · Modern Pop
**Modern Boho & Neutrals** — Mystic Earth · Modern Boho · Sandy Neutrals · Perfectly Peach
**Vintage Romance** — Gothic Vintage · Passionfruit Pie · Modern Mystic · Eclectic Muse
**Luxury & Sophisticated** — Warm Linen · Emerald Manor · Crimson Silk · Midnight Harbor · Gilded Age · Velvet Teal · Jewel Box · Mauve Garden · Slate Mist · Quiet Luxury
**Iconic Brands** — Facebook · Instagram · Twitter X · Tesla · McDonald's · Nike · Spotify · Google · Netflix · Coca-Cola · Slack · Starbucks · Amazon · Airbnb
**Editor Classics (Dark)** — Dracula · One Dark Pro · Monokai · Nord · Gruvbox Dark · Tokyo Night · Catppuccin Mocha · Night Owl · GitHub Dark · Solarized Dark
**Editor Light** — GitHub Light · Solarized Light · Atom One Light · Catppuccin Latte · Rosé Pine Dawn
**Neon & Retro** — Synthwave 84 · Cobalt2 · Shades of Purple · Spaceduck · Horizon
**Obsidian & Calm** — Everforest · Things · Minimal · Blue Topaz · Primary · AnuPpuccin
**Master Painters** — Rothko · Pollock · Picasso Blue Period · Picasso Rose Period · Rembrandt · Van Gogh · Monet · Klimt · Vermeer · Hokusai · Matisse · Frida Kahlo · Mondrian
**Directors & Cinematographers** — Spielberg · Scorsese · Nolan · Deakins · Slocombe · Kubrick · Tarantino · Fincher · Lubezki · Storaro · Wong Kar-wai · Gordon Willis · Villeneuve

Each theme file (`themes/<name>.md`) contains:
- A cohesive color palette with hex codes, ordered by role from **background to
  foreground/text**. Each theme is tagged `Mode: light` or `Mode: dark` — for
  dark themes the darkest color is the background and the lightest is the text.
- A header/body font pairing.
- A "Best Used For" note and its category.

## How to use

1. **Browse + offer.** When a user asks to style an artifact, present the
   combined catalogue (theme-factory's 10 + these 100). **Show this skill's
   `theme-showcase.pdf`** so the user can see all 100 add-on themes visually
   (one page per theme, grouped by category) — do not modify it, just display
   it for viewing. If theme-factory's own `theme-showcase.pdf` is available,
   show that too for the original 10.
2. **Confirm the choice.** Get explicit confirmation of the single theme to use.
3. **Read the theme file.** Open `themes/<chosen-name>.md` from this skill (or
   the matching file from theme-factory for a built-in theme).
4. **Apply** the palette and fonts consistently across the artifact, following
   theme-factory's application process. Use the role labels to map colors:
   *Base/background* for surfaces, *Anchor/text* for type, accents for emphasis.
   Maintain strong contrast and readability.

## A note on fonts

Unlike the built-in themes (which all render with **DejaVu Sans / DejaVu Sans
Bold**), each add-on theme specifies a *recommended* Google Font pairing chosen
to match its aesthetic (e.g. Playfair Display + EB Garamond for Vintage
Romance; Bodoni Moda + Montserrat for Luxury). 

**If your rendering pipeline does not have these fonts installed** (e.g. the
PDF/slide generator only bundles DejaVu), fall back to **DejaVu Sans Bold**
for headers and **DejaVu Sans** for body — the palette still carries the
theme's identity. Treat the font pairing as a design recommendation, not a
hard requirement.

## Regenerating / editing the library

All 100 themes are emitted from a single source-of-truth table in
`generate_themes.py`. To add, rename, recolor, or re-categorize themes, edit
the `THEMES` / `CATEGORY_FONTS` tables and run:

```bash
python3 generate_themes.py      # rebuild themes/*.md
python3 generate_showcase.py    # rebuild theme-showcase.html from the same data
# then print the HTML to PDF with headless Chrome:
"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome" --headless=new \
  --disable-gpu --no-pdf-header-footer --run-all-compositor-stages-before-draw \
  --virtual-time-budget=25000 --print-to-pdf=theme-showcase.pdf \
  "file://$PWD/theme-showcase.html"
```

Color roles are assigned automatically by luminance, so you only need to supply
each color's name and hex — ordering is handled for you. The showcase pulls the
real Google Fonts each theme specifies, so it reflects the intended typography.

## Note on the duplicated source palette

The Brand Alchemists published "Sunset Lovers" with hexes identical to
"Beautiful Blush". Rather than ship a literal duplicate, **Sunset Lovers has
been re-tinted** into a true golden-hour gradient (peach → apricot → coral →
plum dusk) so it is a genuinely distinct theme. Every other palette is
lifted verbatim from its source.

## Note on the Iconic Brands category

The 14 themes in **Iconic Brands** reproduce publicly documented brand colors
(verified hex codes) purely as a **design reference / starting point**. All
brand names and colors are the property of their respective owners. Do not
present work themed this way as affiliated with, or endorsed by, those brands —
use them for inspiration, internal mockups, and study, not for passing off.

## Note on the editor / terminal themes

The four developer categories (**Editor Classics Dark, Editor Light, Neon &
Retro, Obsidian & Calm**) reproduce community theme palettes as a design
reference. Dracula, Nord, Gruvbox, Tokyo Night, Catppuccin, Solarized, Monokai,
One Dark, Night Owl, GitHub, Rosé Pine, Everforest, Synthwave 84, Cobalt2,
Shades of Purple, Spaceduck, and Horizon use each project's **official published
hex spec**. The Obsidian-native themes **Things, Minimal, Blue Topaz, Primary,
and AnuPpuccin** are highly customizable layout/typography themes with no single
canonical palette — those five are faithful **approximations** of each theme's
signature look, not official specs. All theme names belong to their respective
authors; these palettes are for inspiration and study.

## Note on the Master Painters category

The 13 **Master Painters** themes are palettes **derived** from each artist's
iconic work (dominant colors hand-picked) — there is no canonical hex spec for a
painting, so these are faithful *evocations* for design use, not reproductions.
Most source works (Van Gogh, Vermeer, Hokusai, Rembrandt, etc.) are in the
public domain. Picasso appears as two themes for his distinct **Blue** and
**Rose** periods.

## Note on the Directors & Cinematographers category

The 13 **Directors & Cinematographers** themes are palettes **derived** from
each filmmaker's signature look across their body of work (e.g. Deakins'
orange-and-teal from *Blade Runner 2049*, Kubrick's Overlook palette from *The
Shining*, Storaro's saturated *Apocalypse Now*). They are evocations for design
use, not frame-accurate reproductions, and all names belong to the respective
artists. The set mixes directors (Spielberg, Scorsese, Nolan, Kubrick,
Tarantino, Fincher, Wong Kar-wai, Villeneuve) with celebrated cinematographers
(Deakins, Slocombe, Lubezki, Storaro, Gordon Willis).

## Sources

Palettes lifted from:
- The Brand Alchemists — "24 Aesthetic Colour Palettes" (the 6 aesthetic categories)
- Steph Corrigan Design — "10 Sophisticated Colour Palettes for Luxury Branding"
- Documented official brand colors (Iconic Brands), cross-checked against
  usbrandcolors.com, brandpalettes.com, and encycolorpedia.
- Official editor/terminal theme specs (Dracula, Nord, Catppuccin, Gruvbox,
  Solarized, Tokyo Night, Rosé Pine, Everforest, GitHub, etc.); Obsidian-native
  themes approximated from their published look.
- Master Painters palettes derived from each artist's iconic public-domain works.

Names, color roles, font pairings, and "best used for" guidance were authored
for this pack.
