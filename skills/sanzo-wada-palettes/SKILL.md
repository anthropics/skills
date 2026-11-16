---
name: sanzo-wada-palettes
description: Pick, preview, and apply color palettes from Sanzo Wada's A Dictionary of Color Combinations (348 combos, 159 colors) to websites, Tailwind/shadcn themes, designs, or outfits, with a live theme-switcher button for testing.
license: Complete terms in LICENSE.txt
---

# Sanzo Wada palettes

Use this when the user wants a color scheme "from the Wada book", a Sanzo Wada palette, a specific combination number, or a tasteful palette for a site, brand, design, or outfit.

## 1. Get the data

Source: mattdesl/dictionary-of-colour-combinations (MIT license). Clone it into its own empty folder:

```bash
mkdir -p /tmp/wada && git clone --depth 1 -q https://github.com/mattdesl/dictionary-of-colour-combinations /tmp/wada/repo
```

Fallback: `npm install dictionary-of-colour-combinations` in an empty folder.

`colors.json` is an array of 159 colors:

```json
{"name": "Hermosa Pink", "combinations": [176, 227, 273], "swatch": 0,
 "cmyk": [0,30,6,0], "lab": [...], "rgb": [249,193,206], "hex": "#f9c1ce"}
```

Palettes are not stored directly. Combination N is every color whose `combinations` list contains N:

```python
import json, collections
colors = json.load(open('/tmp/wada/repo/colors.json'))
combos = collections.defaultdict(list)
for c in colors:
    for n in c['combinations']:
        combos[n].append(c)
# combos[n] -> list of 2, 3, or 4 colors
```

Run Python with `-I`, and keep scripts outside the cloned folder.

## 2. Choose palettes

- If the user gives a combination number, use it directly.
- Otherwise, filter by what they asked for: color count (2, 3, or 4), mood (warm/cool by hue, muted/bold by LAB chroma), or a color they want to include (closest by LAB distance).
- Pick 5–10 candidates for the switcher (step 4). If not building a site, show 3–5 as inline swatches (hex, name, combo number).
- For UI work, check text contrast with WCAG ratios: 4.5:1 for body text. Use the lightest or darkest color as the background. Fix a failing pair by deriving a lighter/darker tint of a palette color for text, and note it.

## 3. Map each palette to a theme

For web work (Tailwind/shadcn by default), turn every candidate palette into a full set of shadcn CSS variables: `--background`, `--foreground`, `--card`, `--card-foreground`, `--primary`, `--primary-foreground`, `--secondary`, `--secondary-foreground`, `--accent`, `--accent-foreground`, `--muted`, `--muted-foreground`, `--border`, `--ring`. Use the color format the project already uses (HSL or OKLCH). If a palette has no near-white or near-black, derive tints/shades from its own colors instead of using pure gray.

Write all themes to one file, e.g. `lib/wada-themes.ts`:

```ts
export const wadaThemes = [
  { id: 176, name: "Hermosa Pink / ...", swatches: ["#f9c1ce", ...], vars: { "--background": "...", ... } },
  ...
];
```

## 4. Add the theme switcher (always, for web work)

Build a client component `components/wada-theme-switcher.tsx` and render it once in the root layout.

Behavior:
- A small floating button in the bottom-right corner (high z-index, its own fixed neutral styling so it stays readable on every theme).
- Clicking opens a panel listing each theme: combo number, name, and its swatches as small circles. Clicking a theme applies it instantly by setting its `vars` on `document.documentElement.style`.
- Prev/next arrows plus keyboard shortcuts (`[` and `]`) to cycle through themes quickly.
- A "Default" option that removes the inline variables to restore the site's original theme.
- Remember the selected theme in `localStorage` (wrapped in try/catch) so it survives page navigation and reloads.
- A "Copy CSS" button that copies the current theme as a ready-to-paste `:root { ... }` block for `globals.css`, with the combo number in a comment.
- Visibility: show it when `process.env.NODE_ENV !== "production"` OR the URL has `?themes=1`. This lets the user test on a live Vercel preview and share the link with a client, while normal visitors never see it.

When the user picks a winner ("lock in 176"), write that theme's variables into `globals.css` as the default. Ask whether to remove the switcher and `wada-themes.ts` or keep them behind `?themes=1`.

## Other outputs

- **Plain CSS sites:** the same switcher in vanilla JS, setting custom properties on `:root`.
- **Design / print:** list hex, RGB, and CMYK per color with the combination number.
- **Outfits / non-digital:** describe each color in plain words and which item it suits (base, main, accent).

Always cite the combination number(s) so the user can find them in the book.

## Notes

- Hex values are digitized approximations. The printed book's CMYK values are the reference.
- Color names come from the dataset. Don't invent Japanese names.