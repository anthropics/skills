---
name: html-to-pdf-hires
description: Convert an HTML file or URL to a pixel-perfect, high-DPI rasterized PDF by screenshotting each page element at 3x device-pixel-ratio and embedding the PNGs full-bleed into an A4 PDF. Supports slide-style decks where only one element is visible at a time via an active class (use --activate-class=<name>). Use this skill when the user asks to "turn HTML into PDF", "make a PDF from this HTML", "convert to PDF", "generate a crisp PDF", "export to PDF at high resolution", "convert presentation/deck to PDF", or complains that a previously generated vector PDF looks blurry / low-res / fuzzy in their PDF viewer. Output is pixel-identical to the browser at every zoom level — no font-hinting surprises, no viewer-dependent blur. Trade-off: larger file size and non-selectable text compared to vector PDFs.
---

# HTML to PDF (Hi-Res Raster)

Replicates the exact workflow that produces pixel-perfect PDFs: render in Chrome at 3x DPR, screenshot each `.page` element, embed the PNGs full-bleed into a fresh A4 PDF.

## Setup (one-time)

From the skill folder:

```bash
npm install
```

## Usage

Run `scripts/convert.js` from the skill folder:

```bash
# Local file
node scripts/convert.js input.html output.pdf

# URL (preferred when HTML loads web fonts — ensures proper loading)
node scripts/convert.js http://localhost:8765/doc.html output.pdf

# Custom DPR (default 3)
node scripts/convert.js input.html output.pdf --dpr=4

# Landscape
node scripts/convert.js input.html output.pdf --landscape

# Custom selector (default ".page")
node scripts/convert.js input.html output.pdf --selector=".slide"

# Custom format
node scripts/convert.js input.html output.pdf --format=Letter

# Extra wait for fonts / JS (default 2500ms)
node scripts/convert.js input.html output.pdf --wait=4000

# Slide deck where only one element is visible at a time (e.g. .slide.active)
node scripts/convert.js deck.html deck.pdf \
  --selector=.slide --activate-class=active --landscape
```

## Options

| Flag | Default | Description |
|---|---|---|
| `--dpr=<n>` | `3` | Device pixel ratio for screenshot rasterization |
| `--format=<name>` | `A4` | Page format: A4, A3, A5, Letter, Legal |
| `--landscape` | off | Landscape orientation |
| `--selector=<css>` | `.page` | Element selector — one screenshot per match. Falls back to full-page screenshot if no matches |
| `--wait=<ms>` | `2500` | Extra wait after load for fonts/JS |
| `--activate-class=<name>` | none | Slide-deck mode. Before each screenshot, toggle this class on the matched element and remove it from the others. Uses viewport (not element) screenshots — correct for decks using `opacity` + `position:absolute` to stack slides |
| `--activate-delay=<ms>` | `400` | Delay between activating an element and taking its screenshot |

## Required HTML structure for multi-page output

Each page of the PDF corresponds to one matching element. For best results, wrap each page in a div with the selector class and lock its exact physical size:

```css
.page {
  width: 210mm;
  height: 297mm;
  overflow: hidden;
}
```

If `.page` uses `min-height` instead of `height`, content may overflow and the screenshot grows taller than A4 — resulting in clipped or oddly-scaled pages. Always use `height` with `overflow: hidden`.

## Verify after every run

Read the generated PDF and check:
- Correct page count (one per `.page` element)
- No clipped content at page edges
- Gradients, logos, and text all appear crisp

If a page looks clipped or stretched, the source `.page` element's physical dimensions don't match the chosen format — fix the HTML CSS, don't apply scale in the script.

## How it works

1. Launch Puppeteer headless with `--font-render-hinting=none --disable-font-subpixel-positioning --force-color-profile=srgb`
2. Set viewport matching the format at `deviceScaleFactor=<dpr>`
3. Load the URL/file, wait for `load + networkidle0`, then `document.fonts.ready`, then `--wait` ms
4. `$$(selector)` → screenshot each matched element as PNG (default)
   - **With `--activate-class=<name>`**: disable transitions, cycle the class across matches (`classList.toggle(name, j === idx)` for each), then screenshot the viewport after `--activate-delay` ms
   - **No matches**: fall back to full-page screenshot
5. Close browser, build a temporary HTML containing `@page { size: <format>; margin: 0 }` and one full-bleed `<img>` per screenshot
6. Launch a second headless instance, load the composed HTML, and `page.pdf()` with `preferCSSPageSize: true, printBackground: true, scale: 1, margin: 0`
