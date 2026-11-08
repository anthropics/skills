# html-to-pdf-hires

A [Claude Code](https://docs.claude.com/en/docs/claude-code) skill that converts HTML files or URLs into pixel-perfect, high-DPI rasterized PDFs.

Each `.page` element is screenshotted at 3x device-pixel-ratio and embedded full-bleed into a fresh A4 PDF. Output is pixel-identical to the browser at every zoom level — no font-hinting surprises, no viewer-dependent blur.

**Trade-off:** larger file size and non-selectable text compared to vector PDFs. Use this when crispness matters more than text selection (presentations, marketing decks, designed reports).

## Install

```bash
git clone https://github.com/MMTTGL/html-to-pdf-hires ~/.claude/skills/html-to-pdf-hires
cd ~/.claude/skills/html-to-pdf-hires
npm install
```

> **Windows users:** the path resolves to `C:\Users\<you>\.claude\skills\html-to-pdf-hires`. Use Git Bash or PowerShell with the equivalent path.

> **Behind a corporate proxy / locked-down network?** Puppeteer downloads its own Chromium (~170 MB). To skip and use a system Chrome instead:
> ```bash
> PUPPETEER_SKIP_DOWNLOAD=true npm install
> # then point at your Chrome via PUPPETEER_EXECUTABLE_PATH
> ```

## Use it from Claude Code

Just ask Claude any of:

- "convert this HTML to a hi-res PDF"
- "the PDF you made looks blurry, redo it crisper"
- "export this deck to PDF at 4x DPR"

Claude will pick up the skill automatically based on the description.

## Use it from the command line

```bash
# Local file
node scripts/convert.js input.html output.pdf

# URL (preferred when HTML loads web fonts)
node scripts/convert.js http://localhost:8765/doc.html output.pdf

# Custom DPR
node scripts/convert.js input.html output.pdf --dpr=4

# Landscape
node scripts/convert.js input.html output.pdf --landscape

# Custom selector (default ".page")
node scripts/convert.js input.html output.pdf --selector=".slide"

# Letter format
node scripts/convert.js input.html output.pdf --format=Letter

# Extra wait for fonts / JS
node scripts/convert.js input.html output.pdf --wait=4000
```

### Options

| Flag | Default | Description |
|---|---|---|
| `--dpr=<n>` | `3` | Device pixel ratio for screenshot rasterization |
| `--format=<name>` | `A4` | Page format: A4, A3, A5, Letter, Legal |
| `--landscape` | off | Landscape orientation |
| `--selector=<css>` | `.page` | Element selector — one screenshot per match. Falls back to full-page screenshot if no matches |
| `--wait=<ms>` | `2500` | Extra wait after load for fonts/JS |

## HTML structure

For multi-page output, wrap each page in a div with the chosen selector and lock its exact physical size:

```css
.page {
  width: 210mm;
  height: 297mm;
  overflow: hidden;
}
```

Use `height` (not `min-height`) with `overflow: hidden`, otherwise content can overflow and the screenshot grows taller than A4 — leading to clipped or oddly-scaled pages.

## How it works

1. Launches Puppeteer headless with `--font-render-hinting=none --disable-font-subpixel-positioning --force-color-profile=srgb`
2. Sets viewport matching the format at `deviceScaleFactor=<dpr>`
3. Loads the URL/file, waits for `load + networkidle0`, then `document.fonts.ready`, then `--wait` ms
4. Screenshots each `.page` element as PNG (or full-page fallback)
5. Builds a temporary HTML containing `@page { size: <format>; margin: 0 }` and one full-bleed `<img>` per screenshot
6. Loads the composed HTML in a fresh headless instance and exports with `preferCSSPageSize: true, printBackground: true, scale: 1, margin: 0`

## License

MIT — see [LICENSE](./LICENSE).
