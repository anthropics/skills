---
name: screenshot-to-html
description: >
  Converts a product UI screenshot into a pixel-faithful, fully editable HTML file,
  then renders it as a PNG image asset ready for use on a website or in marketing materials.

  Use this skill whenever the user:
  - Uploads a product screenshot and wants to recreate it in HTML
  - Wants a "marketable" or "polished" version of a product UI
  - Asks to turn a screenshot into an editable file
  - Wants to generate a PNG/image from a product UI for use on a website
  - Asks to "stylise", "rerender", "recreate" or "clean up" a screenshot
  - Mentions phrases like "product screenshot", "dashboard asset", "marketing asset", "UI mockup"

  Output: a self-contained HTML file with CSS variables for easy editing, plus a PNG rendered
  via headless Chromium (1x and 2x/retina). Colors, spacing, and all UI values are sampled
  directly from the source screenshot pixels — never guessed.
---

# Screenshot → HTML → PNG

Converts a product UI screenshot into a pixel-faithful, editable HTML file and renders it
as a polished marketing asset PNG. All colors are sampled from the actual image.

---

## Step 1 — Understand the screenshot

When the user uploads a screenshot, first ask (if not already clear):

1. **Which section to feature?** (e.g. "the full dashboard", "just the top stats row", "the policy panel")
2. **Background context** — dark surroundings or light? (determines the presentation frame glow color)
3. **Crop** — remove chrome like sidebars, top navigation, scrollbars? (almost always yes for marketing use)

Do not proceed until you know which section to feature. One question at a time if ambiguous.

---

## Step 2 — Analyse the screenshot

Run `scripts/analyse.py` with the uploaded image path to:
- Detect overall image dimensions
- Sample key UI colors at strategic coordinates
- Find bright/colored pixels (accents, tags, icons, progress bars)
- Identify the crop boundaries (sidebar width, topbar height, scrollbar)

```bash
python3 scripts/analyse.py <image_path>
```

Read the output carefully. The color values it returns are ground truth — use them verbatim
in the HTML CSS variables. Do not substitute with assumed brand colors.

---

## Step 3 — Crop the image (if requested)

If the user wants the sidebar/topbar removed, use the crop values from Step 2:

```python
from PIL import Image
img = Image.open(path)
cropped = img.crop((left, top, right, bottom))
cropped.save("/tmp/cropped.jpg", quality=92)
```

---

## Step 4 — Build the HTML

Build a **single self-contained HTML file** with:

### Structure
```
<html>
  <head>
    <style> :root { --tokens } ... all CSS ... </style>
  </head>
  <body>
    <div class="wrap">          ← outer glow + max-width
      <div class="chrome">      ← rounded border + shadow
        <div class="browser-bar"> ← 3 dots
        <div class="dashboard"> ← the actual UI recreation
```

### CSS tokens (`:root`)
All colors go here as named variables — never hardcode hex values in component CSS.
Pull these directly from the analyser output:
- `--bg` — main background
- `--bg-panel` — card/panel surface
- `--border` — panel border (rgba)
- `--text-primary` — main text
- `--text-secondary` — muted labels
- `--text-muted` — very faint labels
- One variable per accent color: `--blue`, `--amber`, `--green`, `--red`, etc.
- Semantic tag backgrounds: `--tag-amber-bg`, etc.

### Presentation frame
Wrap the dashboard in a dark outer container with:
- Radial gradient glow behind (color matches the dominant UI accent)
- `border-radius: 10px` chrome border
- `box-shadow` for depth
- 3-dot browser bar at top

### UI components
Recreate each section faithfully:
- **Stat cards**: 4-column grid, value in large bold type, label + icon
- **Bar charts**: fixed-height container (`overflow: hidden`), labels in a separate row *outside* the height-constrained area (prevents bars exceeding the ceiling)
- **Lists** (policies, audits, frameworks): border-bottom rows, tag badges, progress bars
- **Tags/badges**: correct background + text color per state (Draft, Approved, Pending, In Progress)
- **Progress bars**: track color from `--grey-track`, fill from `--blue`
- **Icons**: inline SVG, stroke color matches the stat's accent

### Realism rules
- Replace any test/dev/placeholder usernames with realistic generic names (e.g. "M. Okafor", "S. Dhillon")
- Keep all real data values (counts, dates, percentages, framework names)
- Truncate long descriptions with `...` as in the original

### Bar chart ceiling fix
This is a known gotcha — always implement it:
```html
<!-- labels OUTSIDE the height-constrained bars container -->
<div class="chart-inner" style="height:128px; overflow:hidden;">
  <div class="chart-y">...</div>
  <div class="bars">
    <div class="bar-group"><div class="bar-cols">...</div></div>
  </div>
</div>
<div class="bar-labels">  ← outside chart-inner
  <div class="bar-lbl">Operational Tasks</div>
  ...
</div>
```

Bar heights must be calculated as: `value / max_value * chart_height_px`

---

## Step 5 — Render to PNG

Use Playwright headless Chromium to render the HTML. Always generate both 1x and 2x:

```bash
python3 scripts/render.py <html_path> <output_dir>
```

This produces:
- `dashboard.png` — standard resolution
- `dashboard@2x.png` — retina (device_scale_factor=2)

Recommend the `@2x` version for website use.

---

## Step 6 — Deliver

Present both PNG files with `present_files`. Brief summary only — the user can see the files.

If the user asks for adjustments (wrong bar height, wrong color, different crop), edit the HTML
directly and re-run the renderer. No need to redo the full analysis.

---

## Common adjustments

| Issue | Fix |
|-------|-----|
| Bar exceeds gridline | Reduce bar `height` value in HTML; verify chart-inner has `overflow:hidden` |
| Wrong accent color | Re-sample that pixel region; update the CSS variable |
| Sidebar still visible | Tighten left crop value by 5–10px increments |
| Text too small | Increase font-size on `.stat-value` or `.item-name` |
| Glow wrong color | Change the radial-gradient color in `.wrap::before` |

---

## Quality checklist

Before delivering:
- [ ] All colors traced to sampled pixels, not assumed
- [ ] No test/dev usernames in the output
- [ ] Bar chart labels are outside the overflow-hidden container
- [ ] Tallest bar is visibly below its gridline ceiling (not touching or exceeding)
- [ ] Both 1x and 2x PNGs generated
- [ ] HTML opens in browser without errors
