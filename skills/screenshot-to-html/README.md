# screenshot-to-html

Converts a product UI screenshot into a pixel-faithful, fully editable HTML file, then renders it as a PNG asset for websites or marketing materials.

Colors, spacing, and all UI values are sampled directly from the source screenshot pixels — never guessed. Output includes a self-contained HTML file with CSS variables for easy editing, plus 1x and 2x/retina PNGs rendered via headless Chromium.

**Triggers on:** uploading a product screenshot, "stylise this UI", "marketing asset from screenshot", "recreate this dashboard".

See [SKILL.md](SKILL.md) for full instructions. Helper scripts live in [`scripts/`](scripts/):
- `analyse.py` — sample colors and structure from the source image
- `render.py` — render the HTML to PNG via headless Chromium

## Requirements

- Python 3
- Playwright with Chromium (`pip install playwright && playwright install chromium`)
