#!/usr/bin/env python3
"""
Build preview.html: a single-sheet contact grid of all themes (name + color
swatch strip), sized to an exact page so it renders to one clean PNG.

Render:
  python3 generate_preview.py
  chrome --headless=new --no-pdf-header-footer --print-to-pdf=preview.pdf \
         "file://$PWD/preview.html"
  pdftoppm -png -r 96 -f 1 -l 1 preview.pdf assets/screenshots/overview
"""
import os
from generate_themes import THEMES, theme_mode

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "preview.html")

COLS = 5
PAD = 30
TITLE_H = 86
CARD_H = 96
GAP = 14
W = 1600


def build():
    import math
    rows = math.ceil(len(THEMES) / COLS)
    H = PAD + TITLE_H + rows * CARD_H + (rows - 1) * GAP + PAD

    cards = []
    for name, desc, category, colors, *rest in THEMES:
        mode = theme_mode((name, desc, category, colors, *rest))
        chips = "".join(
            f'<span style="flex:1;background:{c[1]};"></span>' for c in colors
        )
        badge = "●" if mode == "dark" else "○"
        cards.append(f'''
          <div class="card">
            <div class="name">{name} <span class="mode">{badge}</span></div>
            <div class="strip">{chips}</div>
            <div class="cat">{category}</div>
          </div>''')

    html = f'''<!DOCTYPE html><html><head><meta charset="utf-8">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;600;700&display=swap" rel="stylesheet">
<style>
  @page {{ size: {W}px {H}px; margin: 0; }}
  * {{ box-sizing: border-box; }}
  body {{ margin: 0; font-family: 'Inter', sans-serif;
         background: #0f1115; color: #e6e8ec; width: {W}px; height: {H}px; }}
  .sheet {{ padding: {PAD}px; }}
  .title {{ font-size: 30px; font-weight: 700; margin: 0; }}
  .sub {{ font-size: 15px; color: #9aa0a6; margin: 4px 0 0; }}
  .grid {{ display: grid; grid-template-columns: repeat({COLS}, 1fr);
           gap: {GAP}px; margin-top: 22px; }}
  .card {{ height: {CARD_H}px; background: #171a21; border: 1px solid #242a33;
           border-radius: 8px; padding: 10px 12px; overflow: hidden; }}
  .name {{ font-size: 13px; font-weight: 600; white-space: nowrap;
           overflow: hidden; text-overflow: ellipsis; }}
  .mode {{ color: #6b7280; font-size: 10px; }}
  .strip {{ display: flex; height: 34px; border-radius: 4px; overflow: hidden;
            margin: 8px 0 6px; border: 1px solid rgba(255,255,255,0.06); }}
  .cat {{ font-size: 10px; color: #6b7280; letter-spacing: 0.04em;
          white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
</style></head>
<body><div class="sheet">
  <h1 class="title">theme-factory-addon</h1>
  <p class="sub">100 curated themes · 14 categories · ● dark / ○ light · companion to Anthropic's theme-factory</p>
  <div class="grid">{"".join(cards)}</div>
</div></body></html>'''
    open(OUT, "w").write(html)
    print(f"Wrote {OUT}  (page {W}x{H}, {len(THEMES)} cards)")


if __name__ == "__main__":
    build()
