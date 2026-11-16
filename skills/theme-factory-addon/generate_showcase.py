#!/usr/bin/env python3
"""
Generate theme-showcase.html for the add-on theme library, mirroring the layout
of theme-factory's own theme-showcase.pdf: one page per theme with a full-bleed
background, a large title in the theme's header font, a row of color swatches
(name + hex), a Typography section with live samples, and a "Best for" footer.

Pulls the real Google Fonts each theme specifies so the showcase reflects the
actual intended typography. Render to PDF with headless Chrome (see make_showcase.sh
or the command printed at the end of this file's docstring).

Run:  python3 generate_showcase.py
"""

import os
from generate_themes import THEMES, CATEGORY_FONTS, luminance

HERE = os.path.dirname(os.path.abspath(__file__))
OUT_HTML = os.path.join(HERE, "theme-showcase.html")

# Google Fonts to load: (family, request_weights?)
FONT_FAMILIES = {
    "Fraunces": True, "Karla": True, "Cormorant Garamond": True,
    "Nunito Sans": True, "Quicksand": True, "Open Sans": True,
    "Poppins": True, "Work Sans": True, "Marcellus": False, "Mulish": True,
    "Playfair Display": True, "EB Garamond": True, "Bodoni Moda": True,
    "Montserrat": True,
    # dev / editor / terminal categories
    "JetBrains Mono": True, "Inter": True, "Fira Code": True,
    "Space Mono": True, "IBM Plex Mono": True, "IBM Plex Sans": True,
    # master painters
    "Spectral": True,
    # directors & cinematographers
    "Oswald": True, "Barlow": True,
}


def gfonts_url():
    parts = []
    for fam, weights in FONT_FAMILIES.items():
        f = fam.replace(" ", "+")
        parts.append(f"family={f}:wght@400;700" if weights else f"family={f}")
    return "https://fonts.googleapis.com/css2?" + "&".join(parts) + "&display=swap"


def hex_to_rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def saturation(h):
    r, g, b = (c / 255 for c in hex_to_rgb(h))
    mx, mn = max(r, g, b), min(r, g, b)
    return 0.0 if mx == 0 else (mx - mn) / mx


def rgba(h, a):
    r, g, b = hex_to_rgb(h)
    return f"rgba({r},{g},{b},{a})"


def title_size(name):
    n = len(name)
    return 62 if n <= 12 else (50 if n <= 18 else 42)


MONO_FONTS = {"JetBrains Mono", "Fira Code", "Space Mono", "IBM Plex Mono"}
SERIF_FONTS = {"Fraunces", "Cormorant Garamond", "Marcellus", "Playfair Display",
               "EB Garamond", "Bodoni Moda", "Spectral"}


def font_stack(font):
    """CSS font-family value with an appropriate generic fallback."""
    if font in MONO_FONTS:
        fallback = "monospace"
    elif font in SERIF_FONTS:
        fallback = "serif"
    else:
        fallback = "sans-serif"
    return f"'{font}',{fallback}"


def page_html(theme, idx, total):
    name, desc, category, colors, best_for = theme[:5]
    mode = theme[5] if len(theme) > 5 else "light"
    header_font, body_font = CATEGORY_FONTS[category]

    ordered = sorted(colors, key=lambda c: luminance(c[1]), reverse=True)
    if mode == "dark":
        bg = ordered[-1][1]   # darkest = editor background
        text = ordered[0][1]  # lightest = foreground
        # accent = most saturated color bright enough to pop on a dark background
        candidates = [c for c in ordered if luminance(c[1]) > 0.3]
        accent = max(candidates or ordered, key=lambda c: saturation(c[1]))[1]
    else:
        bg = ordered[0][1]    # lightest = background
        text = ordered[-1][1]  # darkest = text
        candidates = [c for c in ordered if luminance(c[1]) < 0.6]
        accent = max(candidates or ordered, key=lambda c: saturation(c[1]))[1]

    swatches = "".join(
        f'''<div class="swatch">
              <div class="chip" style="background:{chex};
                   border:1px solid {rgba(text, 0.18)};"></div>
              <div class="sw-name">{cname}</div>
              <div class="sw-hex">{chex.upper()}</div>
            </div>''' for cname, chex in colors
    )

    return f'''
    <section class="page" style="background:{bg}; color:{text};">
      <div class="cat" style="color:{accent};">{category}</div>
      <h1 class="title" style="font-family:{font_stack(header_font)};
          font-size:{title_size(name)}px; color:{text};">{name}</h1>
      <p class="desc" style="color:{accent};">{desc}</p>

      <div class="swatches">{swatches}</div>

      <h2 class="typo" style="font-family:{font_stack(header_font)}; color:{text};">Typography</h2>

      <div class="font-line">
        <span class="lbl" style="color:{accent};">Headers</span>
        <span class="fname">{header_font}</span>
      </div>
      <div class="sample-h" style="font-family:{font_stack(header_font)}; color:{text};">
        Sample Header Text
      </div>

      <div class="font-line">
        <span class="lbl" style="color:{accent};">Body Text</span>
        <span class="fname" style="font-family:{font_stack(body_font)};">{body_font}</span>
      </div>
      <p class="sample-b" style="font-family:{font_stack(body_font)}; color:{rgba(text,0.85)};">
        This is sample body text showing how your content will appear in presentations.
        The typography pairs with the color palette for a cohesive, on-brand design.
      </p>

      <div class="footer">
        <span class="best" style="color:{accent};"><strong>Best for:</strong> {best_for}</span>
        <span class="pageno" style="color:{rgba(text,0.55)};">{idx} of {total}</span>
      </div>
    </section>'''


def build():
    total = len(THEMES)
    pages = "\n".join(page_html(t, i + 1, total) for i, t in enumerate(THEMES))
    html = f'''<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{gfonts_url()}" rel="stylesheet">
<style>
  @page {{ size: Letter; margin: 0; }}
  * {{ box-sizing: border-box; }}
  html, body {{ margin: 0; padding: 0; }}
  .page {{
    width: 8.5in; height: 11in; padding: 0.95in 0.85in;
    page-break-after: always; position: relative; overflow: hidden;
  }}
  .cat {{ font-family:'Work Sans',sans-serif; font-size:11px; font-weight:700;
          letter-spacing:0.22em; text-transform:uppercase; margin:0 0 10px; }}
  .title {{ margin:0 0 6px; font-weight:700; line-height:1.02; white-space:nowrap; }}
  .desc {{ font-family:'Work Sans',sans-serif; font-size:16px; margin:0 0 30px; }}
  .swatches {{ display:flex; gap:14px; margin-bottom:40px; }}
  .swatch {{ flex:1; }}
  .chip {{ height:96px; border-radius:3px; }}
  .sw-name {{ font-family:'Work Sans',sans-serif; font-size:12px; font-weight:600;
              margin-top:9px; }}
  .sw-hex {{ font-family:'Courier New',monospace; font-size:11px; opacity:0.75;
             margin-top:2px; letter-spacing:0.02em; }}
  .typo {{ font-size:28px; font-weight:700; margin:0 0 22px; }}
  .font-line {{ display:flex; align-items:baseline; gap:16px; margin-bottom:6px; }}
  .lbl {{ font-family:'Work Sans',sans-serif; font-size:13px; font-weight:700;
          letter-spacing:0.04em; min-width:90px; }}
  .fname {{ font-size:18px; }}
  .sample-h {{ font-size:46px; font-weight:700; line-height:1.05; margin:4px 0 26px; }}
  .sample-b {{ font-size:15px; line-height:1.65; max-width:6.0in; margin:6px 0 0; }}
  .footer {{ position:absolute; left:0.85in; right:0.85in; bottom:0.7in;
             display:flex; justify-content:space-between; align-items:flex-end; }}
  .best {{ font-family:'Work Sans',sans-serif; font-size:12.5px; max-width:5.5in; }}
  .pageno {{ font-family:'Work Sans',sans-serif; font-size:12px; }}
</style></head>
<body>
{pages}
</body></html>'''
    with open(OUT_HTML, "w") as f:
        f.write(html)
    print(f"Wrote {OUT_HTML} ({total} pages)")


if __name__ == "__main__":
    build()
