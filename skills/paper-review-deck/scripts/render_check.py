#!/usr/bin/env python3
"""Render an HTML slide deck page by page, saving screenshots and an automatic layout check.

Usage:
  python render_check.py deck.html --out check/
  python render_check.py deck.html --out check/ --pages 6,7,8
  python render_check.py deck.html --out check/ --selector "section.slide"
  python render_check.py deck.html --out check/ --static --sheet 6

Output:
  check/p01.png ...      one screenshot per slide
  check/report.json      issues per slide
  stdout                 human-readable summary

Automatic checks (they do not replace a visual pass -- always look at the screenshots too):
  overflow      text overflows its box (scroll size > visible size)
  out_of_slide  element sticks out of the slide
  overlap       text boxes overlap each other
  broken_image  image failed to load
  math_error    KaTeX rendering error
  tiny_text     font size below 14px (at 1440px slide width)
  empty_slide   almost no visible text or media
"""
import argparse
import json, pathlib
import sys
from pathlib import Path

from playwright.sync_api import sync_playwright

DEFAULT_SELECTORS = [
    "[data-slide]",
    "deck-stage > section",
    "section.slide",
    ".slide",
    "section",
]

CHECK_JS = r"""
(slide) => {
  const issues = [];
  const sr = slide.getBoundingClientRect();
  const label = (el) => {
    const t = (el.innerText || el.alt || el.tagName).trim().replace(/\s+/g, ' ');
    return t.slice(0, 40);
  };
  const visible = (el) => {
    const cs = getComputedStyle(el);
    if (cs.display === 'none' || cs.visibility === 'hidden' || +cs.opacity === 0) return false;
    const r = el.getBoundingClientRect();
    return r.width > 0 && r.height > 0;
  };
  const all = [...slide.querySelectorAll('*')].filter(visible);

  // text overflow
  for (const el of all) {
    const cs = getComputedStyle(el);
    if (!el.innerText || !el.innerText.trim()) continue;
    const clipped = ['hidden', 'clip', 'auto', 'scroll'].includes(cs.overflow)
      || ['hidden', 'clip', 'auto', 'scroll'].includes(cs.overflowY);
    if (clipped && (el.scrollHeight > el.clientHeight + 2 || el.scrollWidth > el.clientWidth + 2)) {
      issues.push({type: 'overflow', el: label(el)});
    }
  }
  // element outside the slide
  for (const el of all) {
    const r = el.getBoundingClientRect();
    if (r.right > sr.right + 2 || r.bottom > sr.bottom + 2 || r.left < sr.left - 2 || r.top < sr.top - 2) {
      if (el.children.length === 0 || el.tagName === 'IMG' || el.tagName === 'svg') {
        issues.push({type: 'out_of_slide', el: label(el),
          by: Math.round(Math.max(r.right - sr.right, r.bottom - sr.bottom, sr.left - r.left, sr.top - r.top)) + 'px'});
      }
    }
  }
  // overlapping text boxes (leaf text elements only)
  const leaves = all.filter(el => el.innerText && el.innerText.trim()
    && ![...el.children].some(c => visible(c) && c.innerText && c.innerText.trim())
    && !el.closest('.katex'));
  for (let i = 0; i < leaves.length; i++) {
    for (let j = i + 1; j < leaves.length; j++) {
      const a = leaves[i], b = leaves[j];
      if (a.contains(b) || b.contains(a)) continue;
      const ra = a.getBoundingClientRect(), rb = b.getBoundingClientRect();
      const w = Math.min(ra.right, rb.right) - Math.max(ra.left, rb.left);
      const h = Math.min(ra.bottom, rb.bottom) - Math.max(ra.top, rb.top);
      if (w > 4 && h > 4) issues.push({type: 'overlap', el: label(a) + ' ↔ ' + label(b)});
    }
  }
  // images
  for (const img of slide.querySelectorAll('img')) {
    if (!img.complete || img.naturalWidth === 0) issues.push({type: 'broken_image', el: img.getAttribute('src')});
  }
  // math
  for (const e of slide.querySelectorAll('.katex-error')) issues.push({type: 'math_error', el: label(e)});
  // tiny text
  const scale = 1440 / sr.width;
  for (const el of leaves) {
    const px = parseFloat(getComputedStyle(el).fontSize) * scale;
    if (px < 14 && !el.closest('footer, .footer, figcaption, .caption')) {
      issues.push({type: 'tiny_text', el: label(el), size: Math.round(px) + 'px'});
    }
  }
  // empty slide
  const textLen = (slide.innerText || '').trim().length;
  const media = slide.querySelectorAll('img, svg, video, canvas').length;
  if (textLen < 15 && media === 0) issues.push({type: 'empty_slide', el: ''});

  // drop duplicate reports for the same element
  const seen = new Set();
  return issues.filter(x => { const k = x.type + x.el; if (seen.has(k)) return false; seen.add(k); return true; });
}
"""


def find_slides(page, selector):
    candidates = [selector] if selector else DEFAULT_SELECTORS
    for sel in candidates:
        n = page.locator(sel).count()
        if n >= 2 or (selector and n >= 1):
            return sel, n
    return None, 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("deck")
    ap.add_argument("--out", default="check")
    ap.add_argument("--pages", help="pages to check, e.g. 3,4,5 (default: all)")

    ap.add_argument("--static", action="store_true", help="unfold a one-slide-at-a-time deck into a static page (all slides block, stage static) before checking")

    ap.add_argument("--sheet", type=int, default=0, help="also write contact sheets (sheet_K.png) with N slides each, e.g. 6")
    ap.add_argument("--selector", help="CSS selector for slides (when auto-detection fails)")
    ap.add_argument("--width", type=int, default=1440)
    ap.add_argument("--height", type=int, default=1080)
    args = ap.parse_args()

    deck = Path(args.deck).resolve()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    wanted = {int(p) for p in args.pages.split(",")} if args.pages else None

    with sync_playwright() as pw:
        browser = pw.chromium.launch()
        page = browser.new_page(viewport={"width": args.width, "height": args.height})
        if args.static:
            src = deck.read_text(encoding="utf-8").replace("</head>", "<style>.stage{position:static!important;transform:none!important}.slide{display:block!important}</style></head>")
            deck = deck.with_name("_static_" + deck.name); deck.write_text(src, encoding="utf-8")  # written next to the deck so relative image paths still resolve
        page.goto(deck.as_uri(), wait_until="networkidle")
        page.wait_for_timeout(800)  # wait for fonts and math to render

        sel, n = find_slides(page, args.selector)
        if not sel:
            print("No slides found. Pass a slide selector with --selector.", file=sys.stderr)
            sys.exit(2)

        # make every slide visible so decks that show one slide at a time can be checked too
        page.add_style_tag(content=f"{sel}{{display:block!important;visibility:visible!important;"
                                   f"opacity:1!important;position:relative!important;transform:none!important;}}")
        page.wait_for_timeout(300)

        report = []
        for i in range(n):
            pno = i + 1
            if wanted and pno not in wanted:
                continue
            slide = page.locator(sel).nth(i)
            slide.scroll_into_view_if_needed()
            shot = out / f"p{pno:02d}.png"
            slide.screenshot(path=str(shot))
            issues = slide.evaluate(CHECK_JS)
            report.append({"page": pno, "screenshot": str(shot), "issues": issues})
        browser.close()

    (out / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    if args.sheet:
        from PIL import Image
        shots = [pathlib.Path(r["screenshot"]) for r in report]
        cw, ch, cols = 720, 540, 3
        for k in range(0, len(shots), args.sheet):
            chunk = shots[k:k + args.sheet]; rows = (len(chunk) + cols - 1) // cols
            sheet = Image.new("RGB", (cols * cw, rows * ch), "white")
            for i, f in enumerate(chunk):
                sheet.paste(Image.open(f).convert("RGB").resize((cw, ch)), ((i % cols) * cw, (i // cols) * ch))
            sheet.save(out / f"sheet_{k // args.sheet}.png")
        print(f"contact sheets: {out}/sheet_*.png ({args.sheet} slides each)")

    bad = [r for r in report if r["issues"]]
    print(f"selector: {sel} / checked {len(report)} slides / slides with issues: {len(bad)}")
    for r in bad:
        print(f"p.{r['page']}:")
        for it in r["issues"]:
            extra = " ".join(f"{k}={v}" for k, v in it.items() if k not in ("type", "el"))
            print(f"  - {it['type']}: {it['el']} {extra}".rstrip())
    print(f"screenshots and report.json: {out}/")


if __name__ == "__main__":
    main()
