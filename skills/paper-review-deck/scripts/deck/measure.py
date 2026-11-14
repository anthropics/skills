"""Render deck.html and export every slide's elements with positions (px) to layout.json.
SVG diagrams and math are screenshotted to PNG (they become pictures in the PPTX)."""
import json, pathlib, re
import html as html_mod
from playwright.sync_api import sync_playwright

JS = r"""
(slide) => {
  const S = slide.getBoundingClientRect();
  const box = el => { const r = el.getBoundingClientRect(); return {x:r.left-S.left, y:r.top-S.top, w:r.width, h:r.height}; };
  const rgb = c => { const m = c.match(/\d+/g); return m ? m.slice(0,3).map(v=>(+v).toString(16).padStart(2,'0')).join('').toUpperCase() : '111111'; };
  function runs(el) {
    const out = [];
    function walk(n, st) {
      if (n.nodeType === 3) { if (n.textContent) out.push({text:n.textContent, ...st}); return; }
      if (n.nodeType !== 1) return;
      const cs = getComputedStyle(n);
      if (cs.display === 'none') return;
      if (n.tagName === 'BR') { out.push({text:'\n', ...st}); return; }
      const s2 = {...st};
      if (['STRONG','B'].includes(n.tagName) || +cs.fontWeight >= 600) s2.bold = true;
      if (['EM','I'].includes(n.tagName) || cs.fontStyle === 'italic') s2.italic = true;
      s2.color = rgb(cs.color);
      if (n.tagName === 'CODE') s2.mono = true;
      for (const c of n.childNodes) walk(c, s2);
    }
    const cs = getComputedStyle(el);
    walk(el, {bold: +cs.fontWeight >= 600, italic: cs.fontStyle==='italic', color: rgb(cs.color)});
    // merge & trim
    const m = [];
    for (const r of out) { const p = m[m.length-1];
      if (p && p.bold===r.bold && p.italic===r.italic && p.color===r.color && p.mono===r.mono) p.text += r.text; else m.push({...r}); }
    m.forEach(r => r.text = r.text.replace(/\s*\n\s*/g,' ').replace(/\s+/g,' '));
    if (m.length) { m[0].text = m[0].text.replace(/^\s+/,''); m[m.length-1].text = m[m.length-1].text.replace(/\s+$/,''); }
    return m.filter(r => r.text.length);
  }
  const fs = el => parseFloat(getComputedStyle(el).fontSize);
  const al = el => getComputedStyle(el).textAlign;
  const items = [];
  const kind = slide.classList.contains('cover') ? 'cover' : slide.classList.contains('part') ? 'part' : 'content';
  const add = (o) => items.push(o);
  if (kind !== 'content') {
    slide.querySelectorAll('.frame > div').forEach(d => {
      if (d.classList.contains('cv-bar')) add({t:'bar', ...box(d), color: rgb(getComputedStyle(d).backgroundColor)});
      else add({t:'text', role:d.className, ...box(d), size:fs(d), align:al(d), runs:runs(d)});
    });
  } else {
    const h2 = slide.querySelector('header h2');
    const tag = h2.querySelector('.tag');
    add({t:'title', ...box(h2), size:fs(h2), tag: tag ? tag.textContent : '', tagBox: tag ? box(tag) : null,
         runs: runs(h2).filter(r => !tag || r.text !== tag.textContent)});
    const sub = slide.querySelector('header .sub');
    if (sub) add({t:'text', role:'sub', ...box(sub), size:fs(sub), align:'left', runs:runs(sub)});
    slide.querySelectorAll('.body .md > *, .body .cap, .body .cite, .body pre.code, .body .media, .emph').forEach(el => {
      if (el.closest('.ph-box') ) return;
      if (el.matches('.md > p')) add({t:'text', role:'p', ...box(el), size:fs(el), align:al(el), runs:runs(el)});
      else if (el.matches('.md > ul, .md > ol')) {
        add({t:'list', ordered: el.tagName==='OL', ...box(el), size:fs(el),
             items:[...el.children].map(li => runs(li))});
      } else if (el.matches('.md > table')) {
        const rows = [...el.rows].map(r => [...r.cells].map(c => ({runs:runs(c), head:c.tagName==='TH'})));
        const cw = [...el.rows[0].cells].map(c => c.getBoundingClientRect().width);
        const rh = [...el.rows].map(r => r.getBoundingClientRect().height);
        add({t:'table', ...box(el), size:fs(el.rows[1] ? el.rows[1].cells[0] : el), rows, cw, rh});
      } else if (el.matches('.cap, .cite')) add({t:'text', role:'cap', ...box(el), size:fs(el), align:al(el), runs:runs(el)});
      else if (el.matches('pre.code')) add({t:'code', ...box(el), size:fs(el), text: el.innerText});
      else if (el.matches('.media')) {
        const img = el.querySelector('img'), vid = el.querySelector('video'), svg = el.querySelector('svg'), ph = el.querySelector('.ph-box');
        if (img) add({t:'img', src: img.getAttribute('src'), ...box(img)});
        else if (vid) add({t:'video', src: vid.getAttribute('src'), poster: vid.getAttribute('poster'), ...box(vid)});
        else if (svg) add({t:'snap', sel:'svg', ...box(svg)});
        else if (ph) add({t:'ph', cls: el.className, ...box(ph), color: rgb(getComputedStyle(ph).borderTopColor),
                          lines: [...ph.children].map(c => c.textContent), size: fs(ph)});
      } else if (el.matches('.emph')) {
        const bar = el.querySelector('.emph-bar'); const tx = el.children[1];
        add({t:'bar', ...box(bar), color: rgb(getComputedStyle(bar).backgroundColor)});
        add({t:'text', role:'emph', ...box(tx), size:fs(tx), align:'center', runs:runs(tx)});
      }
    });
    slide.querySelectorAll('.body .math').forEach(el => add({t:'snapmath', ...box(el.querySelector('.katex-display') || el)}));
  }
  return {kind, items};
}
"""

import os, sys
DECK = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("DECK","deck.html")
D = pathlib.Path(DECK).resolve().parent
DECK = pathlib.Path(DECK).name
LAYOUT = sys.argv[2] if len(sys.argv) > 2 else os.environ.get("LAYOUT","layout.json"); SNAPD = os.environ.get("SNAPS","snaps")
html = (D / DECK).read_text(encoding="utf-8").replace("</head>", "<style>.stage{position:static!important;transform:none!important}.slide{display:block!important}</style></head>")
(D / "measure.html").write_text(html, encoding="utf-8")
snaps = D / SNAPD; snaps.mkdir(exist_ok=True)
out = []
with sync_playwright() as p:
    b = p.chromium.launch(); pg = b.new_page(viewport={"width": 1440, "height": 1080}, device_scale_factor=2)
    pg.goto((D / "measure.html").resolve().as_uri(), wait_until="networkidle"); pg.wait_for_timeout(800)
    slides = pg.locator(".slide")
    for i in range(slides.count()):
        sl = slides.nth(i)
        data = sl.evaluate(JS)
        k = 0
        for it in data["items"]:
            if it["t"] in ("snap", "snapmath"):
                loc = sl.locator(".body svg" if it["t"] == "snap" else ".body .math").nth(k if it["t"]=="snapmath" else 0)
                if it["t"] == "snapmath": k += 1
                f = snaps / f"s{i+1:02d}_{it['t']}_{k}.png"
                target = loc.locator(".katex-display").first if it["t"] == "snapmath" else loc
                target.screenshot(path=str(f), omit_background=True)
                it["file"] = str(f.relative_to(D))
        out.append(data)
    b.close()
meta = {}
m = re.search(r"<footer><span>(.*?)</span><span>(.*?)</span>", html)
if m: meta = {"footer_left": html_mod.unescape(m.group(1)), "footer_center": html_mod.unescape(m.group(2))}
t = re.search(r"<title>(.*?)</title>", html)
if t: meta["title"] = html_mod.unescape(t.group(1))
(D / LAYOUT).write_text(json.dumps({"meta": meta, "slides": out}, ensure_ascii=False, indent=1), encoding="utf-8")
print(len(out), "slides;", sum(len(s["items"]) for s in out), "items")
