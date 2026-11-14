#!/usr/bin/env python3
"""PPT Text.md -> single-file HTML deck (1440x1080, 4:3).
usage: python build.py src.md out.html
- frontmatter: deck, lang (ko|en), author, org, footer_left, footer_center, date, font (serif|sans), palette (mono|color)
- "(figure: …)" / "(그림: …)" markers are rendered by functions in svgs.py next to src.md (SVGS list, in order)
- "[[Kind | what | source | why]]" placeholders: Kind = Photo / Video / Repro / Paper Fig (Korean equivalents also accepted)"""
import sys, re, json, html, base64, subprocess, pathlib
import markdown
import os
SRC, OUT = sys.argv[1], sys.argv[2]
HERE = pathlib.Path(__file__).parent
SRCDIR = pathlib.Path(SRC).resolve().parent
text = open(SRC, encoding="utf-8").read()

# ---------- frontmatter ----------
fm = {}
m = re.match(r"^---\n(.*?)\n---\n", text, re.S)
if m:
    for line in m.group(1).splitlines():
        if ":" in line:
            k, v = line.split(":", 1); fm[k.strip()] = v.strip().strip('"')
    text = text[m.end():]
EN = (fm.get("lang") or os.environ.get("DECK_LANG", "ko")).lower() == "en"
SERIF = (fm.get("font") or ("serif" if EN else "sans")).lower() == "serif"
AUTHOR = fm.get("author", "Presenter"); ORG = fm.get("org", "")
FOOT_L = fm.get("footer_left", f"{AUTHOR} · {ORG}" if ORG else AUTHOR); FOOT_C = fm.get("footer_center", "")
DATE = fm.get("date", "")
MONO = (fm.get("palette") or os.environ.get("DECK_PALETTE", "mono")).lower() != "color"   # mono: text, titles and diagrams in grayscale; images keep their colors
os.environ["DECK_PALETTE"] = "mono" if MONO else "color"
sys.path.insert(0, str(SRCDIR))
try:
    from svgs import SVGS
except ImportError:
    SVGS = []

# split on lines that are exactly --- (outside code fences)
slides, cur, in_code = [], [], False
for line in text.splitlines():
    if line.startswith("```"): in_code = not in_code
    if line.strip() == "---" and not in_code:
        slides.append("\n".join(cur)); cur = []
    else:
        cur.append(line)
slides.append("\n".join(cur))
slides = [s.strip("\n") for s in slides if s.strip()]

# ---------- KaTeX ----------
tex_all = re.findall(r"^\$\$(.+?)\$\$\s*$", text, re.M)
tex_html = {}
if tex_all:
    r = subprocess.run(["node", str(HERE / "katex_render.js")], input=json.dumps(tex_all), capture_output=True, text=True, cwd=HERE, check=True)
    tex_html = dict(zip(tex_all, json.loads(r.stdout)))
kcss = (HERE / "node_modules/katex/dist/katex.min.css").read_text()
def _font(mm):
    p = HERE / "node_modules/katex/dist" / mm.group(1)
    return "url(data:font/woff2;base64," + base64.b64encode(p.read_bytes()).decode() + ") format(\"woff2\")"
kcss = re.sub(r"url\((fonts/[^)]+\.woff2)\) format\(\"woff2\"\)(,url\([^)]+\) format\(\"[a-z]+\"\))*", _font, kcss)

md = markdown.Markdown(extensions=["tables", "fenced_code", "sane_lists"])
def mdhtml(src):
    ls = src.split("\n"); fixed = []
    for k, l in enumerate(ls):
        if re.match(r"^\s*([-*]|\d+\.)\s", l) and fixed and fixed[-1].strip() and not re.match(r"^\s*([-*]|\d+\.)\s", fixed[-1]):
            fixed.append("")
        fixed.append(l)
    md.reset(); return md.convert("\n".join(fixed))

svg_i = 0
def esc(s): return html.escape(s, quote=True)

def placeholder(inner):
    """[[Kind | ...]] placeholder box. Kind prefixes: Repro / Video / Photo (Korean: 재현 / 영상 / 사진);
    anything else (e.g. "Paper Fig", 논문 그림) is a paper-figure placeholder (ph-fig)."""
    parts = [p.strip() for p in inner.split("|")]
    kind = parts[0]
    if kind.startswith(("재현", "Repro")):
        cls, label = "ph-repro", "⚙ " + kind
        what, src_line, why = (parts[1:] + ["", "", ""])[:3]; extra = []
    elif kind.startswith(("영상", "Video")):
        cls, label = "ph-video", "▶ " + kind
        what, src, span, why = (parts[1:] + ["", "", "", ""])[:4]
        src_line = src + (f" · {span}" if span else "")
        extra = [p for p in parts[5:] if p]
    elif kind.startswith(("사진", "Photo")):
        cls, label = "ph-photo", kind
        what, src_line, why = (parts[1:] + ["", "", ""])[:3]; extra = []
    else:  # "Paper Fig", "논문 그림", or any other kind
        cls, label = "ph-fig", kind
        what, src_line, why = (parts[1:] + ["", "", ""])[:3]; extra = []
    ex = "".join(f"<div class='ph-l'>{esc(e)}</div>" for e in extra)
    return (f"<div class='media ph {cls}'><div class='ph-box'><div class='ph-tag'>{esc(label)}</div>"
            f"<div class='ph-l'>① {esc(what)}</div><div class='ph-l'>② {esc(src_line)}</div>"
            f"<div class='ph-l'>③ {esc(why)}</div>{ex}</div></div>")

# caption line prefixes; "Source:" / "출처:" captions stay free-standing instead of attaching to the figure above
CAP_RE = re.compile(r"^(▶ |Fig\.|Table|출처:|Source:)")
SOURCE_PREFIX = ("출처", "Source:")
CITE_RE = re.compile(r"^[A-Z][A-Za-z\-]+ et al\., ")
# SVG diagram markers: "(figure: …)" or Korean "(그림: …)"
FIG_MARKERS = ("(figure:", "(그림:")

def render_body(src):
    """Render a column/body chunk: specials become media blocks, rest via markdown."""
    global svg_i
    out, buf = [], []
    lines = src.split("\n"); i = 0
    def flush():
        if any(l.strip() for l in buf):
            out.append(f"<div class='md'>{mdhtml(chr(10).join(buf))}</div>")
        buf.clear()
    while i < len(lines):
        l = lines[i]; st = l.strip()
        if st.startswith("```"):
            j = i + 1
            while j < len(lines) and not lines[j].strip().startswith("```"): j += 1
            flush(); code = "\n".join(lines[i+1:j])
            lang = st[3:].strip()
            out.append(f"<pre class='code'><code>{esc(code)}</code></pre>")
            i = j + 1; continue
        mi = re.match(r"^!\[\]\((.+?)\)\s*$", st)
        if mi:
            flush(); src_ = mi.group(1)
            if src_.lower().endswith((".mp4", ".webm", ".mov")):
                poster = src_.rsplit('.',1)[0] + '_poster.jpg'
                out.append(f"<div class='media img'><video src='{esc(src_)}' poster='{esc(poster)}' controls muted playsinline preload='metadata'></video></div>")
            else:
                out.append(f"<div class='media img'><img src='{esc(src_)}' alt=''></div>")
            i += 1; continue
        if st.startswith("[[") and st.endswith("]]"):
            flush(); out.append(placeholder(st[2:-2])); i += 1; continue
        if st.startswith(FIG_MARKERS):
            flush(); out.append(f"<div class='media svg'>{SVGS[svg_i]()}</div>"); svg_i += 1; i += 1; continue
        mm = re.match(r"^\$\$(.+?)\$\$\s*$", st)
        if mm:
            flush(); out.append(f"<div class='math'>{tex_html[mm.group(1)]}</div>"); i += 1; continue
        if CITE_RE.match(st):
            flush(); out.append(f"<div class='cite'>{esc(st)}</div>"); i += 1; continue
        if CAP_RE.match(st) and (not buf or not any(x.strip() for x in buf[-1:])):
            flush(); cap = f"<div class='cap{' vcap' if st.startswith('▶ ') else ''}'>{mdhtml(st[2:] if st.startswith('▶ ') else st)[3:-4]}</div>"
            if out and out[-1].startswith("<div class='media img'>") and not st.startswith(SOURCE_PREFIX):
                out[-1] = out[-1].replace("<div class='media img'>", "<div class='media img fig'>", 1)[:-6] + cap + "</div>"
            elif out and out[-1].startswith("<div class='md'>") and "<table>" in out[-1] and not st.startswith(SOURCE_PREFIX):
                out[-1] = out[-1][:-6] + cap + "</div>"
            else:
                out.append(cap)
            i += 1; continue
        buf.append(l); i += 1
    flush()
    return "\n".join(out)

def bold_maroon(h):  # **x** already -> <strong>; styled by css
    return h

sections = []
n_total = len(slides)
for idx, s in enumerate(slides, 1):
    lines = s.split("\n")
    # "> …" lines are speaker notes (hidden); ">> …" lines are the emphasis line at the bottom of the slide
    notes = [l[1:].strip() for l in lines if l.startswith(">") and not l.startswith(">>")]
    emph = [l[2:].strip() for l in lines if l.startswith(">>")]
    lines = [l for l in lines if not l.startswith(">")]
    first = next((l for l in lines if l.strip()), "")
    notes_html = f"<aside class='notes'>{esc(' / '.join(notes))}</aside>" if notes else ""
    foot = (f"<footer><span>{esc(FOOT_L)}</span><span>{esc(FOOT_C)}</span><span>{idx}</span></footer>")
    mpart = re.match(r"^# Part\s*(\d+)\s*:\s*(.+)$", first)
    if mpart:
        sections.append(f"<section class='slide part' data-slide='{idx}'><div class='frame'>"
                        f"<div class='part-n'>Part {mpart.group(1)}</div><div class='part-t'>{esc(mpart.group(2))}</div>"
                        f"</div>{foot}{notes_html}</section>"); continue
    if first.startswith("# ") and idx == 1:
        sub = next((l[4:] for l in lines if l.startswith("### ")), "")
        sections.append(f"<section class='slide cover' data-slide='{idx}'><div class='frame'>"
                        f"<div class='cv-t'>{esc(first[2:])}</div><div class='cv-s'>{esc(sub)}</div>"
                        f"<div class='cv-bar'></div><div class='cv-a'>{esc(AUTHOR)}</div>"
                        f"<div class='cv-o'>{esc(ORG)} · {esc(FOOT_C)}</div><div class='cv-d'>{esc(DATE)}</div>"
                        f"</div>{notes_html}</section>"); continue
    title = sub = ""; body = []
    for l in lines:
        if l.startswith("## ") and not title: title = l[3:]
        elif l.startswith("### ") and not sub: sub = l[4:]
        else: body.append(l)
    body = "\n".join(body).strip("\n")
    tag = ""
    mt = re.match(r"^\[(.+?)\]\s*(.*)$", title)
    if mt: tag, title = mt.group(1), mt.group(2)
    tag_html = f"<span class='tag'>{esc(tag)}</span>" if tag else ""
    if "\n|||\n" in "\n" + body + "\n":
        parts = re.split(r"^\|\|\|\s*$", body, flags=re.M)
        pre, left, right = (parts + ["", "", ""])[:3]
        content = (render_body(pre) if pre.strip() else "") + \
            f"<div class='cols'><div class='col'>{render_body(left)}</div><div class='col'>{render_body(right)}</div></div>"
    else:
        content = render_body(body)
    has_media = any(k in content for k in ("class='media", "<table>", "<pre"))
    body_cls = "body" if has_media else "body textonly"
    em = "".join(f"<div class='emph'><div class='emph-bar'></div><div>{mdhtml(e)[3:-4]}</div></div>" for e in emph)
    sections.append(f"<section class='slide' data-slide='{idx}'><div class='frame'>"
                    f"<header><h2>{tag_html}{esc(title)}</h2>{f'<div class=sub>{esc(sub)}</div>' if sub else ''}</header>"
                    f"<div class='{body_cls}'>{content}</div>{em}</div>{foot}{notes_html}</section>")

CSS = r"""
:root{--blue:#004094;--maroon:#8C2D2D;--ink:#111;--gray:#6b7280;--line:#d5dce8;--pale:#f3f6fb}
*{box-sizing:border-box}
html,body{margin:0;background:#2b2b2b}
body{font-family:"Source Sans 3","Pretendard","Noto Sans KR","Noto Sans CJK KR","Malgun Gothic","Apple SD Gothic Neo",sans-serif;color:var(--ink)}
.stage{position:fixed;left:0;top:0;width:1440px;height:1080px;transform-origin:0 0}
.slide{display:none;width:1440px;height:1080px;background:#fff;position:relative;overflow:hidden}
.slide.active{display:block}
.frame{position:absolute;left:64px;right:64px;top:52px;bottom:76px;display:flex;flex-direction:column;gap:18px}
header h2{margin:0;font-size:44px;font-weight:600;color:var(--blue);line-height:1.2}
header .sub{margin-top:8px;font-size:26px;color:#8a8f98}
.tag{display:inline-block;font-size:26px;font-weight:600;color:#fff;background:var(--blue);border-radius:6px;padding:2px 12px;margin-right:14px;vertical-align:5px}
.body{flex:1;min-height:0;display:flex;flex-direction:column;gap:14px}
.cols{flex:1;min-height:0;display:flex;gap:40px}
.col{flex:1;min-width:0;display:flex;flex-direction:column;gap:14px;justify-content:center}
.cols .md{font-size:27px}
.cols .md table{font-size:23px}
.cols .md th{white-space:nowrap}
.md{font-size:29px;line-height:1.45}
.textonly{justify-content:center}
.textonly .md{font-size:34px;line-height:1.5}
.textonly .md li{margin:14px 0}
.textonly .math{font-size:42px}
.md p{margin:0 0 6px}
.md ul,.md ol{margin:0;padding-left:1.2em}
.md li{margin:4px 0}
.md li::marker{color:var(--ink)}
strong{color:var(--maroon);font-weight:700}
.md table{border-collapse:collapse;width:100%;font-size:26px;line-height:1.35}
.md th{background:var(--pale);color:var(--blue);font-weight:600;text-align:left}
.md th,.md td{border:1px solid var(--line);padding:11px 14px;vertical-align:top}
.media{flex:1;min-height:0;display:flex;align-items:center;justify-content:center}
.media.img img{max-width:100%;max-height:100%;object-fit:contain;display:block;min-height:0}
.media.fig{flex-direction:column;gap:6px}
.media.fig img{flex:1;min-height:0;width:100%;object-fit:contain}
.media.fig video{flex:none;width:100%;height:auto;max-height:calc(100% - 44px);aspect-ratio:16/9;object-fit:contain}
.media video{max-width:100%;max-height:100%;background:transparent;border-radius:6px}
.media.fig .cap{margin-top:0;flex:none}
.md .cap{margin-top:8px}
.body>.md:only-child table{font-size:29px}
.body>.md:only-child th,.body>.md:only-child td{padding:16px 16px}
.cols pre.code{font-size:18px;white-space:pre;overflow:hidden}
.cite{font-size:20px;color:var(--gray);text-align:right}
.media.svg svg{width:100%;height:100%;max-height:100%}
.cap{font-size:18px;color:var(--gray);text-align:center;margin-top:-6px}
.media.fig .cap.vcap{font-size:24px;color:var(--ink);font-weight:600}
.cap strong{color:var(--gray)}
.math{font-size:34px;text-align:center}
.math .katex-display{margin:4px 0}
pre.code{margin:0;background:#f4f5f7;border-radius:8px;padding:16px 20px;font-family:"JetBrains Mono","Consolas","D2Coding","DejaVu Sans Mono","Noto Sans Mono CJK KR",monospace;font-size:20px;line-height:1.45;white-space:pre-wrap;color:#222}
.ph-box{width:100%;max-height:100%;aspect-ratio:16/9;border:2px dashed #888;border-radius:10px;display:flex;flex-direction:column;justify-content:center;gap:10px;padding:24px 30px;background:#fafafa;font-size:21px;line-height:1.35;color:#333}
.ph-photo .ph-box{aspect-ratio:4/3;border-color:#888}
.ph-video .ph-box{border-color:var(--maroon)}
.ph-fig .ph-box{border-color:var(--blue)}
.ph-repro .ph-box{border-color:#2E7D32}
.ph-tag{font-weight:700;font-size:23px}
.ph-video .ph-tag{color:var(--maroon)} .ph-fig .ph-tag{color:var(--blue)} .ph-photo .ph-tag{color:#555} .ph-repro .ph-tag{color:#2E7D32}
.ph-l{word-break:break-all}
.emph{display:flex;flex-direction:column;align-items:center;gap:10px;font-size:29px;font-weight:600;text-align:center;padding-top:4px}
.emph-bar{width:72px;height:5px;background:var(--maroon);border-radius:3px}
footer{position:absolute;left:64px;right:64px;bottom:22px;height:34px;display:flex;justify-content:space-between;align-items:center;border-top:1px solid var(--line);padding-top:8px;font-size:18px;color:#777}
footer span{flex:1} footer span:nth-child(2){text-align:center} footer span:nth-child(3){text-align:right}
.part .frame{justify-content:center;align-items:flex-start;padding-left:40px}
.part-n{font-size:30px;font-weight:600;color:var(--maroon);letter-spacing:.04em}
.part-t{font-size:64px;font-weight:600;color:var(--blue)}
.cover .frame{justify-content:center;padding:0 40px}
.cv-t{font-size:66px;font-weight:600;color:var(--blue);line-height:1.2}
.cv-s{font-size:30px;color:#555;margin-top:8px}
.cv-bar{width:96px;height:6px;background:var(--maroon);margin:36px 0 26px}
.cv-a{font-size:30px;font-weight:600}
.cv-o{font-size:24px;color:#555}
.cv-d{font-size:22px;color:#888;margin-top:6px}
.notes{display:none}
.katex .mathnormal,.katex .mathit{font-family:KaTeX_Math}
@media print{
  @page{size:1440px 1080px;margin:0}
  html,body{background:#fff}
  .stage{position:static;transform:none!important}
  .slide{display:block!important;page-break-after:always}
}
"""
JS = r"""
(function(){
 const S=[...document.querySelectorAll('.slide')]; let i=0;
 const h=parseInt(location.hash.slice(1)); if(h>0&&h<=S.length) i=h-1;
 function show(){S.forEach((s,k)=>s.classList.toggle('active',k===i)); history.replaceState(null,'','#'+(i+1));}
 function fit(){const st=document.querySelector('.stage');const k=Math.min(innerWidth/1440,innerHeight/1080);
   st.style.transform=`translate(${(innerWidth-1440*k)/2}px,${(innerHeight-1080*k)/2}px) scale(${k})`;}
 addEventListener('keydown',e=>{if(['ArrowRight','PageDown',' ','Enter'].includes(e.key)){i=Math.min(i+1,S.length-1);show();}
   if(['ArrowLeft','PageUp','Backspace'].includes(e.key)){i=Math.max(i-1,0);show();}
   if(e.key==='Home'){i=0;show();} if(e.key==='End'){i=S.length-1;show();}});
 addEventListener('click',e=>{if(e.target.closest('video'))return;if(e.clientX>innerWidth/2){i=Math.min(i+1,S.length-1);}else{i=Math.max(i-1,0);} show();});
 addEventListener('resize',fit); fit(); show();
})();
"""
deck_title = fm.get("deck", "Deck")
if MONO:
    CSS += r"""
:root{--blue:#111;--maroon:#111;--pale:#f1f1f1;--line:#d4d4d4}
header h2,.cv-t,.part-t{color:#111}
.tag{background:#111;color:#fff}
strong{color:#111;font-weight:700}
.emph-bar,.cv-bar{background:#333}
.md th{color:#111;background:#f1f1f1}
.ph-video .ph-box,.ph-fig .ph-box,.ph-repro .ph-box,.ph-photo .ph-box{border-color:#555}
.ph-video .ph-tag,.ph-fig .ph-tag,.ph-repro .ph-tag,.ph-photo .ph-tag{color:#333}
.part-n{color:#555}
"""
FONTCSS = ""
if SERIF:
    import base64 as _b
    for w, st in [(400,'normal'),(600,'normal'),(700,'normal'),(400,'italic'),(700,'italic')]:
        for sub in ('latin','latin-ext','greek'):
            p = HERE / f"node_modules/@fontsource/noto-serif/files/noto-serif-{sub}-{w}-{st}.woff2"
            if not p.exists(): p = SRCDIR / f"node_modules/@fontsource/noto-serif/files/noto-serif-{sub}-{w}-{st}.woff2"
            if p.exists():
                FONTCSS += ("@font-face{font-family:'Noto Serif';font-style:%s;font-weight:%d;font-display:swap;"
                            "src:url(data:font/woff2;base64,%s) format('woff2')}" % (st, w, _b.b64encode(p.read_bytes()).decode()))
    CSS = CSS.replace('body{font-family:"Source Sans 3",', 'body{font-family:"Noto Serif","Source Sans 3",')
doc = f"""<!doctype html><html lang="{'en' if EN else 'ko'}"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(deck_title)}</title>
<link rel="preconnect" href="https://fonts.googleapis.com"><link href="https://fonts.googleapis.com/css2?family=Source+Sans+3:wght@400;600;700&display=swap" rel="stylesheet">
<style>{FONTCSS}</style><style>{kcss}</style><style>{CSS}</style></head><body>
<div class="stage">
{chr(10).join(sections)}
</div>
<script>{JS}</script></body></html>"""
open(OUT, "w", encoding="utf-8").write(doc)
print(f"{len(sections)} slides -> {OUT}; svgs used {svg_i}/{len(SVGS)}")
