"""Print the HTML deck to a PDF (one slide per page, 1440x1080) with headless Chromium.
usage: python mkpdf.py deck.html deck.pdf
Videos are replaced by their poster image; print_tmp.html is a temporary copy left in the working folder."""
import sys, re, pathlib
from playwright.sync_api import sync_playwright
src, out = sys.argv[1], sys.argv[2]
h = open(src, encoding='utf-8').read()
h = re.sub(r"<video src='([^']+)' poster='([^']+)'[^>]*></video>", r"<img src='\2' alt='' style='width:100%;height:auto;aspect-ratio:16/9;object-fit:cover;border-radius:6px'>", h)
h = h.replace("</head>", "<style>.stage{position:static!important;transform:none!important}.slide{display:block!important;page-break-after:always}html,body{background:#fff}</style></head>")
p = pathlib.Path('print_tmp.html'); p.write_text(h, encoding='utf-8')
with sync_playwright() as pw:
    b = pw.chromium.launch(); pg = b.new_page(viewport={'width':1440,'height':1080})
    pg.goto(p.resolve().as_uri(), wait_until='networkidle'); pg.wait_for_timeout(1000)
    pg.pdf(path=out, width='1440px', height='1080px', print_background=True, prefer_css_page_size=True, margin={'top':'0','bottom':'0','left':'0','right':'0'})
    b.close()
print('ok', out)
