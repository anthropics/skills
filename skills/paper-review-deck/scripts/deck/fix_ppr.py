"""Remove stray mid-paragraph <a:pPr> that pptxgenjs inserts between runs (keeps the first pPr of each paragraph)."""
import sys, re, zipfile, shutil
src = sys.argv[1]; tmp = src + ".tmp"
zin = zipfile.ZipFile(src); zout = zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED)
PPR = re.compile(r'<a:pPr\b[^>]*?(?:/>|>.*?</a:pPr>)', re.S)
def fix_p(m):
    p = m.group(0); seen = [False]
    def keep(mm):
        if not seen[0]:
            seen[0] = True
            # only keep if it is at the start of the paragraph
            return mm.group(0) if p.index(mm.group(0)) == len('<a:p>') else ''
        return ''
    return PPR.sub(keep, p)
n = 0
for it in zin.infolist():
    data = zin.read(it.filename)
    if re.match(r'ppt/slides/slide\d+\.xml$', it.filename):
        x = data.decode('utf-8')
        x2 = re.sub(r'<a:p>.*?</a:p>', fix_p, x, flags=re.S)
        n += x.count('<a:pPr') - x2.count('<a:pPr'); data = x2.encode('utf-8')
    zout.writestr(it, data)
zout.close(); shutil.move(tmp, src); print('removed', n, 'stray pPr')
