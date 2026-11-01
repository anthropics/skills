"""Post-process layout.json: (1) contain-fit image/video boxes to the media's real aspect ratio,
(2) attach the '## p.N' sections of a speaker script as presenter notes.
usage: python fit_notes.py layout.json [script.md]
- layout.json is the output of measure.py; media paths are resolved relative to its folder (the deck folder).
- Stage directions in parentheses are kept verbatim in the notes (so they show in the presenter view too)."""
import json, re, sys, pathlib, subprocess
from PIL import Image

LAY = pathlib.Path(sys.argv[1]).resolve(); D = LAY.parent
SCRIPT = pathlib.Path(sys.argv[2]) if len(sys.argv) > 2 else None
data = json.loads(LAY.read_text(encoding="utf-8"))
slides = data["slides"] if isinstance(data, dict) else data

def natural(path):
    p = D / path
    if not p.exists(): return None
    if p.suffix.lower() in (".mp4", ".webm", ".mov"):
        try:
            r = subprocess.run(["ffprobe", "-v", "error", "-select_streams", "v:0", "-show_entries", "stream=width,height",
                                "-of", "csv=p=0", str(p)], capture_output=True, text=True, check=True)
            w, h = r.stdout.strip().split(",")[:2]; return int(w), int(h)
        except Exception:
            return None
    try:
        with Image.open(p) as im: return im.size
    except Exception:
        return None

def contain(it, wh):
    w0, h0 = wh; bw, bh = it["w"], it["h"]
    s = min(bw / w0, bh / h0); w, h = w0 * s, h0 * s
    it["x"] += (bw - w) / 2; it["y"] += (bh - h) / 2; it["w"], it["h"] = w, h

n_fit = 0
for s in slides:
    for it in s["items"]:
        if it["t"] in ("img", "video"):
            wh = natural(it["src"])
            if wh: contain(it, wh); n_fit += 1

n_notes = 0
if SCRIPT and SCRIPT.exists():
    txt = SCRIPT.read_text(encoding="utf-8")
    parts = re.split(r"^## p\.(\d+)[^\n]*\n", txt, flags=re.M)
    notes = {}
    for i in range(1, len(parts) - 1, 2):
        notes[int(parts[i])] = parts[i + 1].strip()
    for k, s in enumerate(slides, 1):
        if k in notes: s["notes"] = notes[k]; n_notes += 1

LAY.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
print(f"fit {n_fit} media boxes; notes on {n_notes} slides")
