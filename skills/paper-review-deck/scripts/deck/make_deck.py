"""Build HTML, PDF and PPTX from a single manuscript (PPT Text.md) in one go.
usage: python make_deck.py "PPT Text.md" --name "Week5 Review" [--script "script.md"] [--font "Noto Serif"] [--pptx-skill <pptx skill folder>] [--no-pdf] [--no-pptx]
Requirements: run `npm install` once in this folder (katex, pptxgenjs, @fontsource/noto-serif); pip: markdown playwright pillow pymupdf.
Output: {name}.html / {name}.pdf / {name}.pptx next to the manuscript (layout.json and snaps/ are intermediate files).
The PPTX step can use apply_theme.js and validate.py from the Anthropic pptx skill; pass its folder with --pptx-skill
(or the PPTX_SKILL env var). Without it the PPTX is still generated, only theme application and validation are skipped."""
import argparse, os, subprocess, sys, pathlib, shutil

HERE = pathlib.Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument("src"); ap.add_argument("--name", required=True)
ap.add_argument("--script"); ap.add_argument("--font"); ap.add_argument("--pptx-skill")
ap.add_argument("--no-pptx", action="store_true"); ap.add_argument("--no-pdf", action="store_true")
a = ap.parse_args()
src = pathlib.Path(a.src).resolve(); D = src.parent
html = D / f"{a.name}.html"; pdf = D / f"{a.name}.pdf"; pptx = D / f"{a.name}.pptx"
layout = D / "layout.json"

def run(cmd, **kw):
    print("+", " ".join(str(c) for c in cmd)); subprocess.run([str(c) for c in cmd], check=True, **kw)

# node_modules lives in the tool folder; the deck folder gets a symlink to it (so build.py can find the KaTeX fonts)
if not (HERE / "node_modules").exists():
    run(["npm", "install", "--silent"], cwd=HERE)
if not (D / "node_modules").exists():
    os.symlink(HERE / "node_modules", D / "node_modules")

run([sys.executable, HERE / "build.py", src, html], cwd=D)
if not a.no_pdf:
    run([sys.executable, HERE / "mkpdf.py", html, pdf], cwd=D)
if not a.no_pptx:
    skill = a.pptx_skill or os.environ.get("PPTX_SKILL") or ""
    if not skill:
        print("(no pptx skill given: generating PPTX without theme application and validation)")
    run([sys.executable, HERE / "measure.py", html, layout], cwd=D)
    run([sys.executable, HERE / "fit_notes.py", layout] + ([a.script] if a.script else []), cwd=D)
    import re as _re
    fm = _re.match(r"^---\n(.*?)\n---\n", src.read_text(encoding="utf-8"), _re.S)
    pal = "mono"
    if fm:
        m = _re.search(r"^palette:\s*(\w+)", fm.group(1), _re.M)
        if m: pal = m.group(1).lower()
    env = dict(os.environ, LAYOUT=str(layout), PPTX_SKILL=skill, NODE_PATH=str(HERE / "node_modules"), DECK_PALETTE=pal)
    if a.font: env["FONT"] = a.font
    run(["node", HERE / "gen_pptx.js", pptx], cwd=D, env=env)
    run([sys.executable, HERE / "fix_ppr.py", pptx], cwd=D)
    v = pathlib.Path(skill) / "scripts" / "office" / "validate.py" if skill else None
    if v and v.exists(): run([sys.executable, v, pptx], cwd=D)
print("done:", html.name, "" if a.no_pdf else pdf.name, "" if a.no_pptx else pptx.name)
