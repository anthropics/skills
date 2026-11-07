# Deck pipeline

Turns one Markdown manuscript (`PPT Text.md`) into an HTML deck, a PDF and an editable PPTX.
`make_deck.py` runs all steps; each script can also be run on its own.

```
PPT Text.md ──build.py──▶ {name}.html ──mkpdf.py──▶ {name}.pdf
                              │
                          measure.py ──▶ layout.json + snaps/*.png
                              │
                          fit_notes.py (layout.json [+ script.md])
                              │
                          gen_pptx.js ──▶ {name}.pptx ──fix_ppr.py──▶ {name}.pptx
```

| Step | What it does |
|---|---|
| `build.py src.md out.html` | Parses frontmatter + slides, renders Markdown, KaTeX math, SVG diagrams from `svgs.py`, placeholders; writes a single-file HTML deck (1440x1080, 4:3) with keyboard/click navigation. |
| `mkpdf.py deck.html deck.pdf` | Prints the HTML deck to PDF with headless Chromium (one slide per page; videos become their poster image). |
| `measure.py deck.html layout.json` | Opens the deck in Chromium and exports every element with its pixel position, font size and text runs to `layout.json`; SVG diagrams and equations are screenshotted to `snaps/`. |
| `fit_notes.py layout.json [script.md]` | Contain-fits image/video boxes to the media's real aspect ratio, and attaches the `## p.N` sections of a speaker script as presenter notes. |
| `gen_pptx.js out.pptx` | Builds an editable 4:3 PPTX from `layout.json` with pptxgenjs (text boxes, lists, tables, images, code, placeholders, notes). Env: `LAYOUT`, `FONT`, `DECK_PALETTE`, `PPTX_SKILL`. |
| `fix_ppr.py out.pptx` | Removes stray mid-paragraph `<a:pPr>` elements that pptxgenjs inserts between runs. |

Helpers: `katex_render.js` (TeX -> HTML, used by `build.py`), `svgs_template.py` (starting point for a deck's `svgs.py`).

## Setup

```
cd scripts/deck
npm install            # katex, pptxgenjs, @fontsource/noto-serif
pip install -r requirements.txt
python -m playwright install chromium
```

`ffmpeg`/`ffprobe` is optional (video aspect ratio in `fit_notes.py`).

## Running

```
python scripts/deck/make_deck.py "PPT Text.md" --name "Week5 Review" --script "script.md"
```

Outputs `Week5 Review.html`, `Week5 Review.pdf` and `Week5 Review.pptx` next to the manuscript
(`layout.json`, `snaps/`, `measure.html`, `print_tmp.html` are intermediate files).
`make_deck.py` symlinks `scripts/deck/node_modules` into the deck folder so the HTML can embed the KaTeX fonts.

Options:

- `--script script.md` — speaker script whose `## p.N` sections become presenter notes in the PPTX.
- `--font "Noto Serif"` — font face written into the PPTX (default `Malgun Gothic`).
- `--no-pdf`, `--no-pptx` — skip those outputs.
- `--pptx-skill <folder>` (or env `PPTX_SKILL`) — path to the Anthropic `pptx` skill. When given, `gen_pptx.js`
  applies the deck theme with the skill's `scripts/apply_theme.js` and `make_deck.py` runs its
  `scripts/office/validate.py` on the result. **Without it the PPTX is still generated**; only theme
  application and validation are skipped.

Check the rendered deck for overflow, overlaps and broken images:

```
python scripts/render_check.py "Week5 Review.html" --static --sheet 6 --out check
```

## Manuscript format

### Frontmatter

```
---
deck: Week 5 Paper Review
lang: en
author: Jane Doe
org: Example Lab
footer_left: Jane Doe · Example Lab
footer_center: Lab seminar
date: 2026-11-01
font: serif
palette: mono
---
```

| Key | Meaning |
|---|---|
| `deck` | HTML `<title>` and PPTX title. |
| `lang` | `ko` or `en` (`<html lang>`; also the default font family: `en` -> serif, `ko` -> sans). |
| `author`, `org` | Cover slide and default footer (`author · org`). |
| `footer_left`, `footer_center` | Footer text (left / center; the right slot is the slide number). |
| `date` | Date line on the cover. |
| `font` | `serif` (embeds Noto Serif) or `sans`. |
| `palette` | `mono` (default: text, titles and diagrams in grayscale; images keep their colors) or `color` (blue/maroon accents). |

### Slides and markers

- Slides are separated by a line containing only `---` (outside code fences).
- Slide 1 starting with `# Title` (+ optional `### subtitle`) is the cover. `# Part N: Title` makes a section divider.
- `## Title` is the slide title, `### text` its subtitle. A leading `[Tag]` in the title is rendered as a chip: `## [Method] Residual action`.
- `|||` on its own line splits the body into two columns (text before the first `|||` spans the full width).
- `> note` — speaker note (hidden in the deck, exported to notes). `>> text` — emphasis line at the bottom of the slide.
- `$$ … $$` on one line — display math (KaTeX).
- `(figure: description)` or `(그림: …)` — SVG diagram; the N-th marker in the manuscript calls `SVGS[N-1]()` from `svgs.py` next to the manuscript (see `svgs_template.py`).
- `![](path.png)` / `![](clip.mp4)` — image or video (video poster: `clip_poster.jpg`).
- `[[Kind | what | source | why]]` — placeholder box. `Kind` starts with `Photo`, `Video` (`[[Video | what | source | time span | why]]`), `Repro` or `Paper Fig` (any other kind is also treated as a paper figure); Korean kinds (`사진`, `영상`, `재현`) are accepted too.
- Caption lines start with `Fig.`, `Table`, `▶ ` (video caption) or `Source:` (`출처:`); a caption directly under an image or table is attached to it, except `Source:` lines, which stay free-standing.
- A line like `Smith et al., 2025` (`Name et al., `) is rendered as a right-aligned citation.
- Fenced code blocks and Markdown tables are supported.
