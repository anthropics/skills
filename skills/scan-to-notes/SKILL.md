---
name: "scan-to-notes"
description: "Turn scanned or handwritten PDFs and images (lecture notes, slides, whiteboards, textbook photos) into verified, typeset notes. Use when asked to OCR, transcribe, digitise or make notes from a scan."
---

# Scan to Notes

Convert any image-based source (scanned PDF, phone photos, handwritten pages, slide screenshots, mixed printed/handwritten material) into clean, complete, verified notes. Default output: a compiled LaTeX PDF plus its `.tex` source.

The goal is a faithful, readable reconstruction of the source: same content, same order, correct maths, nothing invented, nothing silently dropped.

## 0. Parse the request

Before touching the file, extract from the user's message:
- **Scope**: whole document, a page range, or named topics.
- **Exclusions**: anything the user said to omit (e.g. "omit Newton-Euler"). Record them; they are applied at the inventory stage, not guessed later.
- **Output format**: LaTeX PDF (default), Markdown, Word, or a doc artifact. If the user named one, use it.
- **Depth**: verbatim transcription vs. restructured study notes. Default: restructured notes that keep every idea, derivation and example from the source.

Ask only if the scope is genuinely ambiguous and the job is large. Otherwise state the reading taken and proceed.

## 1. Locate and classify the source

```bash
pdfinfo file.pdf | grep -E "Pages|Producer"
pdftotext -layout file.pdf - | wc -c
```

- **Text layer present and sensible** (more than ~200 characters per page, words not garbled): extract text with `pdftotext -layout`, and still rasterize pages that carry equations, figures or tables, because text layers flatten maths.
- **No text layer, or garbage**: treat as scanned. Read pages as images.
- **Image files** (png/jpg/heic): treat each as one page; convert HEIC first.
- **Printed, text-heavy scans**: if `tesseract` is installed, it can produce a first-draft transcript, but every line must still be checked against the image. Never use tesseract output for handwriting or equations.

## 2. Rasterize for reading

```bash
mkdir -p $SCRATCH/pages && pdftoppm -r 110 -png file.pdf $SCRATCH/pages/h
```

- Combine pages into **2-page side-by-side spreads** (PIL) for reading: it halves the number of reads while staying legible for handwriting at 110 dpi.
- For dense or faint pages, re-render that page alone at 150-200 dpi, or crop the region in question, before deciding what it says.
- Read **every** page. No sampling, no skipping "similar-looking" pages.

## 3. Transcribe to disk as you go (mandatory for long sources)

Image reads get cleared from context in long sessions. After each batch of 4-8 pages, append a per-page transcript to `$SCRATCH/transcript.md`:

```
## p.17
Topic: Jacobian by direct differentiation
Content: [faithful transcription: equations in LaTeX, prose paraphrased tightly]
Figures: [what the figure shows, labels, axes]
Illegible: [location + best reading, or none]
Suspect: [anything that looks mathematically wrong, to verify later]
```

Build the final document from this file, not from memory.

## 4. Build the page inventory

From the transcript, produce a table: page range -> section/topic -> content type (definition, derivation, worked example, figure, table, summary). Use it to:
- Mark excluded pages (from step 0). List them in the final reply.
- Detect the logical order. Handwritten notes are sometimes scanned out of order; follow the content's logic, and say so if pages were reordered.
- Merge repeated material (the same derivation written twice) into one clean version.
- Note syllabus topics the user expects but the source does not contain. Do not fill them in unless asked; list them as gaps.

## 5. Reconstruct the content

Rules:
1. **Coverage**: every definition, derivation step, worked example, figure and table in scope appears in the output. Restructuring is fine; omission is not.
2. **Notation**: pick one notation and apply it consistently (frames, subscripts, transposes, units). Add a short Notation section. Expand every abbreviation at first use.
3. **Derivations**: keep the source's steps, filling in skipped algebra where a reader would get stuck. Show substitutions in worked examples.
4. **Figures**: redraw important diagrams in TikZ (or describe them precisely). Plot functions with pgfplots when the source sketches curves (trajectories, responses). Do not paste the scan as an image unless the user asks.
5. **Illegible content**: write the best reading and flag it `[unclear in source: ...]`. Never invent a value to fill a gap.
6. **Key results**: put boxed or highlighted summaries around formulas a student must memorise.
7. **Source authority**: the scan defines *what* is covered. If the user says not to follow the source's teaching style, keep its content but explain it your own way.

## 6. Verify the maths (do not skip)

Handwritten notes contain errors. For every formula and example:
- **Re-derive symbolically** (sympy) any closed-form result: polynomial coefficients, matrix products, inverses, determinants.
- **Recompute every number** in worked examples (python).
- **Special-case checks**: a general formula must reduce to the known special case (e.g. general cubic with zero end velocities must equal the rest-to-rest cubic; a Jacobian from two methods must match).
- **Physical/dimensional sanity**: units, signs, limits (what happens as a parameter goes to 0 or infinity).

When the source is wrong: put the correct version in the body, and list each correction in a final **"Corrections to the source"** section: what the source says, what is correct, and how it was checked. Never correct silently; never "correct" something you could not verify.

## 7. Typeset (default LaTeX)

Preamble that works:
```latex
\documentclass[11pt,a4paper]{article}
\usepackage[margin=2.1cm]{geometry}
\usepackage{amsmath,amssymb,booktabs,array,enumitem,xcolor,hyperref}
\usepackage{tikz,pgfplots}\pgfplotsset{compat=1.17}\usepgfplotslibrary{groupplots}
\usetikzlibrary{arrows.meta,calc}
\usepackage[most]{tcolorbox}
\usepackage{fancyhdr}\setlength{\headheight}{14pt}
\setcounter{MaxMatrixCols}{12}
\newtcolorbox{keybox}[1][]{colback=blue!4,colframe=blue!45!black,boxrule=0.6pt,arc=2pt,fonttitle=\bfseries\small,#1}
```

Known pitfalls:
- tcolorbox titles containing commas must be braced: `[title={Cubic, rest to rest}]`. Do not regex-brace option lists blindly: it will also wrap pgfplots options such as `ymin=`.
- `\ss`, `\cc` and other short names may already be defined; do not redefine them.
- `groupplot` needs `\usepgfplotslibrary{groupplots}`.
- Matrices: `bmatrix`; wide expressions go in `align*` or are split across lines; long vectors are written component by component.
- Leading super/subscripts: define `\newcommand{\pre}[2]{{}^{#1}\!#2}`.

If the user asked for another format, follow that format's skill instead. In chat replies, never use `\\` line breaks in LaTeX (they render broken); use tables or one-line equations.

## 8. Quality check before delivering

1. Compile twice with `pdflatex -interaction=nonstopmode`; grep the log for `^!` (errors) and `Overfull` (fix anything above ~10pt).
2. Render every page to PNG (`pdftoppm -r 60`), combine into 4-page strips, and look at all of them: overlapping labels, clipped equations, stray option text in plot titles, empty boxes, broken page breaks.
3. For figures, re-render the page at 130-150 dpi and inspect closely.
4. Cross-check the table of contents against the page inventory: every in-scope topic present, excluded topics absent.

## 9. Deliver

Send the PDF and the `.tex` source with a one-line caption. The reply then states, briefly:
- the source scanned and how many pages were read, and what was excluded;
- the section structure of the notes (one line each);
- every correction made to the source;
- gaps: expected topics the source does not contain;
- any content flagged as unclear.

No recap of the process.