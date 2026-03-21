---
name: tufte-swiss-typography
description: >
  Generate PDFs with Tufte-grade Swiss micro-typography using LuaLaTeX.
  12pt baseline grid, perfect fourth type scale (9/12/16/21pt), four-gray
  hierarchy, microtype paragraph building with hanging punctuation and glyph
  expansion. Supports any OTF font via nofonts option with fc-list discovery.
  Use for professional documents, resumes, reports, proposals, academic papers,
  or any PDF requiring typographic precision. Triggers: elegant PDFs, Swiss
  style design, Tufte aesthetics, justified text blocks, baseline grids,
  LuaLaTeX documents, beautiful typography, professional formatting.
---

# Tufte-Swiss Typography Toolkit

Five systems, two primitives, zero document-specific opinions.

```
assets/tufte-swiss.sty         ← The package. \usepackage{tufte-swiss}
assets/tufte-swiss-grid.lua    ← Lua callbacks (must accompany .sty at compile time)
assets/example-onepager.tex    ← Working demo
scripts/smoke_test.sh          ← Compile + verify after any .sty change
references/FONT_REFERENCE.md   ← Font discovery, fontspec, pairing (read for custom fonts)
references/TYPOGRAPHY_SPEC.md  ← Deep parameter reference (read when tuning)
```

## Compilation

Always LuaLaTeX. Never pdflatex or xelatex. Copy both `.sty` and `.lua`
to the build directory before compiling.

```bash
cp ~/.claude/skills/tufte-swiss-typography/assets/tufte-swiss.sty ./
cp ~/.claude/skills/tufte-swiss-typography/assets/tufte-swiss-grid.lua ./
lualatex --interaction=nonstopmode document.tex
```

Check the log after every compile — target zero overfull boxes:

```bash
grep "tufte-swiss:" document.log
```

## Minimal Document

```latex
\documentclass[10pt]{article}
\usepackage{tufte-swiss}
\geometry{paper=letterpaper, margin=20mm, heightrounded}

\begin{document}
\TSTitle\TSBlack Title Here\par
\vspace{\TSGrid}
\TSBody Body text in 9/12 on a 12pt grid.
\end{document}
```

## The Five Systems

### 1. Type Scale — perfect fourth (4:3)

| Command    | Size/Lead | Use                |
| ---------- | --------- | ------------------ |
| `\TSMicro` | 7/12      | Labels, fine print |
| `\TSBody`  | 9/12      | Body text          |
| `\TSStep`  | 12/12     | Subheads           |
| `\TSLarge` | 16/18     | Display            |
| `\TSTitle` | 21/24     | Titles             |

### 2. Baseline Grid

`\TSGrid` = 12pt (one grid unit). `\TSHalf` = 6pt. Snap all vertical
spacing to multiples of these. The grid equals body leading — columns align.

### 3. Color Palette — four grays

| Color         | Hex       | Use               |
| ------------- | --------- | ----------------- |
| `TSText`      | `#111111` | Primary text      |
| `TSMuted`     | `#5D5D5D` | Secondary, labels |
| `TSRuleColor` | `#C8C8C8` | Rules, dividers   |
| `TSStrong`    | `#202020` | Emphasis rules    |

Use color for hierarchy, not decoration. One accent color max per document.

### 4. Fonts

**Default mode** (`\usepackage{tufte-swiss}`): Aktiv Grotesk loaded with
eight weight commands (`\TSLight` through `\TSBlack`).

**Custom mode** (`\usepackage[nofonts]{tufte-swiss}`): No fonts loaded.
You call `\setmainfont` and optionally define weight commands.

To use custom fonts, read `references/FONT_REFERENCE.md` — it covers
`fc-list` discovery, the four-face rule, font pairing, and troubleshooting.

**The four-face rule** (critical): Every `\setmainfont` and `\newfontfamily`
must declare `UprightFont`, `ItalicFont`, `BoldFont`, `BoldItalicFont`. For
single-weight families, set `BoldFont` = `UprightFont` (self-reference
suppresses fontspec auto-probing).

### 5. Paragraph Builder

Enabled automatically. Protrusion (hanging punctuation), expansion (up to
2% glyph width), absolute widow/orphan prevention, tuned hyphenation. See
`references/TYPOGRAPHY_SPEC.md` for parameter details.

## The Two Primitives

`\TSRule[color]{width}{weight}` — horizontal rule. Default: `TSRuleColor`.

`\TSTrack[amount]{text}` — letter-spaced text. Default: 100 (1/1000 em).

```latex
\TSRule{\linewidth}{0.2pt}              % light divider
\TSRule[TSStrong]{\linewidth}{0.6pt}    % heavy rule
\TSTrack{SECTION LABEL}                 % tracked uppercase
```

## Composition Principles

- Set geometry per document. The toolkit loads geometry but does not configure it.
- Define your own semantic macros from the toolkit primitives.
- Snap spacing to `\TSGrid` / `\TSHalf`.
- Color for hierarchy only — `TSText`, `TSMuted`, `TSRuleColor`, `TSStrong`.
- Trust the paragraph builder. Use `\RaggedRight` (ragged2e) for ragged-right.
- Headers/footers are your job — load `fancyhdr` if needed.

## Smoke Test

```bash
bash ~/.claude/skills/tufte-swiss-typography/scripts/smoke_test.sh
```
