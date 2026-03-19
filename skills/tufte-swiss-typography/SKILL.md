---
name: tufte-swiss-typography
description: >
  Generate PDFs with Tufte-grade Swiss micro-typography featuring LuaLaTeX
  precision. Implements 12pt baseline grid, perfect fourth type scale
  (9/12/16/21pt), four-gray hierarchy, microtype paragraph building with
  hanging punctuation and glyph expansion. Use for professional documents,
  resumes, reports, proposals, or any PDF requiring typographic precision.
  Triggers: elegant PDFs, Swiss style design, Tufte aesthetics, justified
  text blocks, baseline grids, LuaLaTeX documents.
---

# Tufte-Swiss Typography Toolkit

A LuaLaTeX system for documents that Tufte and a Swiss typographer would
respect. Five systems, two primitives, zero document-specific opinions.

## What This Is

A portable `.sty` package that provides:

1. **Type scale** — five named sizes on a perfect fourth progression
2. **Baseline grid** — 12pt grid with 6pt half-grid
3. **Color palette** — four grays for hierarchy without decoration
4. **Font setup** — Aktiv Grotesk via fontspec with eight weight commands
5. **Paragraph builder** — microtype protrusion + expansion, tuned penalties

Plus two structural primitives: `\TSRule` and `\TSTrack`.

You define the document's semantic macros. The toolkit provides the vocabulary.

## Files

```text
tufte-swiss-typography/
├── SKILL.md                          ← You are here
├── assets/
│   ├── tufte-swiss.sty               ← The toolkit (load with \usepackage)
│   ├── tufte-swiss-grid.lua          ← Observational callbacks
│   └── example-onepager.tex          ← Executive briefing demo
├── scripts/
│   └── smoke_test.sh                 ← Compile + verify
└── references/
    └── TYPOGRAPHY_SPEC.md            ← Deep parameter reference
```

## How to Use

### Minimal Document

```latex
\documentclass[10pt]{article}
\usepackage{tufte-swiss}

\geometry{paper=letterpaper, margin=20mm, heightrounded}

\begin{document}
\TSTitle\TSBlack Title Here\par
\vspace{\TSGrid}
\TSBody Body text in 9/12 Aktiv Grotesk on a 12pt grid.
\end{document}
```

### Compilation

Both `.sty` and `.lua` must be in the same directory as the `.tex` file
(or on the TEXINPUTS path).

```bash
cd tufte-swiss-typography/assets
/Library/TeX/texbin/lualatex -interaction=nonstopmode your-document.tex
```

Or use the smoke test:

```bash
bash tufte-swiss-typography/scripts/smoke_test.sh
```

## The Five Systems

### 1. Type Scale

Perfect fourth (4:3) from a 9pt base. Each command sets size AND leading.

| Command    | Size/Lead | Use                     |
|------------|-----------|-------------------------|
| `\TSMicro` | 7/12      | Labels, fine print      |
| `\TSBody`  | 9/12      | Primary reading text    |
| `\TSStep`  | 12/12     | Subheads, role titles   |
| `\TSLarge` | 16/18     | Display, cover names    |
| `\TSTitle` | 21/24     | Titles, resume names    |

WHY these sizes: The steps are distinct enough to signal hierarchy but
close enough to feel like one family. 9pt body is dense but readable.
12pt leading is the grid unit. Everything locks together.

### 2. Baseline Grid

| Length    | Value | Use                 |
|-----------|-------|---------------------|
| `\TSGrid` | 12pt  | Standard spacing    |
| `\TSHalf` | 6pt   | Fine spacing        |

WHY 12pt: The grid equals the body leading. Every line of body text sits
on a grid line. Columns align. The page feels architecturally solid.

Snap all vertical spacing to multiples of `\TSGrid` or `\TSHalf`:

```latex
\vspace{\TSGrid}               % 12pt — one grid unit
\vspace{2\TSGrid}              % 24pt — before sections
\vspace{\TSHalf}               % 6pt  — tight gaps
```

### 3. Color Palette

| Color          | Hex       | Use                  |
|----------------|-----------|----------------------|
| `TSText`       | `#111111` | Primary text         |
| `TSMuted`      | `#5D5D5D` | Secondary, labels    |
| `TSRuleColor`  | `#C8C8C8` | Rules, dividers      |
| `TSStrong`     | `#202020` | Emphasis rules       |

WHY near-black: Pure black vibrates against white paper. `#111111` is
perceptually identical but quieter. Use color for hierarchy, not decoration.

### 4. Fonts

Default: Aktiv Grotesk (must be in ~/Library/Fonts/ or system fonts).

| Command        | Weight                  |
|----------------|-------------------------|
| (default)      | Regular                 |
| `\bfseries`    | Bold                    |
| `\itshape`     | Italic                  |
| `\TSLight`     | Light                   |
| `\TSMedium`    | Medium                  |
| `\TSSemiBold`  | SemiBold                |
| `\TSBlack`     | Black                   |
| `\TSLabelFont` | Medium + letter-spacing |

Override: `\setmainfont{Other Font}[...]` after `\usepackage{tufte-swiss}`.

### 5. Paragraph Builder

Enabled automatically. You get:

- Protrusion (hanging punctuation for optical margin alignment)
- Expansion (up to 2% glyph width adjustment for tighter lines)
- Widow/orphan prevention (absolute)
- Tuned hyphenation (no consecutive hyphens, no final-line hyphens)

No configuration needed. See `references/TYPOGRAPHY_SPEC.md` for parameter
details and tuning guidance.

## The Two Primitives

### `\TSRule[color]{width}{weight}`

Horizontal rule. Default color: `TSRuleColor`.

```latex
\TSRule{\linewidth}{0.2pt}                 % light full-width divider
\TSRule[TSStrong]{\linewidth}{0.6pt}       % heavy emphasis rule
\TSRule{0.5\linewidth}{0.2pt}             % half-width
```

### `\TSTrack[amount]{text}`

Letter-spaced text. Default tracking: 100 (1/1000 em).

```latex
\TSTrack{EXPERIENCE}                       % section label
\TSTrack[60]{Sub-label}                    % lighter tracking
```

Also: `\TSLabelFont` for blocks that need persistent tracking.

## Principles for Document Composition

These are guidelines, not rules. The toolkit provides vocabulary; you write
the prose.

**Set your own geometry.** Different documents need different margins. Call
`\geometry{...}` per document. The toolkit loads geometry but does not
configure it.

**Define your own macros.** Build `\SectionHead`, `\RoleEntry`, `\MetaLine`
from the toolkit primitives. The example document shows how.

**Snap spacing to the grid.** Use `\TSGrid` and `\TSHalf` for all vertical
space. This keeps lines aligned and the page composed.

**Use color for hierarchy, not decoration.** `TSText` for primary content.
`TSMuted` for secondary. `TSRuleColor` for structural lines. `TSStrong`
for emphasis lines. That's it.

**Let TeX break paragraphs.** The paragraph builder is tuned. Set justified
text and trust the algorithm. For ragged-right, use `\RaggedRight` (from
ragged2e) — it still hyphenates, unlike `\raggedright`.

**Headers and footers are your job.** Load `fancyhdr` if you need them.
The toolkit doesn't assume page furniture.

## Callbacks

The Lua module (`tufte-swiss-grid.lua`) registers three observational
callbacks:

- `hpack_quality` — counts overfull/underfull boxes
- `start_page_number` — tracks page count
- `stop_run` — prints summary: `tufte-swiss: N overfull, M underfull. P page(s).`

Check the log for the summary line after every compile. Zero overfull boxes
is the target.

## Smoke Test

```bash
bash scripts/smoke_test.sh
```

Verifies: exit code 0, `tufte-swiss:` summary in log, PDF exists.
