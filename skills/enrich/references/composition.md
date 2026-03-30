# Composition Guide

You are a typographer. Design each report from scratch. No templates.

## Setup

```bash
# Copy tufte-swiss assets into build directory
cp ~/.claude/skills/tufte-swiss-typography/assets/tufte-swiss.sty ./
cp ~/.claude/skills/tufte-swiss-typography/assets/tufte-swiss-grid.lua ./
```

```latex
\documentclass[10pt]{article}
\usepackage[nofonts]{tufte-swiss}  % nofonts — you pick the typeface
\usepackage{sidenotes}             % Tufte-style margin notes
\usepackage{marginfix}             % Prevent margin note collisions
\usepackage{tikz}                  % Connection diagrams
\usepackage{tcolorbox}             % Callout boxes for novel insights
\usepackage{sparklines}            % Inline data-words
\usepackage{booktabs}              % Clean tables

% Asymmetric Tufte layout: text left, evidence right
\geometry{
  paper=letterpaper,
  left=20mm,
  right=75mm,           % Wide right margin for sidenotes
  top=25mm,
  bottom=25mm,
  marginparwidth=60mm,  % Sidenote column width
  marginparsep=8mm,
  heightrounded
}
```

## Font Selection

Run `fc-list : family style | sort` to see installed fonts. Pick based on content:

- **Regulatory/financial tone**: Avenir LT Pro, Aktiv Grotesk (clean sans)
- **Scientific/academic tone**: Athelas body + Aktiv Grotesk heads (serif/sans pair)
- **Executive brief tone**: Charter (readable, authoritative serif)

Four-face rule: every `\setmainfont` must declare UprightFont, ItalicFont, BoldFont, BoldItalicFont explicitly. Check weight coverage with `fc-list "FontName" : style`.

## Typography Primitives

| Command | Size | Use for |
|---------|------|---------|
| `\TSTitle` | 21/24pt | Report title |
| `\TSLarge` | 16/18pt | Section heads, headline findings |
| `\TSStep` | 12/12pt | Subsection heads, callout headlines |
| `\TSBody` | 9/12pt | Body text |
| `\TSMicro` | 7/12pt | Margin citations, fine print |
| `\TSRule` | -- | Horizontal dividers |
| `\TSTrack` | -- | Letter-spaced labels |
| `\TSMuted` | -- | Secondary text color |

## The Margin Is the Evidence Layer

Left column (body): clean narrative prose. Right margin: every source, every tier badge, small data graphics.

```latex
Semaglutide reduces body weight by 14.9\% at 68 weeks%
\sidenote{%
  {\TSMicro\color{TSMuted}%
  \textbf{[T1]} FDA label, NDA 215256\\
  \textbf{[T2]} STEP 1 trial, PMID:33567185\\
  14.9\% vs 2.4\% placebo, $p<0.001$}%
}%
compared to 2.4\% with placebo.
```

## Callout Patterns

The LLM decides when to use each. These are options, not requirements:

**Novel Insight Box**:

```latex
\begin{tcolorbox}[colback=black!3, colframe=black!20, boxrule=0.4pt,
  title={\TSStep\TSTrack{NOVEL INSIGHT}}]
{\TSBody Headline finding here.}\\[6pt]
{\TSMicro\color{TSMuted} Evidence chain: A → B → C → D\\
Sources: [T1: ...] [T2: ...] \\
Implication: commercial/clinical significance}
\end{tcolorbox}
```

**Connection Diagram** (TikZ):

```latex
\begin{tikzpicture}[node distance=2cm, >=stealth, every node/.style={font=\TSMicro}]
  \node (A) {GLP-1R};
  \node (B) [right of=A] {Hippocampus};
  \node (C) [right of=B] {Neuroprotection};
  \draw[->] (A) -- node[above] {\tiny T2} (B);
  \draw[->] (B) -- node[above] {\tiny T1} (C);
\end{tikzpicture}
```

**Sparkline** (inline data-word):

```latex
Trial enrollment is accelerating
\begin{sparkline}{4}
  \spark 0 0.1  0.2 0.15  0.4 0.3  0.6 0.5  0.8 0.7  1 1 /
\end{sparkline}
with 340 patients enrolled in Q4.
```

**Audit Table** (claims verification):

```latex
\begin{tabular}{@{}p{5cm}lp{4cm}@{}}
\toprule
{\TSMicro Claim} & {\TSMicro Status} & {\TSMicro Evidence} \\
\midrule
Weight loss 15-20\% & \textcolor{green!50!black}{Verified} & STEP 1, PMID:33567185 \\
No CV risk & \textcolor{orange!80!black}{Corrected} & CV \emph{benefit} shown (SUSTAIN-6) \\
\bottomrule
\end{tabular}
```

## Tufte's Principles — Your Design Vocabulary

Use these when deciding how to present each finding:

- **Above all else, show the data** — the finding IS the content, not the decoration around it
- **Maximize data-ink ratio** — if removing an element doesn't lose information, remove it
- **Smallest effective difference** — visual distinctions just large enough to be perceived
- **Integrate text and graphics** — sparklines in sentences, diagrams next to prose, citations in margins
- **Escape flatland** — use margins, sidenotes, inline graphics — not just the body column
- **Content-proportional ink** — bigger finding gets more visual weight
- **Layering** — body text is the story, margin is the evidence, callout boxes are the headlines

## Visual QA

After compiling, read every page as an image. Fix:

- Margin notes overlapping each other → add `\vspace` or reduce sidenote count per page
- Tables overflowing → reduce columns, wrap text, or use `\small`
- TikZ diagrams broken → simplify, reduce node count
- Bad page breaks → add `\pagebreak` or restructure content
- Excessive whitespace → LaTeX gave up on float placement; restructure

Recompile and re-inspect until every page passes.

## What You Decide

- Which sections exist and in what order
- What gets a callout box vs inline text vs a margin note
- Whether to lead with the biggest novel insight or build to it
- How much space each finding gets (proportional to its importance)
- Document length — 2 pages or 12, driven by content
- Font pairing — justify your choice in the methodology note
