# LaTeX Template Reference

Used by `formatter_agent` for LaTeX output generation.

## Basic Article Template

```latex
\documentclass[12pt, a4paper]{article}

% === Packages ===
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{times}                    % Times New Roman
\usepackage[margin=1in]{geometry}     % 1-inch margins
\usepackage{setspace}                 % Line spacing
\usepackage{amsmath}                  % Math support
\usepackage{graphicx}                 % Figures
\usepackage{booktabs}                 % Professional tables
\usepackage{hyperref}                 % Clickable links
\usepackage{natbib}                   % APA-style citations
\usepackage{url}                      % URL formatting
\usepackage{float}                    % Figure placement

% === CJK Support (for zh-TW content) ===
% Uncomment for Chinese content:
% \usepackage{xeCJK}
% \setCJKmainfont{Noto Sans CJK TC}
% \setCJKsansfont{Noto Sans CJK TC}

% === Settings ===
\doublespacing                        % APA requires double spacing
\setlength{\parindent}{0.5in}         % First-line indent
\bibliographystyle{apalike}           % APA citation style

% === Metadata ===
\title{Paper Title in Title Case}
\author{Author Name \\
  \small Department, Institution \\
  \small \href{mailto:email@example.com}{email@example.com}
}
\date{\today}

% === Document ===
\begin{document}

\maketitle

\begin{abstract}
\noindent
Abstract text here (150-250 words). No paragraph indent in abstract.
\\[6pt]
\textit{Keywords}: keyword1, keyword2, keyword3, keyword4, keyword5
\end{abstract}

\newpage

\section{Introduction}
Introduction text here.

\section{Literature Review}
\subsection{Theme One}
Text with citation \citep{Smith2024}.

\subsection{Theme Two}
\citet{Jones2023} found that...

\section{Methodology}
\subsection{Research Design}
\subsection{Data Collection}
\subsection{Data Analysis}

\section{Results}
\subsection{Finding One}
See Table~\ref{tab:results}.

\begin{table}[H]
\centering
\caption{Descriptive Statistics}
\label{tab:results}
\begin{tabular}{lccc}
\toprule
Variable & $M$ & $SD$ & $N$ \\
\midrule
Variable 1 & 3.45 & 0.82 & 120 \\
Variable 2 & 4.12 & 0.67 & 120 \\
\bottomrule
\end{tabular}
\end{table}

\section{Discussion}
\subsection{Interpretation}
\subsection{Implications}
\subsection{Limitations}

\section{Conclusion}

% === AI Disclosure ===
\subsection*{AI Disclosure}
This paper was prepared with the assistance of AI-powered academic
writing tools. All content was reviewed and verified by the author(s).

% === References ===
\newpage
\bibliography{references}

\end{document}
```

## APA 7.0 Template (`apa7` Class) — Preferred for APA Output

When APA 7.0 format is requested, use the `apa7` document class instead of `article`. This ensures correct running heads, title page layout, and heading levels.

```latex
\documentclass[man,12pt,natbib]{apa7}

% === Fonts (XeTeX) ===
\usepackage{fontspec}
\setmainfont{Times New Roman}
\usepackage{xeCJK}
\setCJKmainfont{Source Han Serif TC VF}
\setmonofont{Courier New}

% === Additional packages ===
\usepackage{longtable}
\usepackage{booktabs}
\usepackage{array}
\usepackage{graphicx}
\usepackage{float}
\usepackage{hyperref}
\hypersetup{colorlinks=true, linkcolor=black, citecolor=black, urlcolor=blue, breaklinks=true}
\usepackage{xurl}  % URL line breaking (after hyperref)

% === Table column types ===
\newcolumntype{L}[1]{>{\raggedright\arraybackslash}p{#1}}
\newcolumntype{C}[1]{>{\centering\arraybackslash}p{#1}}

% === Justify text (CRITICAL — apa7 man mode defaults to raggedright) ===
\usepackage{ragged2e}
\usepackage{etoolbox}
\AtBeginDocument{\justifying}
\apptocmd{\maketitle}{\justifying}{}{}
\let\oldraggedright\raggedright
\renewcommand{\raggedright}{\justifying}

% === Pandoc compatibility ===
\newcounter{none}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}

% === Metadata ===
\title{Paper Title}
\shorttitle{Short Title for Running Head}
\author{Author Name}
\affiliation{Institution}
\authornote{Author note text.}

% === Abstract (primary language) ===
\abstract{
  Primary language abstract text...

  \newpage

  \begin{center}\textbf{Second Language Abstract Title}\end{center}

  Second language abstract text...
}

\keywords{keyword1, keyword2, keyword3}

\begin{document}
\maketitle

% Body sections here...

\end{document}
```

### Key Differences: `apa7` vs `article`

| Feature | `apa7` class | `article` class |
|---------|-------------|-----------------|
| Running head | Automatic (`\shorttitle`) | Manual (`fancyhdr`) |
| Title page | Built-in (`\maketitle`) | Manual (`titlepage`) |
| Abstract | `\abstract{}` in preamble | `\begin{abstract}` in body |
| Heading levels | APA 5-level automatic | Manual formatting |
| Double spacing | Automatic in `man` mode | Requires `\doublespacing` |
| Text alignment | **Ragged-right (must override!)** | Justified by default |

### Table Column Width Formula (Mandatory)

**NEVER** use bare `p{0.25\linewidth}` in longtable — this ignores inter-column padding and causes overflow.

**Correct formula**: `p{(\linewidth - N\tabcolsep) * \real{proportion}}`

Where N = `(number_of_columns - 1) × 2`

| Columns | N (tabcolseps) | Example |
|---------|---------------|---------|
| 3 | 4 | `(\linewidth - 4\tabcolsep) * \real{0.3333}` |
| 4 | 6 | `(\linewidth - 6\tabcolsep) * \real{0.2500}` |
| 5 | 8 | `(\linewidth - 8\tabcolsep) * \real{0.2000}` |

## BibTeX Entry Formats

### Journal Article
```bibtex
@article{Smith2024,
  author  = {Smith, John A. and Jones, Betty C.},
  title   = {Article title in sentence case},
  journal = {Journal Title in Title Case},
  year    = {2024},
  volume  = {45},
  number  = {2},
  pages   = {123--145},
  doi     = {10.1234/example.2024.001}
}
```

### Book
```bibtex
@book{Brown2023,
  author    = {Brown, Alice},
  title     = {Book Title in Sentence Case},
  publisher = {Publisher Name},
  year      = {2023},
  edition   = {2nd},
  address   = {City}
}
```

### Book Chapter
```bibtex
@incollection{Lee2024,
  author    = {Lee, David},
  title     = {Chapter title in sentence case},
  booktitle = {Book Title in Sentence Case},
  editor    = {Editor, First A.},
  publisher = {Publisher Name},
  year      = {2024},
  pages     = {45--67}
}
```

### Conference Paper
```bibtex
@inproceedings{Chen2024,
  author    = {Chen, Wei and Wang, Ming},
  title     = {Paper title in sentence case},
  booktitle = {Proceedings of the Conference Name},
  year      = {2024},
  pages     = {101--110},
  address   = {City, Country},
  doi       = {10.1234/conf.2024.001}
}
```

### Report / Technical Report
```bibtex
@techreport{MOE2024,
  author      = {{Ministry of Education}},
  title       = {Report title in sentence case},
  institution = {Ministry of Education},
  year        = {2024},
  type        = {Annual Report},
  url         = {https://www.example.com}
}
```

### Thesis / Dissertation
```bibtex
@phdthesis{Wang2024,
  author = {Wang, Mei-Ling},
  title  = {Dissertation title in sentence case},
  school = {National Taiwan University},
  year   = {2024},
  type   = {Doctoral dissertation}
}
```

### Website
```bibtex
@misc{WHO2024,
  author       = {{World Health Organization}},
  title        = {Page title in sentence case},
  year         = {2024},
  howpublished = {\url{https://www.who.int/page}},
  note         = {Accessed: 2024-03-15}
}
```

## Citation Commands

### natbib Commands
| Command | Output | Use For |
|---------|--------|---------|
| `\citet{Smith2024}` | Smith (2024) | Narrative citation |
| `\citep{Smith2024}` | (Smith, 2024) | Parenthetical citation |
| `\citep{Smith2024,Jones2023}` | (Jones, 2023; Smith, 2024) | Multiple |
| `\citeauthor{Smith2024}` | Smith | Author only |
| `\citeyear{Smith2024}` | 2024 | Year only |
| `\citep[p.~45]{Smith2024}` | (Smith, 2024, p. 45) | With page |

### biblatex Commands (Alternative)
| Command | Output |
|---------|--------|
| `\textcite{Smith2024}` | Smith (2024) |
| `\parencite{Smith2024}` | (Smith, 2024) |
| `\autocite{Smith2024}` | (Smith, 2024) — adapts to style |

## XeLaTeX for Chinese Content

When the paper includes zh-TW content:

```latex
\documentclass[12pt, a4paper]{article}
\usepackage{xeCJK}
\setCJKmainfont{Noto Sans CJK TC}     % or 'AR PL UMing TW'
\setCJKsansfont{Noto Sans CJK TC}
\setCJKmonofont{Noto Sans Mono CJK TC}

% Compile with: xelatex paper.tex
```

### Bilingual Abstract in LaTeX
```latex
\begin{abstract}
\noindent
English abstract text here...
\\[6pt]
\textit{Keywords}: keyword1, keyword2, keyword3
\end{abstract}

\begin{center}
\textbf{Chinese Abstract}
\end{center}

\noindent
Chinese abstract content...

\noindent
\textbf{Keywords}: Keyword 1, Keyword 2, Keyword 3
```

## Common LaTeX Compilation Issues

| Issue | Solution |
|-------|---------|
| Chinese characters not showing | Use XeLaTeX instead of pdfLaTeX |
| Bibliography not appearing | Run: latex → bibtex → latex → latex |
| Citations showing [?] | Run bibtex and recompile |
| Hyperlinks not working | Ensure `hyperref` is loaded last |
| Table/figure placement wrong | Use `[H]` from `float` package |
| UTF-8 encoding errors | Ensure `\usepackage[utf8]{inputenc}` |

## Pandoc Conversion Commands

### Markdown → LaTeX
```bash
pandoc paper.md -o paper.tex --bibliography=references.bib --csl=apa.csl
```

### Markdown → PDF (via LaTeX)
```bash
pandoc paper.md -o paper.pdf --pdf-engine=xelatex \
  --bibliography=references.bib --csl=apa.csl \
  -V geometry:margin=1in -V fontsize=12pt -V linestretch=2
```

### Markdown → PDF (with Chinese)
```bash
pandoc paper.md -o paper.pdf --pdf-engine=xelatex \
  -V CJKmainfont="Noto Sans CJK TC" \
  --bibliography=references.bib --csl=apa.csl
```

### Markdown → DOCX
```bash
pandoc paper.md -o paper.docx --bibliography=references.bib --csl=apa.csl
```
