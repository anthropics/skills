# Font Reference

How to discover installed fonts, write correct fontspec declarations, pair
fonts, and compile with LuaLaTeX. Read this before using `nofonts` mode.

## Discovering installed fonts

### List all font families

```bash
fc-list : family | sort -u
```

### List families with styles (weights and italics)

```bash
fc-list : family style | sort -u
```

### Search for a specific font

```bash
fc-list : family style file | grep -i "minion"
fc-list : family style file | grep -i "din 2014"
fc-list : family style file | grep -i "frutiger"
```

### List only monospace fonts

```bash
fc-list :spacing=100 family | sort -u
```

### Get full metadata for a single font file

```bash
fc-query --format='family: %{family}\nstyle: %{style}\nweight: %{weight}\nslant: %{slant}\nwidth: %{width}\nfontformat: %{fontformat}\n' ~/Library/Fonts/MinionPro-Regular.otf
```

### Find professional families (4+ weight variants)

```bash
fc-list --format='%{family[0]}\n' | sort | uniq -c | sort -rn | awk '$1 >= 4'
```

### Get the actual filename for fontspec

This is the critical step. fontspec needs the PostScript name (filename
without extension) or the family name fontconfig knows.

```bash
# Get PostScript name (what fontspec uses)
fc-query --format='%{postscriptname}\n' ~/Library/Fonts/MinionPro-Regular.otf
# Output: MinionPro-Regular

# Get all PostScript names for a family
fc-list "Minion Pro" postscriptname | sort
```

Use the PostScript name in `UprightFont`, `BoldFont`, etc.

## Writing fontspec declarations

### The four-face rule

Every `\setmainfont` and `\newfontfamily` MUST declare all four faces.
If a face does not exist, point it at the closest available face.

```latex
% Full family — all four faces exist
\setmainfont{Minion Pro}[
  UprightFont    = MinionPro-Regular,
  BoldFont       = MinionPro-Bold,
  ItalicFont     = MinionPro-It,
  BoldItalicFont = MinionPro-BoldIt,
]

% Single-weight family — self-reference to suppress probing
\newfontfamily\HeadingLight{DIN 2014 Light}[
  UprightFont    = DIN2014-Light,
  ItalicFont     = DIN2014-LightItalic,
  BoldFont       = DIN2014-Light,         % self-reference
  BoldItalicFont = DIN2014-LightItalic,   % self-reference
]

% Single-weight, no italic — point everything at upright
\newfontfamily\DisplayFont{Futura PT Heavy}[
  UprightFont    = FuturaPT-Heavy,
  ItalicFont     = FuturaPT-HeavyOblique,
  BoldFont       = FuturaPT-Heavy,
  BoldItalicFont = FuturaPT-HeavyOblique,
]
```

### Why this matters

fontspec auto-probes for Bold (`/B`) and BoldItalic (`/BI`) variants
when they are not declared. If the font file does not exist under those
suffixes, fontspec logs "Could not resolve font" warnings. Declaring all
four faces explicitly — even if they point at the same file — tells
fontspec to stop looking.

### Optical sizes (Minion Pro)

Minion Pro has four optical size masters. LuaLaTeX can auto-select:

```latex
\setmainfont{Minion Pro}[
  UprightFont      = MinionPro-Regular,
  BoldFont         = MinionPro-Bold,
  ItalicFont       = MinionPro-It,
  BoldItalicFont   = MinionPro-BoldIt,
  SizeFeatures     = {
    {Size=-8.5,   Font=MinionPro-Capt},     % Caption: <8.5pt
    {Size=8.5-13, Font=MinionPro-Regular},   % Text: 8.5-13pt
    {Size=13-21,  Font=MinionPro-Subh},      % Subhead: 13-21pt
    {Size=21-,    Font=MinionPro-Disp},      % Display: >21pt
  },
  Numbers          = OldStyle,
  Ligatures        = {TeX, Common, Contextual},
]
```

## Font pairing

### Principles

1. Pair serif body with sans headings (or vice versa) for contrast.
2. Same-family weight contrast (Light body, Bold headings) is clean.
3. Match x-height between paired fonts.
4. Humanist sans pairs with humanist serif. Geometric sans pairs with
   transitional serif or stands alone.
5. Never pair two different serifs or two different sans at the same
   hierarchy level.

### Classification

| Category | Character | Examples on this system |
|----------|-----------|----------------------|
| Humanist serif | Warm, calligraphic stroke | Minion Pro |
| Neo-grotesque sans | Neutral, uniform stroke | Aktiv Grotesk, Helvetica, Univers |
| Humanist sans | Warm, calligraphic stroke | Neue Frutiger World, Gill Sans Nova |
| Geometric sans | Constructed, circular forms | Futura PT |
| Industrial sans | Engineered, narrow proportions | DIN 2014 |

### Tested pairings

| Body | Headings | Character | Use |
|------|----------|-----------|-----|
| Minion Pro | Aktiv Grotesk | Warm + Swiss neutral | Academic, editorial |
| Minion Pro | Neue Frutiger World | Humanist harmony | Reports, books |
| Minion Pro | DIN 2014 | Warm + industrial | Technical, modern |
| Minion Pro | Gill Sans Nova | Classic British editorial | Formal reports |
| Aktiv Grotesk (all weights) | — | Pure Swiss, weight contrast only | Clean corporate |
| Neue Frutiger World | — | Warm modernist | Presentations |

## Compiling with LuaLaTeX

### Basic compilation

```bash
cd /path/to/document
/Library/TeX/texbin/lualatex --interaction=nonstopmode document.tex
```

### Two passes (for cross-references)

```bash
lualatex --interaction=nonstopmode document.tex
lualatex --interaction=nonstopmode document.tex
```

### With BibTeX

```bash
lualatex --interaction=nonstopmode document.tex
bibtex document
lualatex --interaction=nonstopmode document.tex
lualatex --interaction=nonstopmode document.tex
```

### Checking the log

After compilation, check for zero font warnings:

```bash
grep -i "could not resolve\|not available\|font shape" document.log
```

Target: empty output (no matches).

Check the tufte-swiss summary line:

```bash
grep "tufte-swiss:" document.log
```

Target: `0 overfull, N underfull. P page(s).`

### Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| "Could not resolve font X/B" | Missing BoldFont declaration | Add explicit BoldFont to \newfontfamily |
| "Undefined control sequence \text" | amsmath not loaded | Add `\usepackage{amsmath}` |
| Font renders as fallback | Wrong PostScript name | Run `fc-query --format='%{postscriptname}\n' font.otf` |
| "Font not found" | Font not installed | Check `fc-list \| grep -i "name"` |
| Compile hangs | pdflatex used instead of lualatex | Use `/Library/TeX/texbin/lualatex` |

### Critical: always use LuaLaTeX

tufte-swiss requires LuaLaTeX. Do not use pdflatex or xelatex.

```bash
# Correct
lualatex --interaction=nonstopmode document.tex

# Wrong — will fail
pdflatex document.tex
xelatex document.tex
```
