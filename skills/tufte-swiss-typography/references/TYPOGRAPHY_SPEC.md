# Typography Specification

Deep reference for the tufte-swiss LuaLaTeX toolkit.

## Type Scale

**System**: Perfect fourth (4:3 ratio) from a 9pt base.

| Step | Size | Leading | Command    | Use                   |
| ---- | ---- | ------- | ---------- | --------------------- |
| -1   | 7pt  | 12pt    | `\TSMicro` | Labels, fine print    |
| 0    | 9pt  | 12pt    | `\TSBody`  | Primary reading text  |
| +1   | 12pt | 12pt    | `\TSStep`  | Subheads, role titles |
| +2   | 16pt | 18pt    | `\TSLarge` | Display, cover names  |
| +3   | 21pt | 24pt    | `\TSTitle` | Titles, resume names  |

**Why perfect fourth**: The 4:3 ratio produces steps that are distinct enough
to signal hierarchy but close enough to feel cohesive. Larger ratios (golden
section, augmented fourth) create dramatic jumps that suit editorial design but
overwhelm information-dense documents. Smaller ratios (major third) produce
steps that are hard to distinguish at text sizes.

**Why 9pt base**: 9pt Aktiv Grotesk has an x-height of approximately 4.5pt,
which produces comfortable reading at arm's length on letter paper. 10pt is the
LaTeX default but wastes vertical space in dense documents. 8pt is readable but
fatiguing over multiple pages.

## Baseline Grid

**Grid unit**: 12pt (the body leading).
**Half-grid**: 6pt.

All vertical spacing should be a multiple of `\TSGrid` (12pt) or `\TSHalf`
(6pt). This locks text lines across columns, creates even texture in
multi-column layouts, and makes the page feel architecturally solid rather than
casually stacked.

**Why 12pt**: The grid equals the body leading. When the grid matches the
leading, every line of body text sits exactly on a grid line. This is standard
professional practice in book and magazine typography. A 4pt grid sounds finer
but is fiction in practice because most spacing values are not multiples of 4.

**Snapping rules**:

- Space before sections: 2 grid (24pt)
- Space after section heads: 1 grid (12pt)
- Entry gaps: 1 grid (12pt)
- Small gaps (bullets, summaries): 1 half-grid (6pt)

## Color Palette

| Name          | Hex       | Use                       |
| ------------- | --------- | ------------------------- |
| `TSText`      | `#111111` | Primary text (near-black) |
| `TSMuted`     | `#5D5D5D` | Secondary text, labels    |
| `TSRuleColor` | `#C8C8C8` | Rules, dividers           |
| `TSStrong`    | `#202020` | Emphasis rules            |

**Why near-black, not pure black**: Pure black (#000000) on white paper creates
maximum contrast. That sounds desirable but is actually harsh — the text
vibrates against the page, especially under fluorescent lighting. Near-black
(#111111) is perceptually almost identical but produces a quieter, more
comfortable reading experience. This is standard practice in professional
typography (most books print in a dark gray, not pure black).

**Why four levels**: Fewer levels produce clearer hierarchy. Five or more grays
create near-indistinguishable steps at small sizes. Four levels — text, muted,
rule, strong — cover every common need: primary content, secondary labels,
structural dividers, and emphasis dividers.

## Font Setup

**Default family**: Aktiv Grotesk (Dalton Maag, 2014).

A contemporary grotesque with Helvetica's proportions but better ink traps,
open counters, and hinting at small sizes. The full weight range is available:

| Command        | Weight    | Use                     |
| -------------- | --------- | ----------------------- |
| (default)      | Regular   | Body text               |
| `\bfseries`    | Bold      | Inline emphasis         |
| `\itshape`     | Italic    | Titles, citations       |
| `\TSLight`     | Light     | Delicate display text   |
| `\TSMedium`    | Medium    | Labels, meta values     |
| `\TSSemiBold`  | SemiBold  | Section heads, subheads |
| `\TSBlack`     | Black     | Names, titles           |
| `\TSLabelFont` | Medium+LS | Pre-tracked label text  |

**Override**: Call `\setmainfont{...}` after loading `tufte-swiss` to replace
the entire family. The scale commands, grid, colors, and paragraph builder
remain unchanged.

## Paragraph Builder

The paragraph builder controls how TeX breaks text into lines.

### Penalties

| Parameter              | Value | Effect                       |
| ---------------------- | ----- | ---------------------------- |
| `\clubpenalty`         | 10000 | Forbid orphans (page bottom) |
| `\widowpenalty`        | 10000 | Forbid widows (page top)     |
| `\displaywidowpenalty` | 10000 | Same for display math        |

### Tolerances

| Parameter           | Value | Effect                                |
| ------------------- | ----- | ------------------------------------- |
| `\pretolerance`     | 100   | First pass (no hyphen) badness cap    |
| `\tolerance`        | 400   | Second pass (with hyphen) badness cap |
| `\emergencystretch` | 6pt   | Third pass stretch to avoid overfull  |

**How it works**: TeX tries three passes. First, it sets the paragraph without
hyphenation (pretolerance=100 catches ~80% of paragraphs). If that fails, it
tries with hyphenation (tolerance=400). If that still fails, it adds up to 6pt
of invisible stretch (emergencystretch) to avoid overfull boxes.

### Hyphenation

| Parameter               | Value | Effect                                    |
| ----------------------- | ----- | ----------------------------------------- |
| `\hyphenpenalty`        | 50    | Cost of a hyphen break                    |
| `\exhyphenpenalty`      | 50    | Cost of breaking at an explicit hyphen    |
| `\doublehyphendemerits` | 10000 | Penalty for consecutive hyphenated lines  |
| `\finalhyphendemerits`  | 5000  | Penalty for hyphen on second-to-last line |
| `\adjdemerits`          | 10000 | Penalty for adjacent incompatible lines   |
| `\linepenalty`          | 10    | Per-line cost (favors fewer lines)        |

**What demerits mean**: Demerits are squared penalties. TeX minimizes total
demerits across the paragraph, not individual line badness. High
`doublehyphendemerits` (10000) means TeX will accept slightly worse spacing to
avoid two consecutive hyphenated lines. High `adjdemerits` (10000) discourages
adjacent lines with very different tightness.

### Microtype

| Parameter    | Value | Effect                              |
| ------------ | ----- | ----------------------------------- |
| `protrusion` | true  | Hang punctuation into margins       |
| `expansion`  | true  | Adjust glyph widths for spacing     |
| `tracking`   | false | No global tracking (use `\TSTrack`) |
| `stretch`    | 20    | Max glyph width expansion: 2%       |
| `shrink`     | 20    | Max glyph width shrinkage: 2%       |
| `step`       | 1     | Expansion granularity: 0.1%         |

**Protrusion**: Small punctuation (periods, commas, hyphens) hangs slightly
past the margin so the text edge looks optically straight. Without protrusion,
lines ending in punctuation appear indented. This is the digital equivalent of
Gutenberg's hanging punctuation.

**Expansion**: TeX can stretch or shrink each glyph by up to 2% to improve
line breaks. The distortion is imperceptible but the effect on spacing is
significant — it eliminates many overfull boxes that would otherwise require
hyphenation or loose lines.

## Primitives

### `\TSRule[color]{width}{weight}`

A horizontal rule. Default color is `TSRuleColor`. Use for section dividers,
header separators, and structural lines.

```latex
\TSRule{\linewidth}{0.2pt}                   % light full-width rule
\TSRule[TSStrong]{\linewidth}{0.6pt}         % heavy emphasis rule
\TSRule{0.5\linewidth}{0.2pt}               % half-width rule
```

### `\TSTrack[amount]{text}`

Letter-spaced text via microtype `\textls`. Default tracking: 100 units
(1/1000 em). Use for uppercase labels and section heads.

```latex
\TSTrack{EXPERIENCE}                         % default tracking (100)
\TSTrack[60]{March 2026}                     % lighter tracking
```

### `\TSLabelFont`

A pre-configured font family (Medium weight, LetterSpace=4) for tracked
labels. Use when you need persistent tracking across a block rather than
wrapping each piece of text in `\TSTrack`.

## Quick Reference Card

```latex
% Scale
\TSMicro   % 7/12   labels
\TSBody    % 9/12   body text
\TSStep    % 12/12  subheads
\TSLarge   % 16/18  display
\TSTitle   % 21/24  titles

% Grid
\vspace{\TSGrid}    % 12pt
\vspace{\TSHalf}    % 6pt

% Colors
\color{TSText}      % #111111
\color{TSMuted}     % #5D5D5D
\color{TSRuleColor} % #C8C8C8
\color{TSStrong}    % #202020

% Weights
\TSLight       % light
\TSMedium      % medium
\TSSemiBold    % semibold
\TSBlack       % black
\TSLabelFont   % medium + tracking

% Primitives
\TSRule[color]{width}{weight}
\TSTrack[amount]{text}
```
