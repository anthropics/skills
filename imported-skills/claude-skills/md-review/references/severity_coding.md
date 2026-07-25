# Severity Coding

**Why this exists:** Code-review annotations need a severity dimension or every comment carries the same weight. This skill ships a default 4-tier convention (BLOCKER / MAJOR / MINOR / NIT), accepts custom conventions via `--severity-convention`, and enforces WCAG 1.4.1 (color is not the sole signal — every badge has color + icon + aria-label).

## The default convention

| Tier | Meaning | Source | Visual |
|---|---|---|---|
| **BLOCKER** | Must fix before merge. Author cannot proceed without addressing. | Found in many engineering teams' written conventions; Google calls this "must-fix" | Filled square ■ + derived danger color (accent rotated 120° toward red) |
| **MAJOR** | Strongly recommended. Author should address unless they have a good counter-argument. | Common in Google's *Code Review Developer Guide* as the "non-nit substantive comment" | Filled triangle ▲ + `--md-warn` |
| **MINOR** | Worth fixing. Reasonable to address now; reasonable to defer. | Common middle tier | Filled circle ● + `--md-link` |
| **NIT** | Cosmetic / style preference. Author may address or ignore. | Google's nit: prefix is the canonical example | Open circle ◦ + `--md-text-muted` |

Position 0 (BLOCKER) is most severe; position 3 (NIT) is least. Position determines the `severity_rank` field in the JSON output, which the renderer uses for sort + display order.

## Custom conventions

`--severity-convention "critical,important,suggestion,nit"` swaps the tier list. Same rank ordering applies (position 0 = most severe). Renderer uses the same icon/color mapping when the tier name matches a default; otherwise falls back to the `_text-muted` token + open-circle icon for the unknown tier.

## WCAG 1.4.1 — color is not the sole signal

Every severity badge ships:
1. **Color** — derived from the design-system palette, validated for AA contrast against bg.
2. **Icon** — ■ / ▲ / ● / ◦ — a glyph that's distinct shape-wise. (Deuteranopic readers see the shape difference even if the color difference is muted.)
3. **`aria-label`** — full text spelled out: "Blocker — must fix before merge". Screen readers announce this; sighted readers don't see it but get the icon + color + text.
4. **Text label** — the severity name itself ("BLOCKER") is in the badge. Triple-redundancy: color, icon, text.

A reader who is completely color-blind, or viewing on a grayscale monitor, or screen-reading the page, still has full access to severity.

## What we deliberately don't do

- **Emoji icons** — render inconsistently across OS / font (Windows vs macOS vs Linux vs iOS), break in monochrome printing. We use Unicode geometric shapes (■▲●◦) that ship with every system font.
- **Color-only badges** — the WCAG floor.
- **Severity arithmetic** — no "this PR has score X = blockers × 10 + majors × 3 + …" auto-rollup. Review quality is qualitative; numeric rollups create gaming incentives.
- **Auto-block merge based on severity** — that's a CI concern, not a renderer concern.

## Sources

### 1. WCAG 2.2 §1.4.1 *Use of Color* (w3.org/WAI/WCAG22)
The hard rule: color must not be the only visual means of conveying information. Our color + icon + label + aria-label is the canonical implementation.

### 2. Google *Code Review Developer Guide* (google.github.io/eng-practices/review/reviewer)
Source of the `nit:` prefix convention and the "blocker / major / minor / nit" taxonomy. We adopt it as the default.

### 3. *Software Engineering at Google* (Manshreck & Wright, O'Reilly 2020), Ch. 9
The taxonomy is documented here: blockers are tickets that fail review; nits are "I'd prefer X but it's not a blocker"; majors are substantive comments.

### 4. Phabricator / Sourcegraph / Reviewable.io
Each tool ships its own severity vocabulary; ours is compatible by adopting the most-common 4-tier convention.

### 5. Don Norman — *The Design of Everyday Things* (2013 ed., Basic Books)
The "signifier" concept: visual elements must communicate function. A red badge is a signifier; a red badge that says "BLOCKER" with a filled square is a stronger signifier; a red badge with `aria-label="Blocker — must fix before merge"` adds the non-visual channel.

### 6. NN/g — *Color in UX* (Therese Fessenden, 2024)
Empirical: relying on color alone fails for 8% of male readers (red-green color blindness). The triple-redundancy approach is standard.

### 7. Anil Dash — *The Web We Lost* (dashes.com, 2012)
Indirectly: portable web artifacts. A single-file review must render correctly even when CSS variables fail to load — which is why the badge text label (in addition to color + icon) is essential. If `var(--md-warn)` doesn't resolve, the user still sees "MAJOR" with a triangle.

## Applied to `md-review`

The `_render_severity_badge` helper in `review_html_renderer.py` emits the color + icon + label + aria-label combo for every severity, derived from the design-system palette. The convention is overridable via `--severity-convention`. Refuses to render a badge with color alone.
