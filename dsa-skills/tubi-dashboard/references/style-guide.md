# Tubi Dashboard Style Guide

The house style for HTML dashboards that mirror our Tableau look. Every value below is a CSS variable in `assets/tubi-theme.css` — use the variable, don't hard-code hex.

## Colors

### Brand
| Token | Hex | Use |
|---|---|---|
| `--tubi-purple` | `#6A1B9A` | Page/section titles, KPI numbers, table captions |
| `--tubi-purple-bright` | `#7408FB` | Links, active/focus accents, highlights |
| `--tubi-purple-deep` | `#4A1B8C` | Dark series, gradients, logo gradient end |
| `--tubi-yellow` | `#FCE300` | Logo and accent only — never for text or large fills |
| `--tubi-black` | `#14101E` | Near-black headings and the darkest chart series |

### Surfaces & neutrals
| Token | Hex | Use |
|---|---|---|
| `--bg` | `#FFFFFF` | Page and card background |
| `--bg-band` | `#F2F2F4` | Section-header strips |
| `--bg-filter` | `#ECEAF6` | Filter-bar strips (pale lavender) |
| `--bg-row-alt` | `#F7F7F9` | Zebra table rows |
| `--bg-hover` | `#F0EEF8` | Row / control hover |
| `--border` | `#E2E2E8` | Table rules, card borders |
| `--border-strong` | `#C9C9D2` | Totals rule, header underline, axis |
| `--text` | `#1F2430` | Body text |
| `--text-muted` | `#6B7280` | Labels, captions, axis text |

### Semantic (deltas & conditional formatting)
| Token | Hex | Use |
|---|---|---|
| `--pos` | `#1B873F` | Positive delta text (green) |
| `--neg` | `#D02B2B` | Negative delta text (red) |
| `--pos-bg` | `#C8E6C9` | Conditional in-cell green bar fill |
| `--neg-bg` | `#FBD5D5` | Conditional red fill (rare) |

## Series palette (ordered)

Assign in chart order; the meaning is project-specific, not fixed. Use them in sequence (`--series-1`, `--series-2`, …) so a dashboard with N series always pulls a consistent, distinguishable set.

| # | Hex | Typical use in our decks |
|---|---|---|
| 1 | `#4A90E2` blue | first category (e.g. Creator) |
| 2 | `#8C8C8C` gray | second category (e.g. Non-Priority) |
| 3 | `#A020E0` magenta | third category (e.g. Priority) |
| 4 | `#14101E` black | platform OTT / "Streaming" |
| 5 | `#FCE300` yellow | Web / "Other" |
| 6 | `#4A1B8C` deep purple | Cable |
| 7 | `#2EA39B` teal | overflow |
| 8 | `#E67E22` orange | overflow |

For **pie / share charts** we use the dark-to-light ramp seen on the Nielsen view: black → deep purple → magenta → yellow.

## Typography

- Font stack: `Inter, system-ui, -apple-system, "Segoe UI", Roboto, Helvetica, Arial, sans-serif`. Inter is pulled from Google Fonts with a system fallback if the network blocks it.
- Page title: 30px / 800 weight / `--tubi-purple`.
- Section band title: 17px / 700 / `--text`, centered.
- KPI number: 38px / 800 / `--tubi-purple`. KPI label: 14px / 600 / `--text-muted`.
- Body & tables: 14px. Captions/small: 12px.

## Required structure (every dashboard)

This top-to-bottom order is the fixed convention for all Tubi dashboards — keep it even as content changes:

1. **Header** — logo + title.
2. **Filter bar** — always at the top, directly under the header.
3. **KPI cards** — a row of summary metric cards. Always immediately below the filter bar, always before any chart or table — never bury the headline numbers below a chart.
4. **Data deep-dives** — charts and tables below, each introduced by a `.section-band`, ordered **from highest-level to most granular, top to bottom** (see "Detail progression" under Layout conventions). Every chart and table is a click-to-filter target by default (see "Cross-filtering" in components.md).

**The structure is fixed; the content is not.** Metric names, KPI values, chart types, series, and table columns all change per dashboard — the sample values in `template.html` (e.g. "6.9B Total Impressions", "Time to Tubi") are placeholders only. When building a new dashboard, keep the layout order and styling but replace every metric, label, and data point with the ones relevant to that dashboard. Never carry the sample numbers forward.

## Layout conventions

- Wrap everything in `.dash` (max-width 1320px, centered, 24px padding).
- Order top to bottom: **header → filter bar → KPI row → chart/table sections**, each major block introduced by a `.section-band`.
- Charts live in `.chart-card`s arranged in a `.chart-grid` (use `--2` or `--3` for fixed columns; default auto-fits). Small-multiples grids (like Top of Funnel) use `chart-grid--3`.
- Cards: white, 1px `--border`, 8px radius, subtle shadow, ~18px padding.

### Detail progression (within the deep-dive sections)

KPI cards at the top are the highest level of all — a single number per metric. Below them, order the deep-dive sections themselves from **highest-level down to most granular**, the same overview → detail logic applied a second time within the charts/tables area:

1. **Aggregate section first** — one chart summarizing the whole filtered dataset (e.g. total/median trend over time, or overall share). This should look and read like "the one chart you'd screenshot."
2. **Category breakdown next** — the same metric split by the primary dimension (partner, platform, content type), typically a bar/column, pie/doughnut, or stacked bar — one level more granular than the aggregate above.
3. **Record/line-item detail last** — the table or small-multiples grid a reader reaches for only after the first two sections raised a question ("why is Priority's number off — let me check the rows"). This is where precision beats visual punch.

A dashboard with one section is fine — the rule is about the *order* when there's more than one, not a mandate to always build three. If a request only calls for a single chart, put it right after the KPIs and skip the rest of the progression.

## Number & delta formatting

- Large counts: thousands separators (`35,245,075`). Money: `$` with `K`/`M`/`B` suffixes for KPI cards.
- **Currency and decimal measures always render to exactly 2 decimals** — everywhere: KPI values, chart axis ticks, and tooltips (`$412.48M`, `$1.23K`, `$43.90`, `4.33`). Use the `big()`/`money()`/`num2()` helpers from components.md so this is automatic; never hand-format. Counts (viewers, rows, IDs) stay whole numbers.
- Percentages: one decimal for deltas (`-4.6%`), two for precise share tables (`102.47%`).
- Delta cells: color the **text** green/red by sign with `.pos` / `.neg`. Don't add arrows unless asked.
- Tables: right-align numeric columns, left-align the first label column, bold the grand-total row (`tr.total`).
- Conditional bars: set `style="--bar: <pct>%"` where pct = value ÷ column max × 100, on the column you're ranking.

## Do / don't

- **Do** keep backgrounds white and let purple + the banded grays carry the brand.
- **Do** reuse the ordered series palette so colors stay consistent across tabs.
- **Don't** use yellow for text, KPI numbers, or large area fills — it's an accent.
- **Don't** introduce new chart colors outside the palette; extend `--series-7/8` instead.
- **Don't** mix multiple title colors; titles and KPIs are `--tubi-purple`.

## Design principles

Style makes a dashboard on-brand; these principles make it *effective*. Apply them to every dashboard, not just the styling. (Adapted from "Design KPI Dashboards That Steal the Show," N. Gadda.)

### 1. Design for the audience and the purpose

Before building, know who's reading and why. Decide up front whether the dashboard is for **decision-making** (needs comparisons, targets, drill-down) or **monitoring trends** (needs at-a-glance status and direction). Match the depth to the reader's data fluency and how they'll consume it (quick glance vs. deep analysis). When the purpose is unclear, ask.

### 2. Frame insights — don't just display numbers

A bare metric is a missed opportunity. Give numbers context so they answer a question, not just report a value.

- Instead of "Sales: 2M," show "Sales exceeded target by 15%" — pair the value with a comparison (vs. target, prior period, or benchmark).
- This is why KPI cards carry deltas (DoD/WoW/MoM/YoY) and tables carry % change: the comparison *is* the insight.
- Use section titles and captions to pose or answer the question the panel addresses (e.g. the `.section-band` subtitle), rather than restating the chart title.

### 3. Trigger curiosity — make shifts and outliers obvious

Design so a reader's eye lands on what changed and naturally asks "what's going on here?"

- Let color do this work: `.pos`/`.neg` on deltas, conditional in-cell bars to rank, a highlighted row for a selected item.
- Don't bury the signal in a uniform grid of numbers — surface the outlier.

### 4. Make interactivity purposeful

Filters, drill-downs, and tooltips are for *presenting* data, not just subsetting it.

- **Overview first, detail on demand:** lead with high-level KPIs and totals; let filters and a drill-down (like the streamer/partner selectors) take the reader deeper only when they want it — a breadcrumb trail, not a maze. This is also why deep-dive sections are ordered aggregate → category breakdown → record detail (see "Detail progression" above).
- **Every chart and table is a filter, by default — not an opt-in extra.** Clicking a bar, slice, point, bubble, treemap rect, or table row narrows the whole dashboard through the same `render()` pass the dropdowns use. See "Cross-filtering" in components.md; wire it in while building each chart, not as a pass at the end.
- **Make important data pop dynamically** as filters change instead of forcing users to hunt. This is why the shell recomputes KPIs, charts, and tables together on every filter or click-filter change.
- Use Chart.js **tooltips** to hold the precise numbers so the chart surface can stay clean.

### 5. Balance insight with clean visuals

- **Tell a story with hierarchy** — order sections top-to-bottom from headline to detail (KPIs → trends → breakdowns). The fixed structure already enforces this.
- **Declutter with confidence** — every element should earn its place. Remove chartjunk, redundant legends, and duplicate labels. White space is a feature, not wasted space.
- **Use the right visual for the job** — don't force a metric into the wrong chart because it looks nicer. See the Chart Selection Guide below for how to decide.

## Chart Selection Guide

Pick the chart type from the *shape* of the query result, not from taste. Before building, look at the columns you actually got back and ask which of these situations you're in. `scripts/build_dashboard.py --suggest-chart` will do this inspection for you and print a recommendation + reasoning — run it on the CSV before you start wiring up Chart.js, and treat its answer as a starting point to sanity-check, not a rule to follow blindly (it can't know the *question* behind the data, only its shape).

Every chart type below (and every table row) is a **click-to-filter target by default** — see "Cross-filtering" in components.md. Chart choice and cross-filter wiring aren't separate steps; pick the type from the table below, then wire its `onClick` the same way.

The full toolkit, grouped by the question it answers:

### Comparison and ranking

| Data shape | Chart | Why |
|---|---|---|
| One category column (any cardinality) + one numeric measure, ranking/comparing (not "sums to 100%") | **Bar / Column** (horizontal if labels are long or >6 categories; vertical/"column" if short labels and few categories) — see components.md | Bars make magnitude differences easy to compare directly — better than a pie for "who's biggest," better than a line with no time axis. |
| Same, but the reader also needs the exact numbers next to the rank | **Table with a conditional in-cell bar** | Gets the ranking visual *and* the precise value in one place — often better than a bar alone when precision matters as much as the visual. |
| A single measure against a target, with qualitative context (poor/satisfactory/good) | **Bullet graph** | Answers "is this pacing OK," not just "is it up or down" — richer than a KPI delta when there's a real target and a range to judge it against, without the overhead of a full gauge chart. |

### Trends over time

| Data shape | Chart | Why |
|---|---|---|
| A time/date column + one or more numeric measures | **Line** | Trend over time is the one question a line answers better than anything else. Multiple measures or a low-cardinality category column (≤6) → multi-series line, one line per series. |
| A time/date column + one volume/cumulative measure, where magnitude (not composition) is the point | **Area** | A filled single-series line reads as "how much" more strongly than a bare line — use for one measure, not a mix. |
| A time/date column + a category column with many values, tracking share of a total over time | **Stacked area** | Shows both the trend and the composition shift at once — use when "how is the mix changing" matters as much as "is it growing." |
| A time/date column + only 2-3 points | **KPI card**, not a chart | Two or three months isn't a trend yet — it's a before/after delta. Wait for enough points to show a shape. |
| Inside a KPI card, a compact trend alongside the headline number | **Sparkline** (see "Enhanced KPI card" in components.md) | A tiny axis-free trend line that frames the KPI without competing with it for attention — not a substitute for a full chart when the trend itself is the point. |

### Parts of a whole

| Data shape | Chart | Why |
|---|---|---|
| One category column (2-6 values) + one numeric measure that sums to ~100% or is explicitly a share/mix | **Pie / doughnut** | Only use when the values genuinely are parts of one whole and there are few enough slices to read at a glance. A pie with 10 slivers is a worse table. |
| Same, but with too many categories for a pie (>6) and still genuinely parts-of-a-whole (not a ranking) | **Treemap** | Keeps the whole-to-part relationship readable at higher cardinality than a pie can manage, without pretending it's a ranking (which should be a bar instead). Needs an extra CDN plugin — see components.md. |
| A category column crossed with another category column, composition within each outer category | **Stacked bar** | Shows the mix *within* each category side by side — better than several small pies when the reader needs to compare mixes across categories, not just view one. |

### Relationships and distributions

| Data shape | Chart | Why |
|---|---|---|
| Two numeric measures, no time or category column | **Scatter** | The question is "how do these two things relate," which only a scatter (or a correlation stat) actually answers. Don't force this into a bar or line. |
| Same, plus a third numeric measure that's meaningful to compare visually (size, spend, volume) | **Bubble** | Encodes a third dimension as radius without needing a color legend — only worth it if that third measure is actually part of the question. |
| One continuous numeric measure, no time/category — the question is about its spread | **Histogram** | Shows the distribution's shape (skew, outliers, clusters) that a single average or median would hide. Bin the data yourself; Chart.js has no native histogram type — see components.md. |

### Structural fallbacks (any category)

| Data shape | Chart | Why |
|---|---|---|
| A category column crossed with another category column, each combination with its own small trend or breakdown | **Small multiples** (`chart-grid--3` of compact charts, one per combination) | Comparing many segments at once works better as a grid of small identical charts than one overloaded chart with 12 legend entries. |
| A single current value, optionally with a prior-period value | **KPI card**, not a chart | If there's only one number (plus maybe a comparison), a chart is overkill — a KPI card with a `.delta` line *is* the visualization. |
| Anything you're unsure about, or a shape not listed above | **Table** | The safe default. A clean table with right-aligned numbers and a bold total row is never the wrong answer; a mis-chosen chart type usually is. |

A few things that trip people up:
- **Cardinality drives the pie-vs-bar-vs-treemap call more than anything else.** The same `category, value` shape is a pie at 4 categories, a treemap (if still genuinely parts-of-a-whole) at 8-12, and a bar or top-N + "Other" bucket beyond that. If the script's cardinality check flags "too many for a clean pie," don't default to treemap just to avoid a bar — check whether the question is really ranking (bar) before reaching for treemap.
- **A time column with only 2-3 points isn't really a trend yet.** Two months of data is a delta (KPI card), not a line or area chart — wait for enough points to show a shape.
- **"Category" and "time" can be the same-looking column.** A `month` column formatted as `"2026-01"` is a time dimension even though it looks like a string category — check whether the values are sequential/parseable as dates, not just whether the dtype is numeric.
- **Bullet graphs and histograms are the two chart types with the weakest cross-filter story.** A bullet is usually one fully-specified KPI already; a histogram bin ("0.58–0.62") isn't a normal filter value. It's fine for these two to skip `onClick` when there's no sensible target — see components.md for the exact call on each.

### Checklist before shipping

- Does each KPI carry a comparison, not just a value?
- Can a reader spot the biggest change in under five seconds?
- Does the layout go headline → detail, and within the deep-dives, aggregate → category → record-level?
- Does clicking a bar, slice, point, or table row actually filter the rest of the dashboard?
- Is every filter and element pulling its weight, or is it clutter?
- Is the right chart type used for each question?

## Accessibility

Dashboards should be readable by everyone, including colorblind users and screen-reader users.

### Color

- The **core 5 series** (blue, gray, magenta, black, yellow) are colorblind-safe: minimum perceptual distance stays above ΔE 32 under deuteranopia, protanopia, and tritanopia simulation. Use them for up to 5 series without worry.
- Beyond 5 series (`--series-6/7/8`), color alone is **not** reliable under color-vision deficiency — teal/gray and teal/blue can collide. When you need more than 5 series, don't lean on color: add point-marker shapes, direct labels on the lines, or split into small multiples.
- Never encode meaning by hue alone in a way a colorblind user would miss. Deltas already pair color with a sign (`+`/`−`); keep that pattern.
- Text/background contrast meets WCAG AA in both light and dark themes (`--text` on `--bg`).

### Screen readers

- Give each chart `<canvas>` a text alternative: `role="img"` and an `aria-label` summarizing the takeaway (not just the title). Example: `<canvas id="ttt" role="img" aria-label="Median time-to-Tubi by partner type, June 2025 to May 2026; Priority peaks at 60 days in October."></canvas>`.
- Provide the underlying numbers in an adjacent `.tbl` or a visually-hidden table so the data isn't locked inside the canvas. Use the `.sr-only` helper for hidden-but-readable content.
- Section bands use real `<h2>`s and the page a single `<h1>` — keep the heading order intact for navigation.
- Filter `<select>`s must keep their `<label>` (the shell already pairs `for`/`id`).
