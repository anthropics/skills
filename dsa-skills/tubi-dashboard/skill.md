# Tubi Dashboard

Build HTML dashboards that match Tubi's internal Tableau look: deep-purple titles and KPI numbers, banded gray section headers, pale-lavender filter bars, clean white cards, an ordered series palette, and red/green delta formatting. Charts use Chart.js (CDN).

## When to use

Use this skill for any request to build or restyle an HTML dashboard, analytics page, KPI summary, or report view that should look like our Tableau dashboards (CDP, Executive Summary, Accounting, Nielsen, etc.). Skip it for non-dashboard documents (use docx/pptx/xlsx skills) or for editing the actual Tableau workbooks.

## What's in here

- `assets/tubi-theme.css` — the theme: all brand colors, typography, spacing, and styles for cards, tables, section bands, filter bars, delta cells, and an 8-color ordered series palette. Includes a full **dark theme** under `[data-theme="dark"]`, tab-bar, enhanced-KPI, toolbar, and a print/PDF stylesheet. All values are CSS variables.
- `assets/template.html` — a complete, ready-to-fill page (header + logo, **functional filter bar**, KPI row, Chart.js line + pie, table). Filters embed row-level data and recompute everything on change.
- `references/components.md` — copy-paste snippets for every element plus Chart.js presets for the full chart toolkit (line, area, stacked area, bar/column, stacked bar, pie/doughnut, treemap, scatter, bubble, histogram, bullet graph). **Cross-filtering (click any chart or table row to filter the whole dashboard) is baseline, not opt-in** — every preset ships with its `onClick` wired. Ends with **advanced modules** (opt-in): tabs, enhanced KPI card w/ sparkline, dark-theme toggle, export-PNG, drill-down + URL state, small multiples, auto-caption.
- `references/style-guide.md` — hex codes, typography scale, series-color order, number/delta formatting, layout conventions, do/don'ts, and the **Design principles** (frame insights, trigger curiosity, purposeful interactivity, declutter) + pre-ship checklist.
- `scripts/build_dashboard.py` — turn a CSV / pandas DataFrame into the `#data` island (no hand-editing JSON); `auto_caption()` for framed KPI deltas; and `--suggest-chart` / `suggest_chart_type()`, which inspects a CSV's columns (time? category cardinality? two numeric measures?) and recommends a chart type per the Chart Selection Guide below — run it before wiring up Chart.js rather than guessing.
- `scripts/lint_dashboard.py` — check a finished dashboard against the guide (structure, palette, KPI comparisons, theme). Use it as the verify step.

## Workflow

1. **Know the audience, purpose, and starting point.** Before building anything, ask:

   **Are you building from scratch or replicating something that already exists?**
   - **From scratch** — the user describes what they want; you design the layout, pick charts, and build it. Proceed to step 2.
   - **Replicate an existing view** — the user has a dashboard, report, or visualization they want converted to HTML. They might provide:
     - A **Tableau URL** (e.g. `10ay.online.tableau.com/...`)
     - A **screenshot or PDF** of the view they want to clone
     - A **local file path** to an existing HTML dashboard or notebook output
     - A **deployed URL** to a web app or Teflon page
     - A **description** of a dashboard they've seen ("make it look like the CDP Avails dashboard")

   If replicating, follow the **source acquisition** ladder below to get the visual and data spec, then proceed:

   ### Source acquisition ladder (try in order)

   **a) Tableau MCP (best — try first for any Tableau URL).**
   If the user provides a Tableau URL, check whether Tableau MCP tools are available (`mcp__tableau__*`). If connected:
   - Use the MCP tools to pull the workbook metadata: view names/tabs, fields, filters, data sources, calculated fields, and if possible a rendered image of each view.
   - This gives you the layout, chart types, field names, and the underlying data model — enough to replicate without a screenshot.
   - If MCP can also export the underlying data (CSV/JSON), you can skip the "where is the data?" question entirely — you already have it.

   **b) Tableau MCP unavailable or failed.** If the MCP server isn't connected (check the session startup messages for a `tableau` connection error), tell the user:
   - The Tableau MCP connection isn't available this session.
   - Ask them to fix it and restart, OR fall through to option (c).

   **c) Screenshot / PDF / export image.** Ask the user to:
   - Take a screenshot (`Cmd+Shift+4` on Mac) of each Tableau tab, or
   - Export from Tableau: Dashboard → Download → Image/PDF, or
   - Provide the file path to an existing screenshot or PDF.
   - Read the image directly and catalog every element.

   **d) Fetch the URL directly (non-Tableau URLs).** For deployed HTML pages, Teflon dashboards, or public web apps:
   - Use `WebFetch` to pull the page content.
   - If it requires auth and fails, fall through to (c).

   **e) Description only.** The user names or describes a dashboard they've seen. Check if it's one you have context on from prior work (memory, local files). If not, ask enough questions to reconstruct the layout.

   ### Once you have the source

   1. **Study it.** Catalog every element: title, filters, KPI cards (values + labels + deltas), chart types and their series/axes, table columns and formatting, section headers, color usage, layout grid, tab names.
   2. **Map each element to the skill's components.** For each KPI → `.kpi-card`; each chart → the matching Chart.js preset from `references/components.md`; each table → `.tbl` with the right column alignment and conditional formatting; each filter → `.filter` with `data-field`. Note anything the source has that the skill doesn't cover — flag it to the user rather than silently dropping it.
   3. **Identify the data behind it.** The source dashboard pulls data from somewhere. Ask the user: do you know the query/table, or should I reverse-engineer the data shape from what's visible? If they know the query, use it. If not, infer the schema from the visible columns, metrics, and filters, and write a query that would produce that shape. If Tableau MCP gave you the data source and calculated fields, use those directly.
   4. **Then proceed to step 2** (data questions) with the source as your spec — the layout, charts, and metrics are already decided; you're just wiring them up in the Tubi HTML shell.

   Is this for decision-making (needs comparisons, targets, drill-down) or monitoring (at-a-glance status)? Who reads it and how? This shapes every later choice. See "Design principles" in `references/style-guide.md`. If unclear, ask.

2. **Ask about data before building.** Before writing any HTML, ask the user these questions (skip any they've already answered in their request):

   **a) Where is the data?**
   - **Databricks SQL** — the user has a query (or you'll write one). Most common for the team.
   - **CSV / file** — the user has a CSV, TSV, or JSON file already exported.
   - **REST API / URL** — the data lives at an endpoint that returns JSON.
   - **Manual / placeholder** — the user will fill in data later; build with sample data.

   **b) Static snapshot or live refresh?**
   - **Static** — run the query now, bake the results into the HTML as a JSON data island. Dashboard is self-contained, works offline, can be deployed to Teflon or shared as a file. Best for reports, snapshots, presentations.
   - **Live** — the dashboard fetches fresh data on every page load (or on a refresh button click). Requires the data source to be reachable from the browser or a proxy. Best for monitoring dashboards that need to stay current.

   **c) How big is the dataset?**
   - **Small** (< 5K rows) — embed directly in the data island or fetch in full.
   - **Medium** (5K–50K rows) — pre-aggregate to the grain the charts need before embedding. Ask what grain the charts actually require (daily? monthly? by-partner?).
   - **Large** (> 50K rows) — must pre-aggregate. Consider whether the dashboard should run the aggregation query itself (live mode) or receive pre-rolled data.

   **d) Should charts show their SQL?**
   - If the audience is technical (analysts, data scientists), default to **yes** — include the "Show SQL" toggle on each chart so readers can verify or reuse the queries. See "Show SQL" in `references/components.md`.
   - If the audience is non-technical (execs, ops), default to **no** — skip the SQL buttons to reduce clutter.

   Use the answers to pick the right data loading pattern from `references/components.md` → "Data loading patterns."

3. **Start from the template.** Copy `assets/template.html` and `assets/tubi-theme.css` into the output folder. For a single self-contained file, paste the CSS inline inside a `<style>` tag instead of linking it. The template's metrics, charts, and tables are placeholders — keep the structure, replace all content with the new dashboard's actual metrics and data. Wire up the data loading pattern chosen in step 2.
4. **Read the style guide** (`references/style-guide.md`) — both the visual rules (colors, formatting) and the **Design principles** section. Frame every KPI with a comparison, surface outliers, lead overview → detail, and use the right chart for each question.
5. **Assemble the page** in this order: header → filter bar → KPI row → section-banded chart/table blocks. KPI cards always sit directly under the filter bar, before any chart. Order the chart/table sections themselves from highest-level to most granular top to bottom — one aggregate summary chart first, then a category breakdown, then record-level tables or small multiples last (see "Detail progression" in `references/style-guide.md`). Pull element markup from `references/components.md`. Keep filters functional and purposeful — overview first, drill-down on demand: put row-level data in the `#data` island, tag each categorical `<select>` with `data-field`, and let `render()` recompute on change. **Every chart and table row is also a click-to-filter target by default** — wire each chart's `onClick` (and each table row's `onclick`) to `toggleClickFilter()` as you build it, not as a separate pass; see "Cross-filtering" in `references/components.md`. Only make filters (and click-filtering) static/skipped if the user explicitly wants a non-interactive mockup.
6. **Pick the chart type from the data's shape, not from taste, then wire it up with Chart.js** from the CDN (`https://cdnjs.cloudflare.com/ajax/libs/Chart.js/4.4.1/chart.umd.min.js`). Before assuming a chart type, run `python scripts/build_dashboard.py <data.csv> --suggest-chart` (or call `suggest_chart_type(df)` on a DataFrame) — it checks for a time column, category cardinality, and how many numeric measures there are, and recommends line / stacked area / bar / pie / scatter / small multiples / table / KPI card accordingly, with a one-line reason. The full decision table (and the reasoning behind each call, e.g. why a 10-category breakdown should be a bar chart or table instead of a pie) is the **Chart Selection Guide** in `references/style-guide.md` — read it if the suggestion seems off, since the script knows the data's shape but not the question the dashboard is answering. Paste the Chart.js defaults block from components.md so charts read theme colors; assign series colors in order (`--series-1`, `-2`, …). Put precise numbers in tooltips to keep the surface clean.
7. **Format data** per the guide: thousands separators, `$`/`M`/`B` for KPIs, `.pos`/`.neg` classes for delta cells, `--bar` percent for conditional in-cell bars, bold `tr.total` rows. Every KPI should carry a comparison (delta / target / prior period), not just a value.
8. **Verify** — run `python scripts/lint_dashboard.py <file>.html` (checks structure, palette, KPI comparisons, theme), confirm it renders (Chart.js loads, theme applies, no console errors), **and** run the design checklist in the style guide: does each KPI show a comparison, can the biggest change be spotted in seconds, does layout flow headline → detail, is anything clutter, is the right chart used?

## Conventions (quick reference)

- **Ask "from scratch or replicate?" first:** if the user has an existing dashboard (Tableau view, screenshot, HTML page, notebook), clone its layout and metrics into the Tubi HTML shell. If from scratch, design the layout from their requirements. Either way, then ask the data questions.
- **Ask about data next:** where does it come from (Databricks, CSV, API, placeholder), static or live, and how big. Pick the matching data loading pattern from `references/components.md`. Don't assume static JSON — ask.
- **Fixed structure, variable content:** every dashboard is header → filter bar → KPI cards → data deep-dives. That order never changes; the metrics, charts, and tables always do.
- **KPI cards are always the first thing after the filter bar** — never below a chart.
- **Deep-dive sections run highest-level to most granular, top to bottom:** aggregate summary → category breakdown → record/line-item detail.
- **Every chart and table is a filter by default:** clicking a bar, slice, point, or row filters the whole dashboard via `toggleClickFilter()` (see components.md's Cross-filtering section) — this is baseline, not an add-on to remember later.
- **Show SQL for technical audiences:** include the SQL toggle on each chart/table so analysts can verify or reuse queries. Skip for exec/ops dashboards. See "Show SQL" in components.md.
- **Dark mode and toolbar:** include the dark/light toggle and export-PNG button in the header toolbar by default. See "Dark theme toggle" and "Export chart to PNG" in components.md.
- Titles & KPI numbers: `--tubi-purple` (`#6A1B9A`). Yellow is accent/logo only.
- Section headers: centered title on a `.section-band` (gray strip). Filters in a `.filter-bar` (lavender), functional by default via `data-field` + `render()`.
- Series palette is ordered, not semantic — reuse the sequence so colors stay consistent across tabs.
- Deltas: green up / red down via `.pos` / `.neg`, colored text only.
- Wrap the page in `.dash`; charts in `.chart-card` inside a `.chart-grid`.
- **Frame, don't just display:** pair every metric with a comparison; make the biggest change obvious; lead overview → detail; declutter; use the right chart for each question. Full rationale in the style guide's "Design principles."

Keep dashboards to the elements that exist in the theme; if a new chart color is needed, extend `--series-7/8` rather than inventing one.
