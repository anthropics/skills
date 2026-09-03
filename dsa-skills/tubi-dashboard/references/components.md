# Component Snippets

Copy-paste blocks. All assume `tubi-theme.css` is loaded and (for charts) Chart.js is on the page. Replace sample content with real data.

---

## Header with logo

```html
<header class="dash-header">
  <span class="dash-logo">tubi</span>
  <h1 class="dash-title">VOD Accounting Dashboard</h1>
</header>
```

Centered title variant (no logo, title fills width):

```html
<header class="dash-header">
  <h1 class="dash-title dash-title--center">Executive Summary</h1>
</header>
```

---

## Filter bar (functional)

Filters in the shell are **functional by default** — they recompute the whole dashboard on change. Each categorical `<select>` declares the data column it filters via `data-field`; options auto-populate from the data and changes call `render()`.

```html
<section class="filter-bar">
  <div class="filter">
    <label for="f_time">Time Period</label>
    <select id="f_time" data-field="__time">
      <option value="all">All time</option>
      <option value="12">Last 12 months</option>
      <option value="6">Last 6 months</option>
      <option value="3">Last 3 months</option>
    </select>
  </div>
  <div class="filter">
    <label for="f_country">Country</label>
    <select id="f_country" data-field="country"><option>(All)</option></select>
  </div>
</section>
```

- Add a filter by copying a `.filter` block and setting `data-field` to a column name in your data.
- `data-field="__time"` is the special time-window filter (handled separately in `render()`); leave it as-is.
- Don't hand-write the category options — the wiring fills them from the data.

### Wiring (in your `<script>`)

```js
// auto-populate every categorical filter and re-render on change
document.querySelectorAll('select[data-field]').forEach(sel=>{
  const f = sel.dataset.field;
  if (f.startsWith('__')) return;            // skip special filters like __time
  [...new Set(RAW.map(r=>r[f]))].sort().forEach(val => sel.add(new Option(val,val)));
  sel.addEventListener('change', render);
});

// inside render(): keep rows that match every active categorical filter
let rows = RAW.filter(r =>
  [...document.querySelectorAll('select[data-field]')].every(sel=>{
    const f = sel.dataset.field;
    if (f.startsWith('__')) return true;
    return sel.value==='(All)' || String(r[f])===sel.value;
  })
);
```

See `assets/template.html` for the full working pattern (data island + `render()` that rebuilds KPIs, charts, and tables). For a static/display-only mockup, just drop the `data-field` attributes and the script.

---

## Section header band

```html
<div class="section-band"><h2>Current Video Counts by Stage &amp; Priority</h2></div>
```

With an italic caption underneath (like the L28 note):

```html
<div class="section-band">
  <h2>L28 Durations</h2>
  <span class="subtitle">Data shown for L28 of each stage.</span>
</div>
```

---

## KPI card row

```html
<section class="kpi-row">
  <div class="kpi-card"><div class="value">6.5B</div><div class="label">Total Impressions</div></div>
  <div class="kpi-card"><div class="value">$5.70</div><div class="label">Average eCPM</div></div>
  <div class="kpi-card">
    <div class="value">$37.1M</div>
    <div class="label">Estimated Revenue</div>
    <div class="delta pos">+2.1% MoM</div>   <!-- optional delta line -->
  </div>
</section>
```

Cards auto-fit; 4–5 across on desktop, wrapping on mobile.

---

## Delta table (DoD / WoW / MoM / YoY)

```html
<table class="tbl">
  <thead>
    <tr><th>Metric</th><th>Value</th><th>DoD</th><th>WoW</th><th>MoM</th><th>YoY</th></tr>
  </thead>
  <tbody>
    <tr>
      <td>DAU</td><td>13,831,197</td>
      <td class="pos">0.1%</td><td class="neg">-4.5%</td>
      <td class="pos">2.1%</td><td class="pos">12.8%</td>
    </tr>
  </tbody>
</table>
```

Rule: positive change → `class="pos"` (green), negative → `class="neg"` (red). Apply per cell.

---

## Table with grand-total row + conditional bar

Rows are filters too, by default — give each row a `data-*` attribute matching a real field and an `onclick` that calls `toggleClickFilter` (see Cross-filtering above). Skip this on the `tr.total` row; a grand total isn't a filterable category.

```html
<table class="tbl">
  <thead><tr><th>Partner Type</th><th>MTD</th><th>LMTD</th><th>% Change</th></tr></thead>
  <tbody>
    <tr data-partner="Creator" onclick="toggleClickFilter('partner', this.dataset.partner)">
      <td>Creator</td><td class="cell-bar" style="--bar:32%">1,161</td><td>606</td><td class="pos">91.58%</td></tr>
    <tr class="total"><td>Grand Total</td><td>3,612</td><td>1,784</td><td class="pos">102.47%</td></tr>
  </tbody>
</table>
```

`--bar` is the fill width as a percent of the cell — compute `value / columnMax * 100`. Use on the column you want to visually rank (Tableau-style in-cell bar).

---

## Chart container

```html
<div class="chart-card">
  <h3>DAU by Platform Type</h3>
  <div class="chart-box"><canvas id="dauChart"></canvas></div>
</div>
```

Grid of charts (2 or 3 wide):

```html
<div class="chart-grid chart-grid--3">
  <div class="chart-card">…</div>
  <div class="chart-card">…</div>
  <div class="chart-card">…</div>
</div>
```

---

## Cross-filtering (default — every chart and table)

**Not opt-in.** Every chart, and every table row, is a filter on the whole dashboard by default: clicking a bar, slice, point, or row narrows every KPI, chart, and table through the same `render()` pass the dropdown filters already trigger. Wire this in from the start — it's part of the base shell now, not an advanced add-on.

Two filter mechanisms feed the same `render()`:
- `select[data-field]` dropdowns (see the filter-bar wiring above).
- `CLICK_FILTERS` — an ad-hoc filter set by clicking a chart element, for fields that don't have their own dropdown (e.g. one specific month off a trend line, or a category that's only ever shown inside a chart).

```js
// Ad-hoc filters set by clicking a chart element. Independent of the <select>
// filters so any chart can filter on any field, even one without its own dropdown.
const CLICK_FILTERS = {};

function toggleClickFilter(field, value){
  if (CLICK_FILTERS[field] === value) delete CLICK_FILTERS[field];   // click again to clear
  else CLICK_FILTERS[field] = value;
  render();
}
function clearClickFilters(){ for (const k in CLICK_FILTERS) delete CLICK_FILTERS[k]; render(); }

function esc(s){ return String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;').replace(/'/g,'&#39;'); }
function renderChips(){
  const entries = Object.entries(CLICK_FILTERS);
  filterChips.hidden = entries.length === 0;
  filterChips.innerHTML = entries.map(([f, val]) =>
    `<span class="chip">${esc(f)}: <b>${esc(val)}</b><button aria-label="Clear ${esc(f)} filter" onclick="toggleClickFilter('${esc(f)}','${esc(val)}')">×</button></span>`
  ).join('') + (entries.length > 1 ? `<button class="chip chip--clear" onclick="clearClickFilters()">Clear all</button>` : '');
}
```

```html
<!-- place directly under the filter bar, above the KPI row -->
<div class="filter-chips" id="filterChips" hidden></div>
```

Inside `render()`: apply `CLICK_FILTERS` the same way the `<select>` filters are applied, and call `renderChips()` once at the end so the active click-filters stay visible and clearable:

```js
let rows = RAW.filter(r =>
  [...document.querySelectorAll('select[data-field]')].every(sel => { /* existing dropdown check */ })
  && Object.entries(CLICK_FILTERS).every(([f, val]) => String(r[f]) === String(val))
);
// ...build KPIs/charts/tables from rows as usual...
renderChips();   // last line of render()
```

Every chart preset below wires its `onClick` to `toggleClickFilter`; table rows get `onclick="toggleClickFilter('partner', this.dataset.partner)"` with a matching `data-partner="…"` attribute on the `<tr>`. If a chart genuinely has no categorical dimension (e.g. one aggregate line with a single series and no per-point identity), wire the click to the closest meaningful field anyway — clicking a point on an aggregate trend line can filter to that single time period. "All charts are filters" means all of them, not just the convenient ones.

---

**Before picking which of the presets below to use**, check the Chart Selection Guide in `style-guide.md` — it maps data shape (time column? category cardinality? two numeric measures?) to chart type. `scripts/build_dashboard.py --suggest-chart data.csv` runs that same check programmatically and prints a recommendation if you'd rather not eyeball it.

## Chart.js setup (paste once, before your charts)

```js
const css = getComputedStyle(document.documentElement);
const v = (n) => css.getPropertyValue(n).trim();
const SERIES = [v('--series-1'),v('--series-2'),v('--series-3'),v('--series-4'),
                v('--series-5'),v('--series-6'),v('--series-7'),v('--series-8')];

Chart.defaults.font.family = v('--font');
Chart.defaults.color = v('--text-muted');
Chart.defaults.plugins.legend.position = 'bottom';
```

### Number formatting helpers (always paste these)

Currency and decimals must render to **2 decimals** everywhere — KPI values, chart axis ticks, and tooltips. Use these helpers so you never hand-format:

```js
const fmt   = n => (n==null ? '—' : n.toLocaleString('en-US'));   // integer counts
const big   = n => { n=Number(n)||0; const a=Math.abs(n);
  if (a>=1e9) return (n/1e9).toFixed(2)+'B';
  if (a>=1e6) return (n/1e6).toFixed(2)+'M';
  if (a>=1e3) return (n/1e3).toFixed(2)+'K';
  return n.toFixed(2); };                                         // 2-decimal, K/M/B suffix
const money = n => (n==null ? '—' : '$'+big(n));                  // dollars, 2 decimals
const num2  = n => (n==null ? '—' : Number(n).toFixed(2));        // plain 2-decimal
const pct   = (n,d=1) => (n==null ? '—' : Number(n).toFixed(d)+'%');
```

Wire them into chart axes/tooltips too, so charts match the cards:

```js
scales: { y: { ticks: { callback: money } } },                   // or big for counts/hours
plugins: { tooltip: { callbacks: { label: c => 'Revenue: ' + money(c.raw) } } }
```

Counts (viewers, rows, IDs) stay whole numbers via `fmt`; only currency and decimal measures use `money`/`num2`.

### Line (multi-series)

```js
const dauChart = new Chart(document.getElementById('dauChart'), {
  type: 'line',
  data: { labels: [...], datasets: [
    { label: 'Creator',  data: [...], borderColor: SERIES[0], backgroundColor: SERIES[0], borderWidth: 3, tension: .25, pointRadius: 3 },
    { label: 'Priority', data: [...], borderColor: SERIES[2], backgroundColor: SERIES[2], borderWidth: 3, tension: .25, pointRadius: 3 }
  ]},
  options: { responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {   // click a series -> cross-filter the whole dash to it
      if (!els.length) return;
      toggleClickFilter('partner', dauChart.data.datasets[els[0].datasetIndex].label);
    },
    scales: { y: { beginAtZero: true, grid: { color: v('--border') } }, x: { grid: { display: false } } } }
});
```

A single-series (aggregate, no category) line can still be a filter — click a point to filter to that one time period instead of a category: `toggleClickFilter('month', dauChart.data.labels[els[0].index])`.

### Pie / doughnut

```js
const shareChart = new Chart(ctx, { type: 'doughnut',
  data: { labels: ['Streaming','Cable','Broadcast','Other'],
    datasets: [{ data: [42.46,22.77,20.53,14.24],
      backgroundColor: [v('--tubi-black'), v('--tubi-purple-deep'), v('--series-3'), v('--series-5')],
      borderColor: v('--bg'), borderWidth: 2 }] },
  options: { responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {   // click a slice -> cross-filter the whole dash to it
      if (!els.length) return;
      toggleClickFilter('platform', shareChart.data.labels[els[0].index]);
    } } });
```

### Stacked area (market-share style)

```js
const shareTrendChart = new Chart(ctx, { type: 'line',
  data: { labels: [...], datasets: [
    { label: 'Streaming', data: [...], borderColor: v('--tubi-black'),        backgroundColor: v('--tubi-black')+'30',        fill: true },
    { label: 'Cable',     data: [...], borderColor: v('--tubi-purple-deep'),  backgroundColor: v('--tubi-purple-deep')+'30',  fill: true }
  ]},
  options: { responsive: true, maintainAspectRatio: false, elements: { point: { radius: 0 } },
    onClick: (e, els) => {   // click a band -> cross-filter to that series
      if (!els.length) return;
      toggleClickFilter('platform', shareTrendChart.data.datasets[els[0].datasetIndex].label);
    },
    scales: { y: { stacked: false, ticks: { callback: x => x + '%' } } } } });
```

### Area (single series — volume/cumulative trend, not composition)

Use when there's one measure over time and the visual weight of "how much" matters more than a bare line (e.g. total impressions, cumulative spend). If you're tracking more than one series' *share* of a total, use Stacked area above instead — that's a composition question, this is a volume-over-time question.

```js
const volumeChart = new Chart(ctx, { type: 'line',
  data: { labels: [...], datasets: [{ label: 'Impressions', data: [...],
    borderColor: v('--series-1'), backgroundColor: v('--series-1')+'30', borderWidth: 2, fill: true, tension: .2 }] },
  options: { responsive: true, maintainAspectRatio: false,
    plugins: { legend: { display: false } },
    onClick: (e, els) => {   // click a point -> filter to that time period
      if (!els.length) return;
      toggleClickFilter('month', volumeChart.data.labels[els[0].index]);
    },
    scales: { y: { beginAtZero: true, ticks: { callback: big }, grid: { color: v('--border') } }, x: { grid: { display: false } } } } });
```

### Bar / Column (ranked comparison — no time axis)

Use when the question is "who's biggest," not "how has this changed." See the Chart Selection Guide in style-guide.md for when this beats a pie or a table. **"Column chart" is the same chart, just vertical** (`indexAxis: 'x'`, the Chart.js default) — use vertical/column for short labels and ≤6 categories, horizontal for long labels or more categories.

```js
const rankChart = new Chart(ctx, { type: 'bar',
  data: { labels: ['Roku','Amazon','Samsung','Android TV','Vizio'],
    datasets: [{ data: [42.8, 21.9, 8.0, 7.8, 7.4], backgroundColor: v('--series-1'), borderRadius: 3 }] },
  options: { indexAxis: 'y',              // horizontal — swap to default (vertical/"column") if labels are short and there are <=6 categories
    responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {   // click a bar -> cross-filter the whole dash to that category
      if (!els.length) return;
      toggleClickFilter('platform', rankChart.data.labels[els[0].index]);
    },
    plugins: { legend: { display: false }, tooltip: { callbacks: { label: c => pct(c.raw) } } },
    scales: { x: { beginAtZero: true, ticks: { callback: x => x + '%' }, grid: { color: v('--border') } },
              y: { grid: { display: false } } } } });
```

For a **grouped bar** (multiple series per category, e.g. this month vs last month per platform), add more entries to `datasets` the same way the multi-series line example does, and drop `indexAxis: 'y'` unless labels are long.

### Stacked bar (composition across categories — not over time)

Use for "how does the mix differ by category" when the x-axis is categorical, not time (time + composition is Stacked area above). E.g. content-type mix per partner type.

```js
const mixChart = new Chart(ctx, { type: 'bar',
  data: { labels: ['Creator','Non-Priority','Priority'],
    datasets: [
      { label: 'Movie',   data: [58, 41, 62], backgroundColor: v('--series-1') },
      { label: 'Episode', data: [42, 59, 38], backgroundColor: v('--series-2') }
    ] },
  options: { responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {   // click a segment -> filter to that category + that segment's series
      if (!els.length) return;
      toggleClickFilter('partner', mixChart.data.labels[els[0].index]);
    },
    scales: { x: { stacked: true, grid: { display: false } },
              y: { stacked: true, beginAtZero: true, ticks: { callback: x => x + '%' }, grid: { color: v('--border') } } } } });
```

### Scatter (relationship between two measures)

Use only when there's no time or category dimension and the actual question is "how do these two numbers relate" — a scatter answers that; a bar or line forced onto the same data won't.

```js
const scatterChart = new Chart(ctx, { type: 'scatter',
  data: { datasets: [{ label: 'Line items',
    data: [{x: 12.40, y: 0.62, name: 'LI-4821'}, {x: 27.44, y: 0.71, name: 'LI-9903'}, {x: 16.22, y: 0.58, name: 'LI-1187'}],  // {x: cpm, y: completion_rate}
    backgroundColor: v('--series-1') }] },
  options: { responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {   // filter target only makes sense if each point carries an identity (name/id) — skip onClick if points are anonymous
      if (!els.length) return;
      const pt = scatterChart.data.datasets[els[0].datasetIndex].data[els[0].index];
      if (pt.name) toggleClickFilter('line_item', pt.name);
    },
    plugins: { tooltip: { callbacks: { label: c => `CPM $${c.raw.x.toFixed(2)}, completion ${(c.raw.y*100).toFixed(1)}%` } } },
    scales: { x: { title: { display: true, text: 'CPM ($)' }, grid: { color: v('--border') } },
              y: { title: { display: true, text: 'Completion rate' }, grid: { color: v('--border') } } } } });
```

### Bubble (relationship between two measures + a third as size)

Use when a third numeric measure (deal size, spend, audience) matters alongside the x/y relationship — the radius carries that third dimension without needing a color legend. Don't use if the third measure isn't meaningful to compare visually; a plain scatter is cleaner.

```js
const bubbleChart = new Chart(ctx, { type: 'bubble',
  data: { datasets: [{ label: 'Campaigns',
    data: [{x: 12.40, y: 0.62, r: 8, name: 'FNAF2'}, {x: 27.44, y: 0.71, r: 18, name: 'Apartments 3Q'}, {x: 16.22, y: 0.58, r: 12, name: 'Oak Street'}],
    // r is in pixels, not data units — normalize your third measure into a reasonable px range (e.g. 6-24) before charting
    backgroundColor: v('--series-1')+'80', borderColor: v('--series-1') }] },
  options: { responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {
      if (!els.length) return;
      const pt = bubbleChart.data.datasets[els[0].datasetIndex].data[els[0].index];
      if (pt.name) toggleClickFilter('campaign', pt.name);
    },
    plugins: { tooltip: { callbacks: { label: c => `${c.raw.name}: CPM $${c.raw.x.toFixed(2)}, completion ${(c.raw.y*100).toFixed(1)}%, spend ${money(c.raw.spend)}` } } },
    scales: { x: { title: { display: true, text: 'CPM ($)' }, grid: { color: v('--border') } },
              y: { title: { display: true, text: 'Completion rate' }, grid: { color: v('--border') } } } } });
```

### Histogram (distribution of one continuous measure)

Chart.js has no native histogram type — bin the data yourself, then render the bins as a bar chart with no gaps between bars. Use when the question is "what does the spread of this one measure look like," not a ranking or a trend.

```js
function toBins(values, binCount = 10){
  const v = values.filter(x => x != null);
  const min = Math.min(...v), max = Math.max(...v);
  const width = (max - min) / binCount || 1;
  const counts = new Array(binCount).fill(0);
  v.forEach(x => { const i = Math.min(binCount - 1, Math.floor((x - min) / width)); counts[i]++; });
  const labels = counts.map((_, i) => `${(min + i * width).toFixed(1)}–${(min + (i + 1) * width).toFixed(1)}`);
  return { labels, counts, min, width };
}

const { labels, counts } = toBins(rows.map(r => r.completion_rate));
const histChart = new Chart(ctx, { type: 'bar',
  data: { labels, datasets: [{ data: counts, backgroundColor: v('--series-1') }] },
  options: { responsive: true, maintainAspectRatio: false,
    plugins: { legend: { display: false } },
    // clicking a bin narrows to that value range rather than a single category — most dashboards
    // skip a click-filter here since "between 0.58 and 0.62" isn't a normal filter value; if you
    // need it, store {min,max} in CLICK_FILTERS and change the row filter to a range check for that field.
    scales: { x: { grid: { display: false }, categoryPercentage: 1.0, barPercentage: 1.0 },
              y: { beginAtZero: true, title: { display: true, text: 'Count' }, grid: { color: v('--border') } } } } });
```

### Bullet graph (measure vs. target, with a qualitative range)

No native Chart.js type — build it from a horizontal bar chart: a wide background bar for the qualitative bands (poor/satisfactory/good), a thin bar overlaid for the actual value, and a plugin-drawn tick for the target. Use for KPI-vs-goal questions where a plain KPI card's delta isn't enough context (e.g. "is this pacing OK, not just up or down").

```js
// one bullet per row: { label, value, target, bands: [poorMax, satisfactoryMax, goodMax] }
const bullets = [{ label: 'eCPM', value: 5.70, target: 6.00, bands: [4, 6, 8] }];

const targetTickPlugin = {
  id: 'targetTick',
  afterDatasetsDraw(chart){
    const { ctx, scales: { x, y } } = chart;
    bullets.forEach((b, i) => {
      const xPix = x.getPixelForValue(b.target);
      const yCenter = y.getPixelForValue(i);
      const half = y.getPixelForValue(i) - (chart.getDatasetMeta(0).data[i]?.height ?? 20) / 2;
      ctx.save(); ctx.strokeStyle = v('--tubi-black'); ctx.lineWidth = 3;
      ctx.beginPath(); ctx.moveTo(xPix, yCenter - 10); ctx.lineTo(xPix, yCenter + 10); ctx.stroke();
      ctx.restore();
    });
  }
};

const bulletChart = new Chart(ctx, { type: 'bar',
  data: { labels: bullets.map(b => b.label),
    datasets: [
      { label: 'Poor',         data: bullets.map(b => b.bands[0]),                     backgroundColor: v('--border-strong') },
      { label: 'Satisfactory', data: bullets.map(b => b.bands[1] - b.bands[0]),        backgroundColor: v('--border') },
      { label: 'Good',         data: bullets.map(b => b.bands[2] - b.bands[1]),        backgroundColor: v('--bg-band') },
      { label: 'Actual',       data: bullets.map(b => b.value), backgroundColor: v('--tubi-purple'), barThickness: 10 }
    ] },
  options: { indexAxis: 'y', responsive: true, maintainAspectRatio: false,
    plugins: { legend: { display: false }, tooltip: { callbacks: { label: c => c.dataset.label === 'Actual' ? `Actual: ${money(c.raw)}` : undefined } } },
    scales: { x: { stacked: false, beginAtZero: true, grid: { color: v('--border') } }, y: { stacked: true, grid: { display: false } } } },
  plugins: [targetTickPlugin] });
```

Cross-filtering doesn't apply the same way to a bullet graph (one bullet is usually already a fully-specified KPI, not a category to drill into) — skip `onClick` here unless you have several bullets ranked by the same dimension, in which case treat it like the Bar preset.

### Treemap (hierarchical parts-of-a-whole)

Chart.js has no built-in treemap; use it only when a pie/doughnut has too many slices to read (>6) but the data is still genuinely parts-of-a-whole, not a ranking (which should just be a bar). This needs one extra CDN script beyond Chart.js — only add it on dashboards that actually use a treemap, to keep the rest lean:

```html
<script src="https://cdn.jsdelivr.net/npm/chartjs-chart-treemap@2/dist/chartjs-chart-treemap.min.js"></script>
```

```js
const treemapChart = new Chart(ctx, { type: 'treemap',
  data: { datasets: [{ tree: [
      { name: 'Movie', value: 4200 }, { name: 'Episode', value: 3100 },
      { name: 'Clip', value: 900 }, { name: 'Other', value: 400 }
    ], key: 'value',
    backgroundColor: (c) => SERIES[c.dataIndex % SERIES.length],
    labels: { display: true, color: v('--bg'), font: { weight: '700' } } }] },
  options: { responsive: true, maintainAspectRatio: false,
    onClick: (e, els) => {   // click a rect -> cross-filter to that category
      if (!els.length) return;
      const item = treemapChart.data.datasets[0].tree[els[0].index];
      toggleClickFilter('content', item.name);
    },
    plugins: { legend: { display: false } } } });
```

---

## Manual legend (when you hide Chart.js's)

```html
<div class="legend">
  <span><i style="background:var(--series-1)"></i>Creator</span>
  <span><i style="background:var(--series-2)"></i>Non-Priority</span>
  <span><i style="background:var(--series-3)"></i>Priority</span>
</div>
```

---

# Data loading patterns

The template's `#data` island is the simplest pattern (static JSON baked in), but dashboards can load data from any source. Pick the pattern that matches what the user asked for in the workflow's "Ask about data" step. All patterns end the same way: `RAW` is an array of row objects, and `render()` takes over from there.

## Pattern 1: Static JSON island (default)

Data is embedded in the HTML at build time. Self-contained, works offline, deployable to Teflon.

**When to use:** snapshots, reports, presentations, or when the user ran a query and wants to freeze the result.

**How to build it:** Run the SQL via `run_query.py` (or whatever query runner the user has), get CSV/JSON back, and embed it in the `#data` script tag. For CSV, use `scripts/build_dashboard.py data.csv` to generate the island.

```html
<script id="data" type="application/json">
[{"partner":"Creator","month":"2025-07","value":16}, ...]
</script>
<script>
const RAW = JSON.parse(document.getElementById('data').textContent);
</script>
```

## Pattern 2: CSV file (drag-and-drop or URL)

Dashboard loads a CSV at runtime. Good for dashboards that read from an exported file or a shared CSV URL.

Requires Papa Parse from CDN:

```html
<script src="https://cdnjs.cloudflare.com/ajax/libs/PapaParse/5.4.1/papaparse.min.js"></script>
```

### 2a: Fetch from URL

```js
const DATA_SOURCE = { type: 'csv', url: './data.csv' };

async function loadData(){
  const resp = await fetch(DATA_SOURCE.url);
  const text = await resp.text();
  const { data } = Papa.parse(text, { header: true, dynamicTyping: true, skipEmptyLines: true });
  return data;
}
loadData().then(data => { RAW = data; initFilters(); render(); });
```

### 2b: Drag-and-drop file loader

```html
<div id="dropZone" class="filter-bar" style="text-align:center;cursor:pointer;padding:24px">
  Drop a CSV here or <label style="color:var(--tubi-purple-bright);cursor:pointer">
  click to upload<input type="file" accept=".csv,.tsv" hidden id="fileInput"></label>
</div>
```

```js
let RAW = [];
function handleFile(file){
  Papa.parse(file, { header: true, dynamicTyping: true, skipEmptyLines: true,
    complete: ({ data }) => { RAW = data; dropZone.hidden = true; initFilters(); render(); }
  });
}
dropZone.addEventListener('dragover', e => e.preventDefault());
dropZone.addEventListener('drop', e => { e.preventDefault(); handleFile(e.dataTransfer.files[0]); });
fileInput.addEventListener('change', e => handleFile(e.target.files[0]));
```

## Pattern 3: Live Databricks SQL

Dashboard fetches fresh data from Databricks SQL Statement API on page load. Requires a PAT (personal access token) or OAuth token. Best for monitoring dashboards that need to stay current.

**Security note:** A PAT embedded in client-side HTML is visible to anyone who views source. This pattern is for internal dashboards behind a VPN or for local use only. For broader distribution, use a server-side proxy or pre-run the query and embed the result (Pattern 1).

```js
const DATA_SOURCE = {
  type: 'databricks',
  host: 'https://tubi-dev.cloud.databricks.com',
  warehouseId: 'YOUR_WAREHOUSE_ID',
  token: 'YOUR_PAT',   // or read from a prompt / env var at build time
  query: `SELECT partner_type, DATE_TRUNC('month', ds) AS ms, COUNT(*) AS cnt
           FROM core_prod.dsa.example_table
           WHERE ds >= DATEADD(MONTH, -12, CURRENT_DATE)
           GROUP BY 1, 2 ORDER BY 1, 2`
};

async function loadData(){
  const resp = await fetch(`${DATA_SOURCE.host}/api/2.0/sql/statements`, {
    method: 'POST',
    headers: { 'Authorization': `Bearer ${DATA_SOURCE.token}`, 'Content-Type': 'application/json' },
    body: JSON.stringify({
      warehouse_id: DATA_SOURCE.warehouseId,
      statement: DATA_SOURCE.query,
      wait_timeout: '60s',
      disposition: 'INLINE'
    })
  });
  const json = await resp.json();
  const cols = json.manifest.schema.columns.map(c => c.name);
  return json.result.data_array.map(row =>
    Object.fromEntries(cols.map((c, i) => [c, isNaN(row[i]) ? row[i] : Number(row[i])]))
  );
}

let RAW = [];
loadData().then(data => { RAW = data; initFilters(); render(); })
  .catch(err => { document.querySelector('.kpi-row').innerHTML =
    `<div class="kpi-card"><div class="value" style="font-size:18px;color:var(--neg)">Query failed</div><div class="label">${err.message}</div></div>`; });
```

### With a refresh button

Add to the toolbar:

```html
<button class="btn" id="refreshBtn" onclick="refreshData()">Refresh</button>
```

```js
async function refreshData(){
  refreshBtn.textContent = 'Loading…'; refreshBtn.disabled = true;
  try { RAW = await loadData(); render(); }
  catch(e) { alert('Refresh failed: ' + e.message); }
  finally { refreshBtn.textContent = 'Refresh'; refreshBtn.disabled = false; }
}
```

## Pattern 4: Generic REST API / JSON URL

```js
const DATA_SOURCE = { type: 'url', url: 'https://api.example.com/metrics?range=12m' };

async function loadData(){
  const resp = await fetch(DATA_SOURCE.url);
  const json = await resp.json();
  return json.data || json.results || json;   // adapt to the API's envelope
}
loadData().then(data => { RAW = data; initFilters(); render(); });
```

## Shared: `initFilters()` helper

When data loads asynchronously (patterns 2–4), filters need to be populated after the data arrives, not at page load. Extract the filter-population loop into a function:

```js
function initFilters(){
  document.querySelectorAll('select[data-field]').forEach(sel => {
    const f = sel.dataset.field;
    if (f.startsWith('__')) return;
    const current = sel.value;
    while (sel.options.length > 1) sel.remove(1);   // keep "(All)"
    [...new Set(RAW.map(r => r[f]))].sort().forEach(val => sel.add(new Option(val, val)));
    if ([...sel.options].some(o => o.value === current)) sel.value = current;
    sel.addEventListener('change', render);
  });
}
```

---

# Show SQL

A "SQL" toggle button on each chart card and table that reveals the query behind the data. Include it when the audience is technical (analysts, data scientists); skip it for exec/ops dashboards.

## Markup

Add to each `.chart-card` or wrap tables in a `.tbl-wrap`:

```html
<div class="chart-card">
  <button class="sql-toggle" onclick="toggleSql(this)">SQL</button>
  <h3>Chart Title</h3>
  <div class="chart-box"><canvas id="myChart"></canvas></div>
  <pre class="sql-block" data-sql-key="myChart"></pre>
</div>
```

## Script

Store each chart's SQL in a config object, then populate and wire the toggles:

```js
const SQL = {
  myChart: `SELECT ...`,
  myTable: `SELECT ...`
};

document.querySelectorAll('.sql-block[data-sql-key]').forEach(block => {
  const key = block.dataset.sqlKey;
  if (SQL[key]) block.innerHTML = `<button class="sql-copy" onclick="copySql(this)">Copy</button>${esc(SQL[key])}`;
});

function toggleSql(btn){
  const block = btn.closest('.chart-card, .tbl-wrap').querySelector('.sql-block');
  block.classList.toggle('visible');
  btn.classList.toggle('active');
}
function copySql(btn){
  const block = btn.closest('.sql-block');
  const sql = block.textContent.replace('Copy', '').trim();
  navigator.clipboard.writeText(sql).then(() => {
    btn.textContent = 'Copied!';
    setTimeout(() => btn.textContent = 'Copy', 1500);
  });
}
```

Styles for `.sql-toggle`, `.sql-block`, and `.sql-copy` are in `tubi-theme.css`. Hidden in print mode.

---

# Advanced components & opt-in modules

The base shell stays simple. Reach for these when a dashboard needs them. (Cross-filtering used to live here — it's now baseline behavior; see the Cross-filtering section right after "Chart container" above.)

## Tabbed navigation (multiple views in one file)

Mirrors the Tableau tab strip. Put each view in a `.tab-panel`; the bar toggles them.

```html
<nav class="tab-bar" id="tabs">
  <button class="active" data-tab="ttt">TTT</button>
  <button data-tab="current">Current Data</button>
  <button data-tab="kpi">KPI Tracking</button>
</nav>

<div class="tab-panel active" id="ttt">…view 1…</div>
<div class="tab-panel" id="current">…view 2…</div>
<div class="tab-panel" id="kpi">…view 3…</div>
```

```js
document.getElementById('tabs').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  document.querySelectorAll('#tabs button').forEach(x => x.classList.toggle('active', x === b));
  document.querySelectorAll('.tab-panel').forEach(p => p.classList.toggle('active', p.id === b.dataset.tab));
});
```

## Enhanced KPI card (sparkline + "as of" + source)

```html
<div class="kpi-card">
  <div class="value">$37.1M</div>
  <div class="label">Estimated Revenue</div>
  <div class="delta pos">+2.1% MoM</div>
  <div class="spark"><canvas id="sparkRev"></canvas></div>
  <div class="asof">as of Jun 28, 2026</div>
</div>
```

```js
// tiny inline trend — no axes, no legend
new Chart(document.getElementById('sparkRev'), {
  type: 'line',
  data: { labels: rev.map((_,i)=>i), datasets:[{ data: rev,
    borderColor: v('--tubi-purple'), borderWidth: 2, pointRadius: 0, tension:.3 }] },
  options: { plugins:{legend:{display:false},tooltip:{enabled:false}},
    scales:{x:{display:false},y:{display:false}}, responsive:true, maintainAspectRatio:false }
});
```

Page- or section-level source caption:

```html
<div class="caption-source">Source: <code>core_prod.tubidw.video_session</code> · calendar-month TVT</div>
```

## Dark theme toggle

The theme ships a full dark palette under `[data-theme="dark"]`. Add a toggle:

```html
<div class="dash-toolbar"><button class="btn" id="themeBtn">Dark</button></div>
```
```js
themeBtn.addEventListener('click', () => {
  const dark = document.documentElement.getAttribute('data-theme') === 'dark';
  document.documentElement.setAttribute('data-theme', dark ? '' : 'dark');
  themeBtn.textContent = dark ? 'Dark' : 'Light';
  // Charts read CSS vars at creation — re-run render() (or chart.update()) after toggling.
});
```

Charts capture colors when built, so call your `render()` again after toggling so they pick up the new variables.

## Export chart to PNG

```html
<button class="btn" onclick="downloadChart('lineChart','ttt.png')">Export PNG</button>
```
```js
function downloadChart(canvasId, filename){
  const a=document.createElement('a');
  a.href=document.getElementById(canvasId).toDataURL('image/png',1);
  a.download=filename; a.click();
}
```

Print / PDF works out of the box: the print stylesheet hides filters, tabs, and buttons, expands all tab panels, and avoids breaking cards across pages. Just use the browser's Print → Save as PDF.

## Drill-down + shareable URL state

Persist filter selections in the URL query so a pre-filtered view can be shared or bookmarked.

```js
function writeUrl(){
  const p = new URLSearchParams();
  document.querySelectorAll('select[id^="f_"]').forEach(s => p.set(s.id, s.value));
  history.replaceState(null, '', '?' + p.toString());
}
function readUrl(){
  const p = new URLSearchParams(location.search);
  p.forEach((val,key) => { const el=document.getElementById(key); if(el) el.value=val; });
}
// call readUrl() before the first render(); call writeUrl() at the end of render()
```

## Small multiples

Use the existing grid at 3-up with compact chart cards (Top-of-Funnel style):

```html
<div class="chart-grid chart-grid--3">
  <div class="chart-card"><h3>DAU</h3><div class="chart-box" style="height:200px"><canvas></canvas></div></div>
  <!-- repeat -->
</div>
```

## Auto-caption (frame the number)

`scripts/build_dashboard.py` exposes `auto_caption(current, prior, label, unit, money)` which returns a framed string like `Total TVT $1,135.5M — up 14.4% vs prior`. Use it to fill a KPI `.delta` line so every card states a comparison, not a bare value.

---

# Helper scripts

- `scripts/build_dashboard.py` — turn a CSV or pandas DataFrame into the `#data` island (no hand-editing JSON). CLI: `python build_dashboard.py data.csv --cols a,b,c --out island.html`. Notebook: `from build_dashboard import embed_data`.
- `scripts/lint_dashboard.py` — check a finished dashboard against the style guide (structure order, palette, every KPI carries a comparison, theme loaded). `python lint_dashboard.py my-dashboard.html`. Run it as the verify step.

### Large datasets

Embedding more than a few thousand rows bloats the file and slows first paint. Pre-aggregate to the grain the charts actually need (e.g. month × partner medians) before calling `embed_data`, and keep only the columns the filters and charts use. If you truly need row-level detail, consider a live artifact that fetches on demand instead of an embedded island.

## Accessible chart (aria + hidden data table)

Give every chart a text alternative and expose its numbers to screen readers.

```html
<div class="chart-card">
  <h3>Median TTT by Partner Type</h3>
  <div class="chart-box">
    <canvas id="ttt" role="img"
      aria-label="Median time-to-Tubi by partner type, Jun 2025–May 2026. Priority peaks at 60 days in Oct; Creator stays lowest."></canvas>
  </div>
  <!-- visually hidden but read aloud; mirrors the chart data -->
  <table class="sr-only">
    <caption>Median TTT by partner type</caption>
    <tr><th>Month</th><th>Creator</th><th>Non-Priority</th><th>Priority</th></tr>
    <!-- rows… -->
  </table>
</div>
```

Keep the `aria-label` about the **takeaway**, not just the title. The core-5 series palette is colorblind-safe; past 5 series, add marker shapes (`pointStyle`) or direct labels rather than relying on hue.
