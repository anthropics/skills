---
name: data-analysis
description: Use when analyzing structured data files (CSV, Excel, logs, exports), generating charts, or producing analysis reports. Triggers: "分析这个文件", "分析数据", "画趋势图", "两个版本", "内部版", "客户版", "analyze this file", "generate charts", "trend analysis", "data report".
---

# Data Analysis Skill

Workflow for loading structured data, enriching it, generating charts, and writing reports in one or two versions (internal / client).

For **bot / crawler traffic** specifically, also invoke `bot-traffic-analysis` after this skill.

---

## Step 0: Sniff file format before loading

Files named `.csv` are sometimes actually xlsx. Check magic bytes first:

```bash
python3 -c "
with open('PATH', 'rb') as f: sig = f.read(4)
print('xlsx' if sig[:2] == b'PK' else 'csv/text', '|', sig.hex())
"
```

| Magic bytes | Format | Loader |
|---|---|---|
| `50 4B` (PK) | xlsx | `pd.read_excel()` |
| anything else | csv/tsv | `pd.read_csv()` |

**File lock warning (macOS):** If a file is open in Numbers/Excel, a lock file (`.~filename`) may shadow the real file. Ask user to close the application before loading.

---

## Step 1: Install dependencies

```bash
pip3 install pandas openpyxl matplotlib --break-system-packages -q
```

---

## Step 2: Load and inspect

```python
import pandas as pd

try:
    df = pd.read_excel('PATH')
except:
    df = pd.read_csv('PATH')

print(df.shape, df.dtypes.to_string())
print(df.head(3).to_string())
```

**Timestamp parsing** — always inspect raw format before converting:
```python
print(df['ts_col'].head(3))

# Non-standard format example: "Apr 13, 2026 @ 10:33:15.991"
df['ts'] = df['ts'].str.replace(' @ ', ' ')
df['ts'] = pd.to_datetime(df['ts'], format='%b %d, %Y %H:%M:%S.%f')
df['date'] = df['ts'].dt.date
```

---

## Step 3: Enrich / classify

Add derived columns before aggregating. Write a classify function, apply via `.apply()`, then sanity-check with a cross-tab:

```python
def classify(row):
    val = row['raw_col']
    if pd.isna(val): return 'unknown'
    v = str(val).lower()
    if 'keyword_a' in v: return 'category_a'
    if 'keyword_b' in v: return 'category_b'
    return 'other'

df['category'] = df.apply(classify, axis=1)
print(pd.crosstab(df['group_col'], df['category']))  # sanity check
```

If "other/unknown" is implausibly high, review raw values and add missing rules before proceeding.

---

## Step 4: Handle unequal observation periods

When comparing groups with different data lengths (e.g., Group A = 5 days, Group B = 11 days):

- **Never compare raw totals** — always use **daily averages** (total ÷ days)
- Document the period per group clearly in every table

For **period-over-period comparison within one group**, split into windows:

```python
import datetime
w1 = df[(df['date'] >= datetime.date(2026,4,3)) & (df['date'] <= datetime.date(2026,4,9))]
w2 = df[(df['date'] >= datetime.date(2026,4,10)) & (df['date'] <= datetime.date(2026,4,13))]
avg1, avg2 = len(w1) / 7, len(w2) / 4
pct_change = (avg2 - avg1) / avg1 * 100
```

---

## Step 5: Generate charts

**Always call `matplotlib.use('Agg')` before importing pyplot.**

```python
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from pathlib import Path

CHART_DIR = 'OUTPUT_DIR/charts'
Path(CHART_DIR).mkdir(parents=True, exist_ok=True)
```

### Chinese font setup (macOS)
```python
plt.rcParams['font.sans-serif'] = ['PingFang SC', 'Arial Unicode MS', 'Heiti SC', 'DejaVu Sans']
plt.rcParams['axes.unicode_minus'] = False
```

### Consistent color palette

Define once at the top, reference everywhere. Morandi palette (professional, desaturated, works well for client reports):

```python
C = {
    'category_a': '#C17C74',
    'category_b': '#D4A85C',
    'category_c': '#7B9EAE',
    'category_d': '#8EA88A',
    'anomaly':    '#C4956A',
}
```

### Chart selection guide

| Goal | Chart type |
|---|---|
| Volume over time | Stacked bar or line |
| Category share | Pie or 100% stacked bar |
| Compare groups | Grouped bar |
| Rankings | Horizontal bar |
| Distribution | Histogram |
| Period-over-period with trend | 3-panel (see below) |

### Always label values on charts

```python
# Total on top of stacked bar
def label_bar_top(ax, x_pos, total, threshold=3):
    if total >= threshold:
        ax.text(x_pos, total * 1.02 + 0.5, str(int(total)),
                ha='center', va='bottom', fontsize=8, color='#444444', fontweight='bold')

# Value inside a bar segment
def label_segment(ax, x_pos, y_bottom, val, threshold=10):
    if val >= threshold:
        ax.text(x_pos, y_bottom + val / 2, str(int(val)),
                ha='center', va='center', fontsize=8, color='white', fontweight='bold')
```

### Period-over-period: 3-panel layout

Structure charts that compare two time windows as coarse → fine:

```
Panel ①  Total volume (bar: Period 1 vs Period 2)
Panel ②  Daily average (bar: Period 1 avg vs Period 2 avg)
Panel ③  Category breakdown daily avg (grouped bar, same two periods)
```

Add ▲/▼ pct-change annotations above each bar group:
```python
pct = (val2 - val1) / val1 * 100
sym, color = ('▲', '#2E7D32') if pct >= 0 else ('▼', '#C62828')
ax.text(x, top * 1.1, f'{sym}{abs(pct):.0f}%', ha='center', color=color, fontweight='bold')
```

### Standard axes style
```python
def style_ax(ax):
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.set_facecolor('#FAFAFA')
    ax.grid(axis='y', alpha=0.35, linestyle='--', color='#CCCCCC')
```

Number chart files (`01_`, `02_`, …). Per-entity charts: `06_{entity}_topic.png`.

```python
plt.tight_layout()
plt.savefig(f'{CHART_DIR}/01_name.png', dpi=150, bbox_inches='tight')
plt.close()
```

---

## Step 6: Choose output format

| Format | When to use | Charts embedded? | Skill |
|---|---|---|---|
| `.md` | Internal notes, quick review | No | — |
| `.docx` | Team or stakeholder reports | Yes | `document-skills:docx` |
| `.pdf` | Final client deliverables | Yes | `document-skills:pdf` |

---

## Step 7: Write reports

### Two-version pattern

| | Internal | Client |
|---|---|---|
| Numbers | All raw counts + percentages | Only numbers that support the narrative |
| Methodology | Full 统计口径 per metric | Omit or single footnote |
| Anomalies | Document with evidence | Only if relevant to client |
| Framing | Analytical, neutral | Lead with most impactful finding |
| Ending | Open questions / action items | "What to watch next" timeline table |

**Multi-entity:** produce one combined overview + one individual report per entity, from the same charts.

### Methodology blocks (统计口径)

Every metric section in the internal report needs a note covering:
1. **What is counted** — which records/categories are included or excluded
2. **How calculated** — the formula

```javascript
// docx pattern
function methodology(lines) {
  return new Paragraph({
    shading: { fill: 'F5F5F5', type: ShadingType.CLEAR },
    border: { left: { style: BorderStyle.SINGLE, size: 6, color: 'AAAAAA', space: 4 } },
    children: lines.map((line, i) => new TextRun({
      text: line, font: 'Arial', size: 18, italics: true, color: '666666',
      break: i > 0 ? 1 : 0,
    }))
  });
}
```

---

## Common issues

| Problem | Fix |
|---|---|
| `ModuleNotFoundError: pandas` | `pip3 install pandas openpyxl --break-system-packages -q` |
| `.csv` reads garbage | File is xlsx — use `pd.read_excel()` |
| `DateParseError` | Inspect raw format with `.head()`, use explicit `format=` |
| Charts not saving | `matplotlib.use('Agg')` must come before `import matplotlib.pyplot` |
| Groups have unequal date ranges | Use daily averages, not raw totals |
| Suspiciously high "other/unknown" % | Classification rules missing patterns — review raw values |
| macOS file lock (`.~filename`) | Ask user to close the file in Numbers/Excel |
