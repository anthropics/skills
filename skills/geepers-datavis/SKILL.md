---
name: geepers-datavis
description: Comprehensive data visualization toolkit for creating beautiful, mathematically elegant visualizations with D3.js, Chart.js, and custom SVG. Use when (1) building interactive data visualizations, (2) designing color palettes for charts, (3) choosing scales and visual encodings, (4) creating data pipelines from Census/SEC/Wikipedia APIs, (5) crafting narrative-driven data stories, (6) making perceptually accurate charts, or (7) implementing force-directed networks, timelines, or geographic maps.
license: MIT
---

# Data Visualization Skill

Create beautiful, mathematically elegant, emotionally resonant data visualizations.

## Philosophy: "Life is Beautiful"

Every visualization should:
1. **Reveal truth** through data
2. **Evoke wonder** through design
3. **Respect the viewer** through accessibility
4. **Honor complexity** through elegant simplification

## Core Capabilities

### 1. Visual Encoding

**Scale Selection**:
| Scale | Use When | Example |
|-------|----------|---------|
| Linear | Evenly distributed data | Temperature |
| Log | Multiple orders of magnitude | Population (100 to 1B) |
| Sqrt | Encoding area (circles) | Bubble chart radius |
| Time | Temporal data | Dates |

**Perceptual Honesty** - Area scales with square of radius, so use sqrt:
```javascript
// WRONG: Linear radius exaggerates large values
const badScale = d3.scaleLinear().domain([0, max]).range([0, maxRadius]);

// RIGHT: Sqrt maintains perceptual accuracy
const goodScale = d3.scaleSqrt().domain([0, max]).range([0, maxRadius]);
```

### 2. Color Design

**Palette Types**:
- **Categorical** - Distinct hues for nominal data (max 8)
- **Sequential** - Single hue gradient for ordered data
- **Diverging** - Two hues meeting at meaningful midpoint

**Colorblind-Safe Palette** (8 colors):
```javascript
const colorblindSafe = [
  '#332288', '#117733', '#44AA99', '#88CCEE',
  '#DDCC77', '#CC6677', '#AA4499', '#882255'
];
```

**Always use redundant encoding** - don't rely on color alone:
```javascript
node.attr('fill', d => colorScale(d.category))
    .attr('d', d => symbolScale(d.category)); // Shape too!
```

### 3. D3.js Patterns

**Force Simulation**:
```javascript
const simulation = d3.forceSimulation(nodes)
  .force('charge', d3.forceManyBody().strength(-300))
  .force('link', d3.forceLink(links).id(d => d.id))
  .force('center', d3.forceCenter(width/2, height/2))
  .force('collision', d3.forceCollide().radius(d => d.r + 2));
```

**Responsive SVG**:
```javascript
const svg = d3.select('#chart')
  .append('svg')
  .attr('viewBox', `0 0 ${width} ${height}`)
  .attr('preserveAspectRatio', 'xMidYMid meet');
```

**Touch-Friendly** (44x44px minimum):
```javascript
node.append('circle')
  .attr('class', 'hit-area')
  .attr('r', Math.max(actualRadius, 22))
  .attr('fill', 'transparent');
```

### 4. Narrative Structure

**Three Acts**:
1. **Invitation** - What draws viewer in? Why should they care?
2. **Discovery** - What patterns emerge? What surprises?
3. **Reflection** - What should they feel/understand/do?

**Progressive Disclosure**:
```
Level 1: Overview → Level 2: Exploration → Level 3: Detail → Level 4: Context
```

### 5. Data Pipeline

**Structure**:
```
scripts/
├── 01_fetch_raw.py    # API calls with caching
├── 02_clean_data.py   # Transformation
├── 03_validate.py     # Quality checks
└── 04_export.py       # Final format
```

**Source Documentation** (every dataset needs):
- URL, access date, update frequency
- License and confidence level
- Field descriptions and limitations

## CLI Usage

### 1. Scaffold Project (Manual Coding)
Start a new visualization project with boilerplate code.

```bash
# Available templates: force-network, timeline, choropleth, radial-tree, sankey, bubble-chart, treemap
python3 scripts/d3-scaffold.py my-viz --type radial-tree
```

### 2. Generate Visualization (Automated)
Instantly create an HTML file from a data file.

```bash
# From JSON
python3 scripts/viz-generator.py data.json --template sankey

# From CSV
python3 scripts/viz-generator.py data.csv --template bar-race
```

## MCP Tools

### `dream_visualize_data`
Generates a collaborative visualization artifact.

**Parameters:**
*   `data` (string/json): Data to visualize.
*   `template` (string): One of [force-network, timeline, choropleth, radial-tree, sankey, bubble-chart, treemap].
*   `title` (string): Title for the chart.

### `dream_list_viz_templates`
Returns descriptions of all available visualization templates.

## Utility Scripts

### Generate Color Palette
```bash
python3 scripts/color-palette.py --type sequential --hue blue --steps 9
```

### Analyze Distribution
```bash
python3 scripts/analyze-distribution.py data.csv --column value
```

## Quality Checklist

- [ ] Scale choice justified for data distribution
- [ ] Color palette is colorblind-safe
- [ ] Minimum 44x44px touch targets
- [ ] Clear entry point for viewer
- [ ] Sources documented
- [ ] Responsive on mobile
