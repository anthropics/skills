---
name: datavis
description: Comprehensive data visualization toolkit for creating beautiful, mathematically elegant visualizations with D3.js, Chart.js, and custom SVG. Use when (1) building interactive data visualizations, (2) designing color palettes for charts, (3) choosing scales and visual encodings, (4) creating data pipelines from Census/SEC/Wikipedia APIs, (5) crafting narrative-driven data stories, (6) making perceptually accurate charts, or (7) implementing force-directed networks, timelines, or geographic maps.
license: MIT
---

# Data Visualization Skill

Toolkit for creating beautiful, mathematically elegant data visualizations with D3.js, Chart.js, and custom SVG.

## Helper Scripts Available

- `scripts/create_viz.py` - Generate D3.js visualization templates
- `scripts/color_palette.py` - Generate accessible color palettes
- `scripts/validate_data.py` - Validate datasets for visualization
- `scripts/fetch_census.py` - Fetch Census Bureau data with caching

**Always run scripts with `--help` first** to see usage.

## Decision Tree: Choosing Your Chart Type

```
Data → What do you want to show?
    ├─ Comparison → How many categories?
    │   ├─ Few (<7) → Bar chart
    │   └─ Many → Horizontal bar / Grouped bar
    │
    ├─ Change over time → Line chart / Area chart
    │   └─ Multiple series → Streamgraph / Small multiples
    │
    ├─ Part-to-whole → How many parts?
    │   ├─ Few (<6) → Pie / Donut
    │   └─ Many → Treemap / Sunburst
    │
    ├─ Distribution → Histogram / Box plot / Violin
    │
    ├─ Relationship → Scatter / Bubble
    │   └─ Categories → Heatmap
    │
    ├─ Hierarchy → Tree / Dendrogram / Pack
    │
    └─ Network → Force / Arc / Chord
```

## D3.js Quick Reference

### Selection & Data Binding (v7)
```javascript
const circles = svg.selectAll('circle')
  .data(data, d => d.id)  // Key function for object constancy
  .join(
    enter => enter.append('circle')
      .attr('r', 0)
      .call(enter => enter.transition().attr('r', d => rScale(d.value))),
    update => update
      .call(update => update.transition().attr('r', d => rScale(d.value))),
    exit => exit
      .call(exit => exit.transition().attr('r', 0).remove())
  );
```

### Force Simulation
```javascript
const simulation = d3.forceSimulation(nodes)
  .force('charge', d3.forceManyBody().strength(-300))
  .force('link', d3.forceLink(links).id(d => d.id).distance(100))
  .force('center', d3.forceCenter(width/2, height/2))
  .force('collision', d3.forceCollide().radius(d => d.r + 2));
```

### Scale Selection
```javascript
// Choose scale based on data distribution
const linearScale = d3.scaleLinear().domain([0, max]).range([0, width]);
const logScale = d3.scaleLog().domain([1, 1000000]).range([0, height]);
const sqrtScale = d3.scaleSqrt().domain([0, max]).range([0, maxRadius]); // For area encoding
```

## Color Theory

### Palette Types
- **Sequential**: Single hue varying in lightness (for ordered data)
- **Diverging**: Two hues meeting at neutral (for data with meaningful center)
- **Categorical**: Distinct hues (for unordered categories)

### Colorblind-Safe Palettes
```javascript
// Wong palette (colorblind-safe categorical)
const wongPalette = ['#000000', '#E69F00', '#56B4E9', '#009E73',
                     '#F0E442', '#0072B2', '#D55E00', '#CC79A7'];

// Viridis (colorblind-safe sequential)
d3.scaleSequential(d3.interpolateViridis);
```

### Perceptual Uniformity
- Equal steps in data should produce equal perceived color change
- Use `d3.interpolateLab()` for perceptually uniform gradients
- Test with colorblind simulators

## Mathematical Elegance

### Perceptual Accuracy
```javascript
// Area encoding: Use sqrt scale for accurate perception
const radiusScale = d3.scaleSqrt()
  .domain([0, d3.max(data, d => d.value)])
  .range([0, 50]);

// Circle area = π × r² - so radius must scale with sqrt(value)
```

### Choosing Scales
| Data Distribution | Scale Choice |
|-------------------|--------------|
| Normal, bounded | Linear |
| Power law, skewed | Log or sqrt |
| Percentages | Linear 0-100% |
| Growth rates | Log |

## Accessibility Requirements

### WCAG 2.1 for Data Visualization
- 4.5:1 contrast ratio for text
- 3:1 contrast ratio for graphical elements
- Don't rely on color alone (use patterns, labels)
- Minimum touch target: 44×44px

```javascript
// ARIA labels for chart regions
svg.attr('role', 'img')
  .attr('aria-label', 'Bar chart showing sales by region');

// Keyboard navigation
nodes.attr('tabindex', 0)
  .on('keydown', function(event, d) {
    if (event.key === 'Enter' || event.key === ' ') {
      selectNode(d);
    }
  });
```

## Performance Optimization

### Canvas for Large Datasets
Use Canvas instead of SVG when you have 1000+ elements:
```javascript
const canvas = d3.select('#chart').append('canvas')
  .attr('width', width)
  .attr('height', height);
const ctx = canvas.node().getContext('2d');

function draw() {
  ctx.clearRect(0, 0, width, height);
  data.forEach(d => {
    ctx.beginPath();
    ctx.arc(xScale(d.x), yScale(d.y), 3, 0, 2 * Math.PI);
    ctx.fillStyle = colorScale(d.category);
    ctx.fill();
  });
}
```

## Anti-Patterns to Avoid

- 3D charts (almost always misleading)
- Pie charts for many categories (>6)
- Dual y-axes (confusing correlation)
- Rainbow color scales (not perceptual)
- Animation without purpose
- Tooltips that cover the data

## Example: Using create_viz.py

```bash
# Generate a bar chart template
python scripts/create_viz.py --type bar --data sales.csv --output chart.html

# Generate a force-directed network
python scripts/create_viz.py --type force --data network.json --output network.html
```

## Example: Using color_palette.py

```bash
# Generate a categorical palette
python scripts/color_palette.py --type categorical --count 5

# Generate a colorblind-safe sequential palette
python scripts/color_palette.py --type sequential --colorblind-safe --steps 9
```

## Reference Files

- **examples/** - Working examples:
  - `bar_chart.html` - Responsive bar chart with accessibility
  - `force_network.html` - Draggable force-directed network
  - `choropleth.html` - Geographic visualization template
