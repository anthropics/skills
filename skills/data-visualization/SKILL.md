---
name: data-visualization
description: Use this skill whenever the user wants to create charts, graphs, plots, or any visual representation of data. This includes bar charts, line charts, scatter plots, histograms, heatmaps, pie charts, box plots, dashboards, and interactive visualizations. If the user mentions matplotlib, seaborn, plotly, charts, graphs, or wants to visualize data from a CSV, DataFrame, or database, use this skill.
license: Proprietary. LICENSE.txt has complete terms
---

# Data Visualization Guide

## Overview

This guide covers creating charts and visualizations using Python's most popular libraries: matplotlib, seaborn, and plotly.

## Library Selection

| Library | Best For | Output |
|---------|----------|--------|
| matplotlib | Fine-grained control, publication figures | Static PNG/PDF |
| seaborn | Statistical plots, attractive defaults | Static PNG/PDF |
| plotly | Interactive charts, dashboards | HTML/Interactive |

## Installation

```bash
pip install matplotlib seaborn plotly pandas
```

## Matplotlib

### Basic Line Chart
```python
import matplotlib.pyplot as plt
import numpy as np

x = np.linspace(0, 10, 100)
y = np.sin(x)

plt.figure(figsize=(10, 6))
plt.plot(x, y, label='sin(x)', color='blue', linewidth=2)
plt.xlabel('X axis')
plt.ylabel('Y axis')
plt.title('Sine Wave')
plt.legend()
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig('line_chart.png', dpi=150)
plt.show()
```

### Bar Chart
```python
import matplotlib.pyplot as plt

categories = ['A', 'B', 'C', 'D', 'E']
values = [23, 45, 12, 67, 34]

fig, ax = plt.subplots(figsize=(8, 6))
bars = ax.bar(categories, values, color='steelblue', edgecolor='white')

# Add value labels on bars
for bar, val in zip(bars, values):
    ax.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.5,
            str(val), ha='center', va='bottom', fontsize=11)

ax.set_xlabel('Category')
ax.set_ylabel('Value')
ax.set_title('Bar Chart Example')
plt.tight_layout()
plt.savefig('bar_chart.png', dpi=150)
```

### Scatter Plot
```python
import matplotlib.pyplot as plt
import numpy as np

np.random.seed(42)
x = np.random.randn(100)
y = 2 * x + np.random.randn(100) * 0.5

plt.figure(figsize=(8, 6))
plt.scatter(x, y, alpha=0.6, color='coral', edgecolors='darkred', s=50)
plt.xlabel('X')
plt.ylabel('Y')
plt.title('Scatter Plot')
plt.tight_layout()
plt.savefig('scatter.png', dpi=150)
```

### Multiple Subplots
```python
import matplotlib.pyplot as plt
import numpy as np

fig, axes = plt.subplots(2, 2, figsize=(12, 10))

x = np.linspace(0, 10, 100)

axes[0, 0].plot(x, np.sin(x))
axes[0, 0].set_title('Sine')

axes[0, 1].plot(x, np.cos(x), color='orange')
axes[0, 1].set_title('Cosine')

axes[1, 0].hist(np.random.randn(1000), bins=30, color='green', alpha=0.7)
axes[1, 0].set_title('Histogram')

axes[1, 1].scatter(np.random.rand(50), np.random.rand(50), alpha=0.6)
axes[1, 1].set_title('Scatter')

plt.suptitle('Multiple Plots', fontsize=16)
plt.tight_layout()
plt.savefig('subplots.png', dpi=150)
```

## Seaborn

### Distribution Plot
```python
import seaborn as sns
import matplotlib.pyplot as plt
import pandas as pd
import numpy as np

sns.set_theme(style='whitegrid')

data = np.random.normal(loc=0, scale=1, size=500)

fig, ax = plt.subplots(figsize=(8, 6))
sns.histplot(data, kde=True, ax=ax, color='steelblue')
ax.set_title('Distribution with KDE')
plt.tight_layout()
plt.savefig('distribution.png', dpi=150)
```

### Heatmap (Correlation Matrix)
```python
import seaborn as sns
import matplotlib.pyplot as plt
import pandas as pd
import numpy as np

# Create sample DataFrame
df = pd.DataFrame(np.random.randn(100, 6),
                  columns=['A', 'B', 'C', 'D', 'E', 'F'])

corr = df.corr()

fig, ax = plt.subplots(figsize=(8, 7))
sns.heatmap(corr, annot=True, fmt='.2f', cmap='coolwarm',
            vmin=-1, vmax=1, center=0, ax=ax,
            square=True, linewidths=0.5)
ax.set_title('Correlation Heatmap')
plt.tight_layout()
plt.savefig('heatmap.png', dpi=150)
```

### Box Plot
```python
import seaborn as sns
import matplotlib.pyplot as plt
import pandas as pd

# Load built-in dataset
tips = sns.load_dataset('tips')

fig, ax = plt.subplots(figsize=(10, 6))
sns.boxplot(data=tips, x='day', y='total_bill', hue='sex', ax=ax)
ax.set_title('Total Bill by Day and Gender')
plt.tight_layout()
plt.savefig('boxplot.png', dpi=150)
```

### Pair Plot
```python
import seaborn as sns
import matplotlib.pyplot as plt

iris = sns.load_dataset('iris')
g = sns.pairplot(iris, hue='species', diag_kind='kde')
g.fig.suptitle('Iris Dataset Pair Plot', y=1.02)
plt.tight_layout()
plt.savefig('pairplot.png', dpi=150)
```

## Plotly (Interactive)

### Interactive Line Chart
```python
import plotly.graph_objects as go
import numpy as np

x = np.linspace(0, 10, 100)

fig = go.Figure()
fig.add_trace(go.Scatter(x=x, y=np.sin(x), name='sin(x)', mode='lines'))
fig.add_trace(go.Scatter(x=x, y=np.cos(x), name='cos(x)', mode='lines'))

fig.update_layout(
    title='Interactive Line Chart',
    xaxis_title='X',
    yaxis_title='Y',
    template='plotly_white'
)
fig.write_html('interactive_chart.html')
fig.show()
```

### Interactive Bar Chart from DataFrame
```python
import plotly.express as px
import pandas as pd

df = pd.DataFrame({
    'category': ['A', 'B', 'C', 'D'],
    'value': [23, 45, 12, 67],
    'group': ['X', 'Y', 'X', 'Y']
})

fig = px.bar(df, x='category', y='value', color='group',
             title='Interactive Bar Chart',
             template='plotly_white')
fig.write_html('bar_chart.html')
fig.show()
```

### Scatter Plot with Hover Info
```python
import plotly.express as px

gapminder = px.data.gapminder().query("year == 2007")
fig = px.scatter(gapminder, x='gdpPercap', y='lifeExp',
                 size='pop', color='continent',
                 hover_name='country',
                 log_x=True,
                 title='GDP vs Life Expectancy (2007)')
fig.write_html('gapminder.html')
fig.show()
```

## Visualizing Pandas DataFrames

```python
import pandas as pd
import matplotlib.pyplot as plt

df = pd.read_csv('data.csv')

# Quick plots using pandas built-in
df['column'].plot(kind='hist', bins=30, figsize=(8, 6))
plt.title('Histogram')
plt.savefig('hist.png')

df.plot(kind='line', figsize=(10, 6))
plt.savefig('line.png')

# Time series
df.index = pd.to_datetime(df['date'])
df['value'].plot(figsize=(12, 5), title='Time Series')
plt.savefig('timeseries.png')
```

## Best Practices

- Always call `plt.tight_layout()` before saving to prevent label clipping
- Use `dpi=150` or higher for crisp output images
- Save figures before calling `plt.show()` (show clears the figure)
- Set `figsize` explicitly for consistent sizing
- Use `alpha` for overlapping elements
- Add titles, axis labels, and legends to all charts
- Use colorblind-friendly palettes: `sns.set_palette("colorblind")` or plotly's built-in accessible colors

## Quick Reference

| Chart Type | matplotlib | seaborn | plotly |
|------------|-----------|---------|--------|
| Line | `plt.plot()` | `sns.lineplot()` | `px.line()` |
| Bar | `plt.bar()` | `sns.barplot()` | `px.bar()` |
| Scatter | `plt.scatter()` | `sns.scatterplot()` | `px.scatter()` |
| Histogram | `plt.hist()` | `sns.histplot()` | `px.histogram()` |
| Box | `plt.boxplot()` | `sns.boxplot()` | `px.box()` |
| Heatmap | `plt.imshow()` | `sns.heatmap()` | `px.imshow()` |
