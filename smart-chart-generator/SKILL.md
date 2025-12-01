---
name: smart-chart-generator
description: Automatically generate optimal charts from CSV data with professional business styling. Analyzes data structure (numeric/categorical/temporal), selects appropriate chart types (line, bar, scatter, heatmap, etc.), and outputs multiple PNG visualizations with insights in Japanese. Use when users upload CSV files and request "create charts", "visualize this data", or "analyze and graph". Supports Japanese column names, uses Noto Sans font, outputs individual PNG files with corresponding insight text files.
---

# Smart Chart Generator

Automatically analyze CSV data and generate professional business charts with actionable insights in Japanese.

## Purpose

Transform clean CSV data into multiple professional visualizations by automatically detecting data types, selecting optimal chart types, and generating insights. Each chart is saved as a high-quality PNG with a corresponding insight text file.

## Workflow

1. **Load and inspect CSV data**
   - Read CSV file with Japanese encoding support (UTF-8, Shift-JIS, CP932)
   - Display data shape, column names, and first few rows

2. **Analyze data structure**
   - Detect column types: numeric, categorical, datetime, text
   - Identify temporal patterns, correlations, distributions
   - Count unique values per categorical column
   - Check for date/time columns

3. **Select optimal chart types** based on data characteristics:
   - **Temporal data** → Line chart, area chart
   - **Categorical comparisons** → Bar chart, horizontal bar chart
   - **Proportions/composition** → Pie chart, stacked bar chart
   - **Correlations** → Scatter plot, heatmap
   - **Distributions** → Histogram, box plot
   - **Multiple numeric columns** → Multi-line chart, grouped bar chart

4. **Generate multiple perspectives**
   - Create 2-5 charts depending on data complexity
   - Each chart focuses on a different analytical angle
   - Prioritize most informative visualizations

5. **Apply consistent styling**
   - Font: Noto Sans JP (Japanese), Noto Sans (alphanumeric)
   - Color palette: Professional business colors
   - High resolution: 300 DPI, 10x6 inch default size
   - Clean layout: Clear labels, legends, titles

6. **Save outputs**
   - Charts: `chart_1.png`, `chart_2.png`, `chart_3.png`, ...
   - Insights: `insights_1.txt`, `insights_2.txt`, `insights_3.txt`, ...
   - All files saved to `/mnt/user-data/outputs/`

7. **Generate insights in Japanese** for each chart:
   - Key trends and patterns
   - Notable data points or anomalies
   - Numerical evidence (means, totals, percentages)
   - Business implications or recommendations

## Technical Implementation

### Required Libraries

```python
import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np
from matplotlib import font_manager
```

### Font Configuration

```python
# Noto Sans JP for Japanese text
plt.rcParams['font.sans-serif'] = ['Noto Sans JP', 'Noto Sans']
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['axes.unicode_minus'] = False
```

### Color Palette

Use professional business colors:
```python
BUSINESS_COLORS = ['#2E5090', '#4A90E2', '#7CB342', '#FFA726', '#EF5350', '#AB47BC']
sns.set_palette(BUSINESS_COLORS)
```

### Chart Generation Pattern

For each chart:
```python
fig, ax = plt.subplots(figsize=(10, 6), dpi=300)
# ... create visualization ...
ax.set_title('Chart Title', fontsize=16, weight='bold')
ax.set_xlabel('X Label', fontsize=12)
ax.set_ylabel('Y Label', fontsize=12)
plt.tight_layout()
plt.savefig(f'/mnt/user-data/outputs/chart_{i}.png', dpi=300, bbox_inches='tight')
plt.close()
```

## Data Type Detection Logic

### Temporal Detection
- Check for datetime dtype
- Parse strings matching date patterns: `YYYY-MM-DD`, `YYYY/MM/DD`, `YYYY年MM月DD日`
- Look for column names containing: 日付, 年月, date, time, 時刻

### Numeric Detection
- Check for int64, float64 dtypes
- Verify numeric range is reasonable for visualization

### Categorical Detection
- String or object dtype with < 50 unique values
- Boolean columns
- Columns with repeated values

## Chart Selection Examples

### Example 1: Sales Data (日付, 商品カテゴリ, 売上金額)
Charts generated:
1. Line chart: Sales trend over time
2. Bar chart: Sales by product category
3. Stacked bar chart: Monthly sales breakdown by category

### Example 2: Survey Data (年齢層, 満足度, 利用頻度, 地域)
Charts generated:
1. Bar chart: Satisfaction by age group
2. Pie chart: Regional distribution
3. Grouped bar chart: Usage frequency by age group

### Example 3: Web Analytics (日時, ページ, 滞在時間, デバイス)
Charts generated:
1. Line chart: Traffic over time
2. Horizontal bar chart: Top pages by visits
3. Pie chart: Device distribution
4. Box plot: Dwell time distribution by page type

## Insight Generation Guidelines

Each insight file should contain:

1. **Overview** (1-2 sentences)
   - What the chart shows
   - Overall trend or pattern

2. **Key Findings** (2-4 bullet points)
   - Specific numerical facts
   - Notable patterns or anomalies
   - Comparisons between categories

3. **Business Implications** (1-2 sentences)
   - What this means for decision-making
   - Recommended actions or areas to investigate

Example insight format:
```
【グラフ概要】
このグラフは2024年1月から12月までの月次売上推移を示しています。

【主要な発見】
- 7月に売上がピーク（850万円）を記録
- 10月-12月は前年同期比で15%増加
- 2月と8月に若干の落ち込みが見られる

【ビジネス上の示唆】
第3四半期の成長トレンドを維持するため、成功要因の分析が推奨されます。
2月・8月の季節変動パターンを考慮した在庫計画の見直しが有効です。
```

## Input Requirements

- **Format**: CSV file (`.csv`)
- **Encoding**: UTF-8, Shift-JIS, or CP932
- **Data quality**: Clean data (no missing values or outliers)
- **Column names**: Japanese or English supported
- **Size**: Recommended < 100,000 rows for performance

## Output Specification

### Chart Files
- **Format**: PNG
- **Resolution**: 300 DPI
- **Size**: 10x6 inches (adjustable for specific chart types)
- **Naming**: `chart_1.png`, `chart_2.png`, ...
- **Location**: `/mnt/user-data/outputs/`

### Insight Files
- **Format**: Plain text (`.txt`)
- **Encoding**: UTF-8
- **Language**: Japanese
- **Naming**: `insights_1.txt`, `insights_2.txt`, ...
- **Location**: `/mnt/user-data/outputs/`

## Constraints

### DO
- Automatically detect data types and optimal chart types
- Generate 2-5 charts per CSV based on data complexity
- Use consistent Noto Sans font family
- Apply professional business color palette
- Generate insights in Japanese
- Support Japanese column names

### DO NOT
- Perform data cleaning (missing values, outliers) - Use separate preprocessing skill
- Create interactive dashboards
- Generate integrated reports (Word/PowerPoint)
- Connect to real-time data sources
- Include more than 5 charts per analysis (to avoid overwhelming users)

## Error Handling

Common issues and solutions:

1. **Encoding errors**
   ```python
   encodings = ['utf-8', 'shift-jis', 'cp932']
   for enc in encodings:
       try:
           df = pd.read_csv(file_path, encoding=enc)
           break
       except:
           continue
   ```

2. **Font not found**
   - Verify Noto Sans JP is installed
   - Fall back to system default fonts
   - Notify user if Japanese text may not render correctly

3. **Too many categories** (>20 for pie/bar charts)
   - Group smaller categories into "その他"
   - Use top N categories only
   - Suggest alternative chart type

4. **Empty or invalid data**
   - Check for empty DataFrame
   - Validate at least one numeric column exists
   - Provide clear error message to user
