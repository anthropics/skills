# Statistical Visualization Standards

Reference guide for the `visualization_agent`. Covers APA 7.0 figure guidelines, accessible color palettes, chart type selection, common pitfalls, and code templates.

---

## APA 7.0 Figure Guidelines (Chapter 7 Summary)

### General Principles

1. **Every figure must add value** — do not visualize data that is better expressed in a sentence or table
2. **Figures are numbered sequentially** (Figure 1, Figure 2, ...) in order of first mention
3. **Every figure must be cited in text** ("As shown in Figure 1, ...")
4. **Captions appear below the figure** (unlike table notes which appear above)
5. **Figures must be interpretable without reading the text** — include all necessary context in the caption

### Caption Format

```
Figure [N]                          ← Bold, on its own line
[Descriptive Title]                 ← Italic, sentence case, next line
Note. [Explanation if needed]       ← Plain text, starts with "Note."
```

### Typography Specifications

| Element | Size | Style |
|---------|------|-------|
| Figure label ("Figure 1") | 10-12 pt | Bold |
| Figure title | 10-12 pt | Italic |
| Axis labels | 8-10 pt | Plain, sentence case |
| Axis tick labels | 8-9 pt | Plain |
| Legend text | 8-9 pt | Plain |
| Annotations | 8 pt | Plain or italic |
| Note text | 8-9 pt | Plain |

### Required Elements

- [ ] Axis labels (both axes, descriptive, with units)
- [ ] Tick marks and tick labels
- [ ] Legend (for multi-group figures)
- [ ] Error bars or confidence intervals (for mean comparisons)
- [ ] Scale bars (for images/maps)
- [ ] Caption with Figure number + title
- [ ] Note (if explanation is needed)

---

## Accessible Color Palettes

### Primary: Viridis (Perceptually Uniform)

Best for: continuous/sequential data.

| Index | Hex Code | Usage |
|-------|----------|-------|
| 0 | `#440154` | Darkest value |
| 1 | `#46327E` | |
| 2 | `#365C8D` | |
| 3 | `#277F8E` | |
| 4 | `#1FA187` | |
| 5 | `#4AC16D` | |
| 6 | `#9FDA3A` | |
| 7 | `#FDE725` | Lightest value |

### Alternative: Cividis (Deuteranopia/Protanopia Optimized)

Best for: publications where colorblind accessibility is critical.

| Index | Hex Code |
|-------|----------|
| 0 | `#00204D` |
| 1 | `#00336F` |
| 2 | `#39486B` |
| 3 | `#5F5D6A` |
| 4 | `#7B7463` |
| 5 | `#9A8C4F` |
| 6 | `#BBA634` |
| 7 | `#DEC000` |
| 8 | `#FFE945` |

### Categorical: Tol's Qualitative Palette (Max 8 Categories)

Best for: categorical comparisons, group labels.

| Label | Hex Code | Sample Use |
|-------|----------|------------|
| Blue | `#0077BB` | Group 1 / Baseline |
| Cyan | `#33BBEE` | Group 2 |
| Teal | `#009988` | Group 3 |
| Orange | `#EE7733` | Group 4 / Highlight |
| Red | `#CC3311` | Group 5 / Alert |
| Magenta | `#EE3377` | Group 6 |
| Grey | `#BBBBBB` | Reference / NA |
| Black | `#000000` | Outline / Text |

### Diverging: Blue-Red (For Correlation/Difference Maps)

| Negative | Zero | Positive |
|----------|------|----------|
| `#2166AC` | `#F7F7F7` | `#B2182B` |
| `#4393C3` | | `#D6604D` |
| `#92C5DE` | | `#F4A582` |

### Accessibility Rules

1. Never rely on color alone — pair with shape, pattern, or label
2. Minimum contrast ratio: 3:1 (WCAG AA for non-text elements)
3. Test with a colorblindness simulator before finalizing
4. When printing in grayscale, patterns or labels must still distinguish groups

---

## Chart Type Decision Tree

### Which Chart for Which Data?

| Your Data | Your Question | Recommended Chart | Avoid |
|-----------|--------------|-------------------|-------|
| Categories + values | Compare magnitudes | **Bar chart** (vertical or horizontal) | Pie chart |
| Categories + values + groups | Compare across groups | **Grouped bar chart** or **stacked bar** | 3D bar chart |
| Continuous variable, 1 group | Show distribution | **Histogram** + density curve | |
| Continuous variable, 2-5 groups | Compare distributions | **Boxplot** or **violin plot** | Bar chart of means only |
| Two continuous variables | Show relationship | **Scatter plot** + regression line | |
| Time series (1-5 series) | Show trends | **Line chart** | Bar chart for time series |
| Time series (> 5 series) | Show trends | **Small multiples** (faceted line charts) | Spaghetti plot |
| Correlation matrix | Show multi-variable relationships | **Heatmap** | Scatter plot matrix (too dense) |
| Effect sizes + CIs (meta) | Summarize meta-analysis | **Forest plot** | Bar chart |
| Effect sizes + SE (meta) | Check publication bias | **Funnel plot** | |
| Concepts + relationships | Map theoretical framework | **Network graph** / **concept map** | |
| Proportions summing to 100% | Show composition | **Stacked bar chart** | Pie chart |
| Geographic data | Show spatial patterns | **Choropleth map** | |

### When NOT to Visualize

- Fewer than 3 data points (use text or a table)
- A single percentage or mean (state in text)
- Data that requires more than 2 sentences to explain the chart (use a table)
- Redundant visualization of data already in a table

---

## Common Pitfalls

### Critical Errors (Never Do)

| Pitfall | Problem | Fix |
|---------|---------|-----|
| **Pie charts** | Human perception is poor at comparing angles/areas | Use bar chart |
| **3D charts** | Distorts values through perspective projection | Use 2D |
| **Dual y-axes** | Implies false correlation; scale choice is arbitrary | Two separate panels |
| **Rainbow colormap** | Not perceptually uniform; not colorblind-safe | Use viridis/cividis |
| **Truncated y-axis** (without marking) | Exaggerates small differences | Start at 0 or mark break clearly |
| **Missing error bars** | Hides uncertainty; readers cannot assess significance | Add SE, SD, or 95% CI bars |
| **Chartjunk** (decorative elements) | Reduces data-ink ratio; distracts from data | Remove unnecessary elements |

### Subtle Errors (Easy to Miss)

| Pitfall | Problem | Fix |
|---------|---------|-----|
| Unequal bin widths in histogram | Distorts frequency perception | Use equal bins |
| Overlapping labels | Unreadable at print size | Rotate, abbreviate, or reduce categories |
| Too many colors (> 8) | Indistinguishable at print size | Group categories or use facets |
| Legend far from data | Reader must scan back and forth | Place legend inside plot area or use direct labels |
| Aspect ratio distortion | Exaggerates or minimizes trends | Use 4:3 default; 16:9 for time series |

---

## Python matplotlib Code Templates

### Template 1: Bar Chart

```python
import matplotlib.pyplot as plt
import numpy as np

# APA 7.0 settings
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['Arial', 'Helvetica', 'DejaVu Sans'],
    'font.size': 9, 'axes.titlesize': 11, 'axes.labelsize': 10,
    'xtick.labelsize': 8, 'ytick.labelsize': 8, 'legend.fontsize': 8,
    'figure.dpi': 300, 'savefig.dpi': 300, 'savefig.bbox': 'tight',
    'axes.spines.top': False, 'axes.spines.right': False,
})
CB = ['#0077BB', '#33BBEE', '#009988', '#EE7733', '#CC3311', '#EE3377']

# Data
categories = ['Group A', 'Group B', 'Group C', 'Group D']
values = [4.2, 3.8, 5.1, 4.5]
errors = [0.3, 0.4, 0.2, 0.5]

fig, ax = plt.subplots(figsize=(6.9, 4.5))
bars = ax.bar(categories, values, yerr=errors, capsize=4,
              color=CB[:len(categories)], edgecolor='black', linewidth=0.5)
ax.set_ylabel('Score (points)')
ax.set_xlabel('Group')
ax.set_ylim(0, max(values) * 1.3)

plt.tight_layout()
plt.savefig('figure_01.pdf', format='pdf')
plt.savefig('figure_01.png', format='png')
plt.show()
```

### Template 2: Boxplot

```python
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9, 'axes.labelsize': 10,
    'figure.dpi': 300, 'axes.spines.top': False, 'axes.spines.right': False,
})
CB = ['#0077BB', '#33BBEE', '#009988', '#EE7733']

# Data (replace with actual data)
np.random.seed(42)
data = [np.random.normal(loc, 1, 50) for loc in [3.5, 4.0, 3.8, 4.5]]
labels = ['Public', 'Private', 'Technical', 'National']

fig, ax = plt.subplots(figsize=(6.9, 4.5))
bp = ax.boxplot(data, labels=labels, patch_artist=True, widths=0.6,
                medianprops=dict(color='black', linewidth=1.5))
for patch, color in zip(bp['boxes'], CB):
    patch.set_facecolor(color)
    patch.set_alpha(0.7)

ax.set_ylabel('Satisfaction Score (1-5)')
ax.set_xlabel('Institution Type')
plt.tight_layout()
plt.savefig('figure_02.pdf', format='pdf')
plt.show()
```

### Template 3: Line Chart (Trend)

```python
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9, 'axes.labelsize': 10,
    'figure.dpi': 300, 'axes.spines.top': False, 'axes.spines.right': False,
})
CB = ['#0077BB', '#CC3311', '#009988']

years = [2018, 2019, 2020, 2021, 2022, 2023]
series_a = [72, 75, 68, 71, 78, 82]
series_b = [65, 63, 60, 58, 55, 52]

fig, ax = plt.subplots(figsize=(6.9, 4.5))
ax.plot(years, series_a, 'o-', color=CB[0], label='Public universities', linewidth=1.5, markersize=5)
ax.plot(years, series_b, 's--', color=CB[1], label='Private universities', linewidth=1.5, markersize=5)
ax.set_xlabel('Year')
ax.set_ylabel('Enrollment (thousands)')
ax.legend(frameon=False)
ax.set_xlim(min(years) - 0.5, max(years) + 0.5)

plt.tight_layout()
plt.savefig('figure_03.pdf', format='pdf')
plt.show()
```

### Template 4: Scatter Plot + Regression

```python
import matplotlib.pyplot as plt
import numpy as np
from scipy import stats

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9, 'axes.labelsize': 10,
    'figure.dpi': 300, 'axes.spines.top': False, 'axes.spines.right': False,
})

# Data
np.random.seed(42)
x = np.random.uniform(10, 50, 80)
y = 0.6 * x + np.random.normal(0, 5, 80) + 10

slope, intercept, r, p, se = stats.linregress(x, y)
x_line = np.linspace(min(x), max(x), 100)
y_line = slope * x_line + intercept

fig, ax = plt.subplots(figsize=(6.9, 5.5))
ax.scatter(x, y, color='#0077BB', alpha=0.6, edgecolors='black', linewidth=0.3, s=30)
ax.plot(x_line, y_line, color='#CC3311', linewidth=1.5,
        label=f'y = {slope:.2f}x + {intercept:.2f}, r = {r:.2f}, p < .001')
ax.set_xlabel('Faculty-Student Ratio')
ax.set_ylabel('Student Satisfaction Score')
ax.legend(frameon=False, loc='lower right')

plt.tight_layout()
plt.savefig('figure_04.pdf', format='pdf')
plt.show()
```

### Template 5: Forest Plot (Meta-Analysis)

```python
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9, 'axes.labelsize': 10,
    'figure.dpi': 300,
})

studies = ['Smith (2018)', 'Chen (2019)', 'Johnson (2020)',
           'Lee (2021)', 'Garcia (2022)', 'Overall']
effects = [0.35, 0.42, 0.28, 0.51, 0.38, 0.39]
ci_lower = [0.15, 0.22, 0.08, 0.31, 0.18, 0.27]
ci_upper = [0.55, 0.62, 0.48, 0.71, 0.58, 0.51]
weights = [18, 22, 15, 25, 20, None]

fig, ax = plt.subplots(figsize=(6.9, 4.0))
y_pos = np.arange(len(studies))

for i, study in enumerate(studies):
    color = '#CC3311' if study == 'Overall' else '#0077BB'
    marker = 'D' if study == 'Overall' else 'o'
    size = 8 if study == 'Overall' else 6
    ax.errorbar(effects[i], i, xerr=[[effects[i]-ci_lower[i]], [ci_upper[i]-effects[i]]],
                fmt=marker, color=color, markersize=size, capsize=3, linewidth=1.2)

ax.axvline(x=0, color='grey', linestyle='--', linewidth=0.8)
ax.set_yticks(y_pos)
ax.set_yticklabels(studies)
ax.set_xlabel("Effect Size (Cohen's d)")
ax.invert_yaxis()
ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)

plt.tight_layout()
plt.savefig('figure_05.pdf', format='pdf')
plt.show()
```

### Template 6: Correlation Heatmap

```python
import matplotlib.pyplot as plt
import numpy as np
import seaborn as sns

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9,
    'figure.dpi': 300,
})

# Correlation matrix
labels = ['Teaching', 'Research', 'Service', 'Satisfaction', 'Retention']
corr = np.array([
    [1.00, 0.45, 0.32, 0.67, 0.55],
    [0.45, 1.00, 0.28, 0.38, 0.30],
    [0.32, 0.28, 1.00, 0.41, 0.35],
    [0.67, 0.38, 0.41, 1.00, 0.72],
    [0.55, 0.30, 0.35, 0.72, 1.00],
])

fig, ax = plt.subplots(figsize=(5.5, 5.0))
mask = np.triu(np.ones_like(corr, dtype=bool), k=1)
sns.heatmap(corr, mask=mask, annot=True, fmt='.2f', cmap='RdBu_r',
            center=0, vmin=-1, vmax=1, square=True,
            xticklabels=labels, yticklabels=labels,
            linewidths=0.5, cbar_kws={'shrink': 0.8, 'label': 'r'}, ax=ax)

plt.tight_layout()
plt.savefig('figure_06.pdf', format='pdf')
plt.show()
```

### Template 7: Funnel Plot

```python
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9, 'axes.labelsize': 10,
    'figure.dpi': 300, 'axes.spines.top': False, 'axes.spines.right': False,
})

# Data
np.random.seed(42)
effects = np.random.normal(0.4, 0.15, 20)
se = np.random.uniform(0.05, 0.25, 20)
mean_effect = np.mean(effects)

fig, ax = plt.subplots(figsize=(6.9, 5.0))
ax.scatter(effects, se, color='#0077BB', edgecolors='black', linewidth=0.3, s=40, alpha=0.7)
ax.axvline(x=mean_effect, color='#CC3311', linestyle='--', linewidth=1, label=f'Mean = {mean_effect:.2f}')

# Funnel boundaries (95% CI)
se_range = np.linspace(0.01, max(se) * 1.1, 100)
ax.fill_betweenx(se_range, mean_effect - 1.96 * se_range, mean_effect + 1.96 * se_range,
                 alpha=0.1, color='grey', label='95% CI')

ax.set_xlabel("Effect Size (Cohen's d)")
ax.set_ylabel('Standard Error')
ax.invert_yaxis()
ax.legend(frameon=False)

plt.tight_layout()
plt.savefig('figure_07.pdf', format='pdf')
plt.show()
```

### Template 8: Grouped Bar Chart

```python
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams.update({
    'font.family': 'sans-serif', 'font.size': 9, 'axes.labelsize': 10,
    'figure.dpi': 300, 'axes.spines.top': False, 'axes.spines.right': False,
})
CB = ['#0077BB', '#EE7733', '#009988']

categories = ['Teaching', 'Research', 'Service', 'Admin']
group_a = [4.1, 3.5, 3.8, 3.2]
group_b = [3.8, 4.2, 3.5, 3.0]
group_c = [4.3, 3.9, 4.0, 3.5]

x = np.arange(len(categories))
width = 0.25

fig, ax = plt.subplots(figsize=(6.9, 4.5))
ax.bar(x - width, group_a, width, label='Public', color=CB[0], edgecolor='black', linewidth=0.5)
ax.bar(x, group_b, width, label='Private', color=CB[1], edgecolor='black', linewidth=0.5)
ax.bar(x + width, group_c, width, label='National', color=CB[2], edgecolor='black', linewidth=0.5)

ax.set_xlabel('Domain')
ax.set_ylabel('Mean Score (1-5)')
ax.set_xticks(x)
ax.set_xticklabels(categories)
ax.set_ylim(0, 5.5)
ax.legend(frameon=False)

plt.tight_layout()
plt.savefig('figure_08.pdf', format='pdf')
plt.show()
```

---

## R ggplot2 Code Templates

### Template 1: Bar Chart

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    plot.title = element_text(size = 11, face = "bold", hjust = 0),
    axis.title = element_text(size = 10),
    axis.text = element_text(size = 8),
    legend.title = element_text(size = 9),
    legend.text = element_text(size = 8),
    panel.grid.minor = element_blank(),
    panel.grid.major.x = element_blank(),
    strip.text = element_text(size = 9, face = "bold")
  )
cb_palette <- c("#0077BB", "#33BBEE", "#009988", "#EE7733", "#CC3311", "#EE3377")

df <- data.frame(
  group = c("Group A", "Group B", "Group C", "Group D"),
  value = c(4.2, 3.8, 5.1, 4.5),
  se = c(0.3, 0.4, 0.2, 0.5)
)

ggplot(df, aes(x = group, y = value, fill = group)) +
  geom_col(color = "black", linewidth = 0.3, width = 0.7) +
  geom_errorbar(aes(ymin = value - se, ymax = value + se), width = 0.2) +
  scale_fill_manual(values = cb_palette) +
  labs(x = "Group", y = "Score (points)") +
  theme_apa +
  theme(legend.position = "none") +
  coord_cartesian(ylim = c(0, NA))

ggsave("figure_01.pdf", width = 6.9, height = 4.5, units = "in", dpi = 300)
```

### Template 2: Boxplot

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    axis.title = element_text(size = 10), axis.text = element_text(size = 8),
    panel.grid.minor = element_blank(), panel.grid.major.x = element_blank()
  )
cb_palette <- c("#0077BB", "#33BBEE", "#009988", "#EE7733")

set.seed(42)
df <- data.frame(
  type = rep(c("Public", "Private", "Technical", "National"), each = 50),
  score = c(rnorm(50, 3.5, 1), rnorm(50, 4.0, 1), rnorm(50, 3.8, 1), rnorm(50, 4.5, 1))
)

ggplot(df, aes(x = type, y = score, fill = type)) +
  geom_boxplot(alpha = 0.7, outlier.shape = 21, outlier.size = 1.5) +
  scale_fill_manual(values = cb_palette) +
  labs(x = "Institution Type", y = "Satisfaction Score (1-5)") +
  theme_apa +
  theme(legend.position = "none")

ggsave("figure_02.pdf", width = 6.9, height = 4.5, units = "in", dpi = 300)
```

### Template 3: Line Chart (Trend)

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    axis.title = element_text(size = 10), axis.text = element_text(size = 8),
    legend.text = element_text(size = 8), panel.grid.minor = element_blank()
  )

df <- data.frame(
  year = rep(2018:2023, 2),
  enrollment = c(72, 75, 68, 71, 78, 82, 65, 63, 60, 58, 55, 52),
  type = rep(c("Public", "Private"), each = 6)
)

ggplot(df, aes(x = year, y = enrollment, color = type, shape = type)) +
  geom_line(linewidth = 1) +
  geom_point(size = 2.5) +
  scale_color_manual(values = c("#0077BB", "#CC3311")) +
  labs(x = "Year", y = "Enrollment (thousands)", color = NULL, shape = NULL) +
  theme_apa

ggsave("figure_03.pdf", width = 6.9, height = 4.5, units = "in", dpi = 300)
```

### Template 4: Scatter Plot + Regression

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    axis.title = element_text(size = 10), axis.text = element_text(size = 8),
    panel.grid.minor = element_blank()
  )

set.seed(42)
df <- data.frame(ratio = runif(80, 10, 50))
df$satisfaction <- 0.6 * df$ratio + rnorm(80, 0, 5) + 10

ggplot(df, aes(x = ratio, y = satisfaction)) +
  geom_point(color = "#0077BB", alpha = 0.6, size = 1.5) +
  geom_smooth(method = "lm", color = "#CC3311", se = TRUE, linewidth = 1, fill = "#CC3311", alpha = 0.1) +
  labs(x = "Faculty-Student Ratio", y = "Student Satisfaction Score") +
  theme_apa

ggsave("figure_04.pdf", width = 6.9, height = 5.5, units = "in", dpi = 300)
```

### Template 5: Forest Plot

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    axis.title = element_text(size = 10), axis.text = element_text(size = 8),
    panel.grid.minor = element_blank(), panel.grid.major.y = element_blank()
  )

df <- data.frame(
  study = c("Smith (2018)", "Chen (2019)", "Johnson (2020)", "Lee (2021)", "Garcia (2022)", "Overall"),
  effect = c(0.35, 0.42, 0.28, 0.51, 0.38, 0.39),
  ci_lower = c(0.15, 0.22, 0.08, 0.31, 0.18, 0.27),
  ci_upper = c(0.55, 0.62, 0.48, 0.71, 0.58, 0.51),
  is_overall = c(FALSE, FALSE, FALSE, FALSE, FALSE, TRUE)
)
df$study <- factor(df$study, levels = rev(df$study))

ggplot(df, aes(x = effect, y = study, xmin = ci_lower, xmax = ci_upper)) +
  geom_vline(xintercept = 0, linetype = "dashed", color = "grey50") +
  geom_errorbarh(height = 0.2, linewidth = 0.8) +
  geom_point(aes(shape = is_overall, color = is_overall), size = 3) +
  scale_color_manual(values = c("FALSE" = "#0077BB", "TRUE" = "#CC3311")) +
  scale_shape_manual(values = c("FALSE" = 16, "TRUE" = 18)) +
  labs(x = "Effect Size (Cohen's d)", y = NULL) +
  theme_apa +
  theme(legend.position = "none")

ggsave("figure_05.pdf", width = 6.9, height = 4.0, units = "in", dpi = 300)
```

### Template 6: Correlation Heatmap

```r
library(ggplot2)
library(reshape2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(axis.title = element_blank(), axis.text = element_text(size = 8))

labels <- c("Teaching", "Research", "Service", "Satisfaction", "Retention")
corr_matrix <- matrix(c(
  1.00, 0.45, 0.32, 0.67, 0.55,
  0.45, 1.00, 0.28, 0.38, 0.30,
  0.32, 0.28, 1.00, 0.41, 0.35,
  0.67, 0.38, 0.41, 1.00, 0.72,
  0.55, 0.30, 0.35, 0.72, 1.00
), nrow = 5, dimnames = list(labels, labels))

# Lower triangle only
corr_matrix[upper.tri(corr_matrix)] <- NA
melted <- melt(corr_matrix, na.rm = TRUE)

ggplot(melted, aes(x = Var1, y = Var2, fill = value)) +
  geom_tile(color = "white") +
  geom_text(aes(label = sprintf("%.2f", value)), size = 3) +
  scale_fill_gradient2(low = "#2166AC", mid = "#F7F7F7", high = "#B2182B",
                       midpoint = 0, limit = c(-1, 1), name = "r") +
  coord_fixed() +
  theme_apa

ggsave("figure_06.pdf", width = 5.5, height = 5.0, units = "in", dpi = 300)
```

### Template 7: Funnel Plot

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    axis.title = element_text(size = 10), axis.text = element_text(size = 8),
    panel.grid.minor = element_blank()
  )

set.seed(42)
df <- data.frame(
  effect = rnorm(20, 0.4, 0.15),
  se = runif(20, 0.05, 0.25)
)
mean_effect <- mean(df$effect)

ggplot(df, aes(x = effect, y = se)) +
  geom_point(color = "#0077BB", size = 2, alpha = 0.7) +
  geom_vline(xintercept = mean_effect, linetype = "dashed", color = "#CC3311") +
  geom_ribbon(data = data.frame(
    se = seq(0.01, max(df$se) * 1.1, length.out = 100),
    xmin = mean_effect - 1.96 * seq(0.01, max(df$se) * 1.1, length.out = 100),
    xmax = mean_effect + 1.96 * seq(0.01, max(df$se) * 1.1, length.out = 100)
  ), aes(x = NULL, y = se, xmin = xmin, xmax = xmax), alpha = 0.1, fill = "grey") +
  scale_y_reverse() +
  labs(x = "Effect Size (Cohen's d)", y = "Standard Error") +
  theme_apa

ggsave("figure_07.pdf", width = 6.9, height = 5.0, units = "in", dpi = 300)
```

### Template 8: Grouped Bar Chart

```r
library(ggplot2)

theme_apa <- theme_minimal(base_size = 10, base_family = "Arial") +
  theme(
    axis.title = element_text(size = 10), axis.text = element_text(size = 8),
    legend.text = element_text(size = 8), panel.grid.minor = element_blank(),
    panel.grid.major.x = element_blank()
  )
cb_palette <- c("#0077BB", "#EE7733", "#009988")

df <- data.frame(
  domain = rep(c("Teaching", "Research", "Service", "Admin"), 3),
  type = rep(c("Public", "Private", "National"), each = 4),
  score = c(4.1, 3.5, 3.8, 3.2, 3.8, 4.2, 3.5, 3.0, 4.3, 3.9, 4.0, 3.5)
)

ggplot(df, aes(x = domain, y = score, fill = type)) +
  geom_col(position = position_dodge(0.8), width = 0.7, color = "black", linewidth = 0.3) +
  scale_fill_manual(values = cb_palette) +
  labs(x = "Domain", y = "Mean Score (1-5)", fill = NULL) +
  coord_cartesian(ylim = c(0, 5.5)) +
  theme_apa

ggsave("figure_08.pdf", width = 6.9, height = 4.5, units = "in", dpi = 300)
```

---

## LaTeX Figure Inclusion Template

### Single Figure

```latex
\begin{figure}[htbp]
    \centering
    \includegraphics[width=\columnwidth]{figures/figure_01.pdf}
    \caption{\textit{Comparison of Student Satisfaction Scores Across Three Institution Types.}
    Error bars represent 95\% confidence intervals. $N = 1{,}247$.}
    \label{fig:satisfaction}
\end{figure}
```

### Multi-Panel Figure

```latex
\usepackage{subcaption}  % Required in preamble

\begin{figure}[htbp]
    \centering
    \begin{subfigure}[b]{0.48\textwidth}
        \centering
        \includegraphics[width=\textwidth]{figures/figure_02a.pdf}
        \caption{Public universities}
        \label{fig:dist-public}
    \end{subfigure}
    \hfill
    \begin{subfigure}[b]{0.48\textwidth}
        \centering
        \includegraphics[width=\textwidth]{figures/figure_02b.pdf}
        \caption{Private universities}
        \label{fig:dist-private}
    \end{subfigure}
    \caption{\textit{Distribution of Faculty-Student Ratios by Institution Type.}
    Box plots show median, interquartile range, and outliers (circles beyond whiskers).}
    \label{fig:ratio-distribution}
\end{figure}
```

### Full-Page Landscape Figure

```latex
\usepackage{pdflscape}  % Required in preamble

\begin{landscape}
\begin{figure}[htbp]
    \centering
    \includegraphics[width=\linewidth]{figures/figure_wide.pdf}
    \caption{\textit{Comprehensive Correlation Matrix of All Study Variables.}}
    \label{fig:correlation-full}
\end{figure}
\end{landscape}
```
