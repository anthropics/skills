## Instructions

Radar charts (beta) display multivariate data on axes starting from the same point, useful for comparing multiple items across different dimensions.

### Syntax

- Use `radar-beta` keyword
- Title: `title Chart Title`
- Axes: `axis AxisName [min, max]`
- Series: `series SeriesName [values]`
- Values should match the number of axes

### Example

```mermaid
radar-beta
    title Performance Comparison
    axis Performance [0, 100]
    axis Quality [0, 100]
    axis Speed [0, 100]
    axis Cost [0, 100]
    
    series Product A [80, 90, 70, 60]
    series Product B [70, 85, 90, 75]
```
