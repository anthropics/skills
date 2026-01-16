## Instructions

XY charts display data using X and Y axes, supporting bar charts, line charts, and area charts.

### Syntax

- Use `xychart-beta` keyword
- Title: `title Chart Title`
- X-axis: `x-axis [categories]`
- Y-axis: `y-axis "Label" [min, max]`
- Series: `bar [values]` or `line [values]` or `area [values]`
- Multiple series can be defined

### Example

```mermaid
xychart-beta
    title "Sales Performance"
    x-axis [Jan, Feb, Mar, Apr, May, Jun]
    y-axis "Sales" 0 --> 1000
    bar [500, 600, 750, 800, 950, 1000]
    line [450, 550, 700, 750, 900, 950]
```
