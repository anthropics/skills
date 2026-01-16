## Instructions

Quadrant charts display items in a 2x2 grid based on two criteria, useful for prioritization and analysis.

### Syntax

- Use `quadrantChart` keyword
- Title: `title Chart Title`
- X-axis: `x-axis Low Label --> High Label`
- Y-axis: `y-axis Low Label --> High Label`
- Quadrants: `quadrant-1 Label`, `quadrant-2 Label`, `quadrant-3 Label`, `quadrant-4 Label`
- Items: `Item Name: [x, y]`

### Example

```mermaid
quadrantChart
    title Product Prioritization
    x-axis Low Effort --> High Effort
    y-axis Low Impact --> High Impact
    quadrant-1 Should Do
    quadrant-2 Must Do
    quadrant-3 Won't Do
    quadrant-4 Nice to Have
    Feature A: [0.3, 0.8]
    Feature B: [0.7, 0.9]
    Feature C: [0.2, 0.3]
    Feature D: [0.8, 0.2]
```
