## Instructions

Treemap diagrams (beta) visualize hierarchical data as nested rectangles, where the size of each rectangle represents a value.

### Syntax

- Use `treemap-beta` keyword
- Title: `title Chart Title`
- Hierarchy: Indentation determines parent-child relationships
- Values: `Label : Value`
- Colors can be applied to different levels

### Example

```mermaid
treemap-beta
    title Sales by Region
    Region A : 500
        Product A1 : 200
        Product A2 : 150
        Product A3 : 150
    Region B : 300
        Product B1 : 120
        Product B2 : 180
    Region C : 200
        Product C1 : 100
        Product C2 : 100
```
