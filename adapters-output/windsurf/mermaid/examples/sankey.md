## Instructions

Sankey diagrams visualize flow and relationships between entities, showing the magnitude of flows between nodes.

### Syntax

- Use `sankey-beta` keyword
- Flows: `Source -->|Value| Target`
- Values should be numeric
- Multiple flows can originate from or target the same node

### Example

```mermaid
sankey-beta
    Energy Production -->|100| Electricity
    Energy Production -->|30| Heat
    Electricity -->|80| Residential
    Electricity -->|20| Industrial
    Heat -->|25| Residential
    Heat -->|5| Industrial
```
