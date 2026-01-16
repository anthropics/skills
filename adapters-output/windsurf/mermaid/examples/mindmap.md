## Instructions

Mindmaps visualize hierarchical information, showing relationships between concepts in a tree-like structure.

### Syntax

- Use `mindmap` keyword
- Root: `root((Root Node))`
- Nodes: `NodeName[Label]` or `NodeName((Label))`
- Hierarchy: Indentation determines parent-child relationships
- Icons: `fa:fa-icon-name` for Font Awesome icons

### Example

```mermaid
mindmap
    root((Mermaid))
        Flowcharts
            Basic Flowchart
            Subgraph
            Styling
        Sequence Diagrams
            Participants
            Messages
            Activations
        Class Diagrams
            Classes
            Relationships
            Interfaces
        Other Diagrams
            State Diagrams
            ER Diagrams
            Gantt Charts
```
