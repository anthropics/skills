## Instructions

Block diagrams represent systems as interconnected blocks, showing the structure and relationships between components.

### Syntax

- Use `block-beta` keyword
- Blocks: `block BlockName`
- Connections: `Block1 --> Block2`
- Labels: `Block1 -->|Label| Block2`
- Groups: `blockGroup GroupName { }`

### Example

```mermaid
block-beta
    block Input
    block Process
    block Output
    
    Input -->|Data| Process
    Process -->|Result| Output
```
