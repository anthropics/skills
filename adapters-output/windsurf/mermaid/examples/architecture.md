## Instructions

Architecture diagrams (beta) visualize system architectures, showing components and their relationships.

### Syntax

- Use `architecture-beta` keyword
- Components: `component ComponentName`
- Connections: `Component1 --> Component2`
- Labels: `Component1 -->|Label| Component2`
- Groups: `group GroupName { }`

### Example

```mermaid
architecture-beta
    component Frontend
    component API
    component Database
    component Cache
    
    Frontend -->|HTTP| API
    API -->|Query| Database
    API -->|Read/Write| Cache
```
