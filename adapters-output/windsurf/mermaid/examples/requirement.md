## Instructions

Requirement diagrams model system requirements and their relationships, showing how requirements relate to each other and to system elements.

### Syntax

- Use `requirementDiagram` keyword
- Requirements: `requirement RequirementID { }`
- Requirement types: `functionalRequirement`, `interfaceRequirement`, `performanceRequirement`, `physicalRequirement`, `designConstraint`
- Relationships:
  - `contains` - Parent-child relationship
  - `satisfies` - Requirement satisfies element
  - `verifies` - Element verifies requirement
  - `refines` - Requirement refines another
  - `traces` - Trace relationship

### Example

```mermaid
requirementDiagram
    requirement R1 {
        id: 1
        text: System must handle 1000 concurrent users
        risk: high
        verifymethod: test
    }
    requirement R2 {
        id: 2
        text: System must respond within 2 seconds
        risk: medium
        verifymethod: test
    }
    
    element E1 {
        type: System
        docref: docs/system.md
    }
    
    R1 satisfies E1
    R2 satisfies E1
```
