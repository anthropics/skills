## Instructions

Class diagrams represent the structure of a system by showing classes, their attributes, methods, and relationships.

### Syntax

- Use `classDiagram` keyword
- Class definition: `class ClassName { }`
- Attributes: `+public`, `-private`, `#protected`
- Methods: `+methodName()`, `-privateMethod()`
- Relationships:
  - `<|--` - Inheritance
  - `*--` - Composition
  - `o--` - Aggregation
  - `-->` - Association
  - `..>` - Dependency
- Interfaces: `<<interface>>` or `<<Interface>>`

### Example

```mermaid
classDiagram
    class Animal {
        +String name
        +int age
        +eat()
        +sleep()
    }
    class Dog {
        +String breed
        +bark()
    }
    class Cat {
        +meow()
    }
    
    Animal <|-- Dog
    Animal <|-- Cat
```
