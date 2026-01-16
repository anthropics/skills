## Instructions

Entity Relationship (ER) diagrams model the structure of a database by showing entities, their attributes, and relationships between them.

### Syntax

- Use `erDiagram` keyword
- Entities: `ENTITY_NAME { }`
- Attributes: `type attribute_name`
- Relationships: `ENTITY1 ||--o{ ENTITY2 : "relationship_label"`
- Cardinality:
  - `||--o{` - One to many
  - `||--||` - One to one
  - `}o--o{` - Many to many
  - `||--o|` - One to zero or one
  - `}o--||` - Many to one

### Example

```mermaid
erDiagram
    CUSTOMER ||--o{ ORDER : places
    ORDER ||--|{ ORDER_LINE : contains
    PRODUCT ||--o{ ORDER_LINE : "ordered in"
    
    CUSTOMER {
        int customer_id PK
        string name
        string email
    }
    ORDER {
        int order_id PK
        date order_date
        int customer_id FK
    }
    PRODUCT {
        int product_id PK
        string name
        decimal price
    }
    ORDER_LINE {
        int order_id FK
        int product_id FK
        int quantity
    }
```
