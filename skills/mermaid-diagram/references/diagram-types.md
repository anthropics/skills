# Mermaid Diagram Types Reference

A quick syntax reference for the most common Mermaid diagram types. For the full
specification see <https://mermaid.js.org>. Each snippet below validates cleanly
with `scripts/validate.py`.

## Flowchart

Best for processes, decision trees, and workflows.

```mermaid
flowchart TD
    A[Start] --> B{Authenticated?}
    B -->|Yes| C[Load dashboard]
    B -->|No| D[Show login]
    D --> E["Enter credentials"]
    E --> B
    C --> F[End]
```

- Directions: `TD`/`TB` (top-down), `BT` (bottom-up), `LR` (left-right), `RL`.
- Node shapes: `A[rect]`, `B(rounded)`, `C([stadium])`, `D{diamond}`,
  `E((circle))`, `F[/parallelogram/]`.
- Edges: `-->` arrow, `---` line, `-.->` dotted, `==>` thick, `-->|label|` labeled.
- Group with `subgraph Name ... end`.

## Sequence Diagram

Best for interactions between participants over time.

```mermaid
sequenceDiagram
    participant U as User
    participant API
    participant DB
    U->>API: POST /login
    API->>DB: SELECT user
    DB-->>API: row
    alt valid password
        API-->>U: 200 + token
    else invalid
        API-->>U: 401
    end
```

- Arrows: `->>` solid, `-->>` dashed (reply), `-x` lost message.
- Blocks: `loop`, `alt`/`else`, `opt`, `par`, `critical`, `rect` — each closed by `end`.
- Lifelines: `activate X` / `deactivate X` (or `+`/`-` shorthand on arrows).

## Class Diagram

Best for object-oriented structure.

```mermaid
classDiagram
    class Animal {
        +String name
        +int age
        +makeSound() void
    }
    class Dog {
        +fetch() void
    }
    Animal <|-- Dog
```

- Relationships: `<|--` inheritance, `*--` composition, `o--` aggregation,
  `-->` association, `..>` dependency.
- Visibility: `+` public, `-` private, `#` protected.

## State Diagram

Best for state machines.

```mermaid
stateDiagram-v2
    [*] --> Idle
    Idle --> Running : start
    Running --> Paused : pause
    Paused --> Running : resume
    Running --> [*] : stop
```

- `[*]` marks start and end states.
- Composite states: `state Name { ... }`.

## Entity Relationship Diagram

Best for database schemas.

```mermaid
erDiagram
    CUSTOMER ||--o{ ORDER : places
    ORDER ||--|{ LINE_ITEM : contains
    CUSTOMER {
        int id PK
        string name
        string email
    }
    ORDER {
        int id PK
        int customer_id FK
    }
```

- Cardinality: `||` exactly one, `o{` zero-or-many, `|{` one-or-many.
- Keys: `PK`, `FK`, `UK` in the attribute block.

## Gantt Chart

Best for project schedules.

```mermaid
gantt
    title Project Plan
    dateFormat YYYY-MM-DD
    section Design
    Wireframes      :a1, 2025-01-01, 5d
    Review          :after a1, 2d
    section Build
    Implementation  :2025-01-10, 10d
```

## Mindmap

Best for hierarchical brainstorming around one idea.

```mermaid
mindmap
  root((Product))
    Discovery
      Interviews
      Surveys
    Delivery
      MVP
      Launch
```

## Pie Chart

Best for proportions of a whole.

```mermaid
pie title Traffic sources
    "Organic" : 45
    "Paid" : 30
    "Referral" : 25
```
