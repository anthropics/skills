# Architecture Options Catalog

Each option lists what it is, when it fits, its trade-offs, and when NOT to use it.
Detail files (principles, data flow, Do-Nots) live next to this catalog, one per core
pattern.

## Core system patterns

### Layered Architecture (Traditional) — [detail](layered.md)
- **What:** Presentation → Business → Persistence; calls go downward only.
- **Best for:** CRUD applications, simple monoliths, rapid prototyping.
- **Trade-offs:** Low complexity; tight coupling; hard to test in isolation.
- **When NOT to use:** Complex domain logic that changes independently of delivery
  mechanisms; when you need to swap infrastructure (DB, transport) freely.

### Hexagonal Architecture (Ports & Adapters) — [detail](hexagonal.md)
- **What:** Core domain logic isolated behind Ports (interfaces); Adapters implement
  them for the outside world (DB, HTTP, CLI).
- **Best for:** Complex business logic, long-term maintainability, DDD.
- **Trade-offs:** Higher initial complexity; more files; steeper learning curve.
- **When NOT to use:** Thin CRUD layers where the "domain" is the database schema;
  throwaway prototypes.

### Clean Architecture — [detail](clean.md)
- **What:** Entities → Use Cases → Interface Adapters → Frameworks/Drivers; outer
  layers depend on inner, never reverse.
- **Best for:** Large enterprise systems, multiple delivery mechanisms.
- **Trade-offs:** Significant boilerplate; risk of over-engineering.
- **When NOT to use:** Small services; teams without the discipline to keep the
  dependency rule (it decays into Layered quickly).

### CQRS (Command Query Responsibility Segregation) — [detail](cqrs.md)
- **What:** Separate read and write models; commands mutate, queries project.
- **Best for:** High-throughput systems, complex reporting needs.
- **Trade-offs:** Eventual consistency; duplicated logic; operational complexity.
- **When NOT to use:** When read and write sides are the same shape (most CRUD);
  no real need for independent scaling of reads/writes.

### Microservices — [detail](microservices.md)
- **What:** Deployment units decomposed by bounded context; independent lifecycles.
- **Best for:** Large teams, independent scaling, polyglot persistence.
- **Trade-offs:** Network latency; distributed transactions; DevOps overhead.
- **When NOT to use:** Small teams; unclear domain boundaries; no container/orchestration
  maturity — a modular monolith delivers most benefits without the tax.

### Modular Monolith — [detail](modular-monolith.md)
- **What:** One deployable, internally split into modules with enforced boundaries
  and explicit public surfaces.
- **Best for:** Most products until scale proves otherwise; teams of 1-15.
- **Trade-offs:** Discipline needed to prevent boundary erosion; single-runtime
  scaling limits.
- **When NOT to use:** Modules with radically different scaling or availability
  requirements; hard team ownership borders that CI cannot enforce.

### Event-Driven Architecture — [detail](event-driven.md)
- **What:** State changes emitted as events; consumers react asynchronously.
- **Best for:** Real-time systems, audit trails, decoupled workflows.
- **Trade-offs:** Harder to debug; eventual consistency; event schema versioning.
- **When NOT to use:** When callers need synchronous answers; low event volume
  where a direct call plus an outbox table is enough.

### Functional Core / Imperative Shell
- **What:** Pure decision-making core; side effects (I/O) pushed to a thin shell.
- **Best for:** Data pipelines, transformations, highly testable business logic.
- **Trade-offs:** Requires discipline; less OOP-friendly; mapping layers at edges.
- **When NOT to use:** Effect-dominated code (thin CRUD controllers) where the core
  would be empty.

## Specialized patterns (overlays — choose independently of the core pattern)

### API styles
| Style | Best for | Avoid when |
|---|---|---|
| REST | Resource-oriented CRUD, public APIs | Fine-grained field selection or many round trips needed |
| GraphQL | Client-specified fields, aggregated views | Simple resources; strict caching requirements |
| gRPC | Internal service-to-service, high throughput, streaming | Browser-facing public APIs (needs a gateway) |
| WebSocket | Real-time bidirectional (chat, live dashboards) | Request/response semantics suffice |

### Frontend integration
| Pattern | Best for | Avoid when |
|---|---|---|
| MVC | Traditional server-rendered web | Heavy client-side state |
| MVVM | Reactive UIs with two-way binding | Simple static views |
| Clean + Redux | Unidirectional data flow, complex app state | Small apps (ceremony outweighs benefit) |
| BFF | API tailored to one UI's needs | Single client type |

### Data persistence
| Pattern | Best for | Avoid when |
|---|---|---|
| Repository | Abstracting data access behind a domain interface | The ORM already is the abstraction and leaks are acceptable |
| Unit of Work | Transactional consistency across aggregates | Single-aggregate transactions only |
| Event Sourcing | Full audit trail, temporal queries | The team cannot own event versioning and replays |
| CQRS | Read/write shapes diverge significantly | They do not (see above) |

## Selection guidance

Choose at most ONE core system pattern per service and justify with: complexity,
team size, scalability needs. If unsure between two, write both as alternatives in
the design document with pros/cons and pick one — the reviewer challenges the
justification, not the choice itself.
