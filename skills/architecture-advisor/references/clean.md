# Architecture — Clean

Entities → Use Cases → Interface Adapters → Frameworks/Drivers; outer layers depend on
inner, never reverse. Chosen for large enterprise systems with multiple delivery
mechanisms where the business rules must outlive frameworks, databases and UIs.

## Principles

- **The dependency rule is absolute.** Source code dependencies point toward the
  entities; nothing in an inner circle knows anything about an outer circle.
- **Entities carry enterprise-wide business rules.** Use cases carry
  application-specific rules and orchestrate entities; both are framework-free.
- **Boundaries cross via interfaces and DTOs.** Outer layers call inner ones through
  interfaces defined by the inner layer; data crosses as simple structures owned by
  the inner layer.
- **Frameworks are details.** Web, DB, DI and messaging live in the outermost ring
  and are replaceable without touching entities or use cases.

## Data Flow

A request arrives at the delivery mechanism (outermost) → a controller maps it into a
use-case input structure → the interactor (use case) executes business rules with
entities → output flows back through an output port into a presenter → the delivery
mechanism renders it. Each arrow crosses a boundary in the inward-allowed direction,
or through an interface the inner side owns.

## Do Not

- Reference frameworks, ORM models or HTTP types from entities or use cases.
- Let the database schema dictate the entities — mapping belongs to the outer ring.
- Skip the presenter boundary "temporarily"; leaking delivery formats into use cases
  is how the dependency rule dies.
- Grow a generic "shared" ring that all layers import; it dissolves the circles.
