# Architecture — Layered (Traditional)

Presentation → Business → Persistence; calls go downward only. Chosen for CRUD
applications, simple monoliths and rapid delivery where the domain is stable and
the value is in the workflow, not in the model.

## Principles

- **Downward dependencies only.** A layer may call the layer directly beneath it;
  skip-layers and upward calls are defects, not shortcuts.
- **The layer is the contract.** Each layer exposes a narrow, documented interface;
  layers communicate through it, never by reaching into each other's internals.
- **One responsibility per layer.** Presentation renders and validates input;
  business decides; persistence stores and queries. Business logic never leaks into
  SQL or templates.

## Data Flow

Request enters at Presentation (controller/CLI/queue listener) → validated and mapped
to a Business call → Business applies rules using Persistence interfaces → Persistence
returns rows/entities → results flow back up, mapped at each boundary. Cross-cutting
concerns (auth, logging, transactions) enter at the outermost layer and travel with
the request context.

## Do Not

- Business rules in controllers, SQL queries or stored procedures — the business layer
  must stay the only place a rule can live.
- Shared "utils" layers that everything depends on; they become a coupling sink.
- Circular references between modules; if two layers need each other, the boundary is
  drawn in the wrong place.
- Reaching around the persistence interface with native queries from business code.
