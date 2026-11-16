# Architecture — Modular Monolith

One deployable, internally split into modules with enforced boundaries and explicit
public surfaces. Chosen for most products until scale proves otherwise: microservice
benefits (boundaries, ownership) without the distributed tax.

## Principles

- **Modules are the unit of ownership.** Each module owns its data, its public API
  and its tests; the build fails — not the code review — when a boundary is crossed.
- **Public surfaces are explicit.** A module exports a narrow API (published types
  and functions); everything else is internal, unreachable from sibling modules.
- **No shared database tables.** Each module owns its schema (separate schemas or
  table prefixes); cross-module reads go through the owning module's API.
- **Extract-ready.** A module that later needs independent scaling can be lifted into
  a service without rewriting its internals — because its communication already goes
  through its API.

## Data Flow

Inbound request → the module owning that capability → its internal layers freely →
response. Cross-module calls go only through published APIs; cross-module data
replication happens via in-process events. One process, one database, enforced seams.

## Do Not

- Importing another module's internals "just this once" — every exception becomes
  permanent.
- Cross-module JOINs or shared tables; they fuse modules at the data layer.
- A `common` module that accumulates domain logic and everything's dependencies.
- Reaching for microservices while the team is small and the boundaries are still
  moving; the monolith absorbs change cheaper.
