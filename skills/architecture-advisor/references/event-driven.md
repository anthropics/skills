# Architecture — Event-Driven

State changes are emitted as events; consumers react asynchronously. Chosen for
real-time systems, audit trails and decoupled workflows where producers must not know
their consumers.

## Principles

- **Events are facts.** Named in past tense (`PolicyRenewed`), immutable, carrying
  the data consumers need — consumers never call back the producer to reconstruct
  context.
- **Producers are ignorant of consumers.** A producer publishes because the fact
  happened; adding a consumer changes no producer code.
- **Handlers are idempotent.** Every consumer tolerates duplicates (at-least-once
  delivery is the default); dedup keys and idempotent writes are part of the handler
  contract.
- **Schemas are contracts.** Event payloads are versioned; breaking changes ship as
  new versions, not mutations.

## Data Flow

Command processing commits state and publishes events (ideally in the same
transaction — transactional outbox) → broker distributes → each consumer processes
independently, advancing its own position. Sagas/process managers coordinate
multi-step workflows by reacting to events and emitting commands. Every event carries
correlation and causation ids.

## Do Not

- Request/response semantics smuggled through events (publish-then-wait-for-reply as
  a hidden sync call) — name it a saga or use RPC.
- Consumers reaching into the producer's database to "complete" the event.
- Unversioned evolving payloads; fat events with everything "just in case".
- Event chains with no observability: without tracing ids, debugging becomes
  archaeology.
