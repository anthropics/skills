# Architecture Decision Records (ADR)

An ADR captures **why** a decision was made — the single most valuable and most-often-
lost piece of architectural knowledge. Produce one for any non-trivial choice: style
selection, a boundary, a persistence strategy, introducing/extracting a service, a
cross-cutting pattern. Keep it short; the value is the *context and consequences*,
not length.

## Format (use this exact structure)

```markdown
# ADR-NNNN: <short decision title>

- Status: Proposed | Accepted | Superseded by ADR-XXXX | Deprecated
- Date: YYYY-MM-DD
- Deciders: <names/roles>

## Context
The forces at play: the problem, the relevant drivers (domain complexity, team,
scale, ops maturity, consistency, lifespan, hosting reality), and any constraints.
State facts, not the conclusion. Someone reading this in two years should understand
the situation without asking you.

## Decision
The choice, stated plainly and actively: "We will …". Include the concrete shape
(style, solution/project layout, the boundary, the pattern) so it's unambiguous.

## Alternatives considered
The real options and why each was rejected. This is the heart of the ADR — the roads
not taken. One short paragraph or bullet each, tied to the driver that ruled it out.

## Consequences
What becomes easier and what becomes harder. Include the costs, the technical debt
or risk accepted, the new constraints, and the conditions under which we'd revisit
this. Be honest about the downside — an ADR with no negative consequences is hiding
something.
```

## Worked example

```markdown
# ADR-0004: Use the transactional outbox for all cross-module events

- Status: Accepted
- Date: 2026-06-10
- Deciders: Platform team

## Context
Our modular monolith (Billing, Customers, Notifications modules) communicates via
integration events on an in-process bus today, but Notifications is about to be
extracted to its own service, and Billing events will cross a process boundary over
RabbitMQ. Events are currently published after SaveChangesAsync — if the process
crashes between commit and publish, the event is lost; if publish succeeds and the
commit fails, we emit a phantom. Billing events drive invoicing emails and payment
reconciliation, so losses are customer-visible. Team has EF Core experience; no
existing message-broker operational experience beyond dev.

## Decision
We will persist every integration event to an outbox table (EventId, Type, Content,
OccurredOn, ProcessedDate) inside the same EF Core transaction as the business
change, in each module's own schema. A background processor (hosted service) reads
unprocessed entries, publishes to the bus, and marks them processed; handlers are
idempotent keyed on EventId. This follows the IntegrationEventLogEF pattern from
eShop / the outbox job from modular-monolith-with-ddd.

## Alternatives considered
- Publish-after-commit (status quo): rejected — loses events on crash; the
  reconciliation bugs we already saw in staging are this failure mode.
- Distributed transaction (TransactionScope across DB + broker): rejected — our
  broker doesn't enlist; 2PC operational complexity we can't support.
- Change Data Capture (Debezium-style): rejected for now — strongest guarantees but
  introduces a Kafka/connector platform the team can't operate yet. Revisit if event
  volume outgrows the polling processor.

## Consequences
+ No lost or phantom events: state change and event persist atomically.
+ Works identically in-process today and over RabbitMQ after extraction — the
  extraction no longer changes delivery semantics.
- Adds an outbox table per module and a processor loop; publish latency is now
  polling-interval bound (acceptable: notifications are not latency-critical).
- Consumers must be idempotent (at-least-once delivery); we accept this and key on
  EventId.
- Revisit if: event volume makes polling a bottleneck → move to CDC; or if a module
  needs sub-second event latency.
```

## Tips

- Number ADRs sequentially; never edit an accepted ADR's decision — supersede it
  with a new one and link them. The history *is* the value.
- Write Context before you've written the Decision elsewhere, so it stays
  driver-focused rather than a justification.
- Keep the files in the repo (e.g. `docs/adr/`), close to the code they govern.
