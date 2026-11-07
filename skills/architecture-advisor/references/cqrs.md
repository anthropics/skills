# Architecture — CQRS

Separate read and write models: commands mutate state through the domain, queries
project optimized read shapes. Chosen for high-throughput systems and complex
reporting where reads and writes have genuinely different shapes and scaling needs.

## Principles

- **Commands and queries are different pipelines.** A command changes state and
  returns at most an acknowledgment/id; a query returns data and never mutates.
- **The write model guards invariants.** All business rules live in the command side;
  the read side is allowed to denormalize freely for query performance.
- **Projections are disposable.** Read models are derived state — rebuildable from
  the source of truth; losing them loses no business data.
- **Eventual consistency is explicit.** Where the read side lags the write side, the
  API and UI say so; no hidden synchronizations.

## Data Flow

Command → validation → domain aggregate applies the change → new state (and/or domain
events) persisted → projections update read models. Query → read model directly
(no domain involvement) → response. The two sides share no write path and no write
model types.

## Do Not

- CRUD-through-CQRS: splitting a model that has one shape and low contention — it is
  tax without benefit.
- Business rules in projections; if a query needs a rule, the rule belongs to the
  write side or the projection is wrong.
- Bidirectional coupling between read and write models (shared ORM entities count).
- Introducing CQRS before measuring that reads/writes actually contend.
