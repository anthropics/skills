# Architecture — Microservices

Deployment units decomposed by bounded context; independent lifecycles, teams and
scaling. Chosen for large organizations with clear domain boundaries and mature
container/orchestration practice.

## Principles

- **A service owns its data.** Exactly one service owns each datastore; every other
  service reaches it through its API or its events — never through its database.
- **Bounded contexts, not layers.** Service boundaries follow business capabilities
  (`policies`, `billing`, `notifications`); a service that must be deployed with
  another to ship a change is mis-cut.
- **Independent lifecycles are real.** Each service builds, deploys and rolls back
  alone; versioned contracts (OpenAPI, event schemas) keep consumers stable.
- **Failures are designed in.** Timeouts, retries with backoff, circuit breakers and
  idempotent handlers are part of every contract, not afterthoughts.

## Data Flow

External request → gateway/BFF → service owning that capability → that service's
private datastore. Cross-capability data moves as events (or explicit API calls);
orchestrations are sagas with compensated steps, never distributed transactions.
Correlation ids propagate end to end.

## Do Not

- Shared databases or shared libraries carrying domain logic between services — both
  re-couple what the network decoupled.
- Synchronous call chains deeper than two hops; they turn one slow service into an
  outage.
- A release that requires locking-step deployment of multiple services.
- Distributed transactions; use sagas with explicit compensation.
