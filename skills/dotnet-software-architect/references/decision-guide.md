# Decision Guide — choosing a .NET architecture

The job here is to match **forces** (drivers) to a **style**, then say out loud which
styles you rejected and why. The reference codebases make the trade-offs concrete:
the Clean Architecture templates are praised for clean seams but carry ceremony the
domain must justify; a flat layered app is fast but drifts anemic; eShop's
microservices are canonical but demand Aspire/observability/outbox machinery; the
modular monolith costs discipline and project count. There is no free lunch — pick
the cost you can afford.

## Step 1 — Surface the drivers

Ask only what you need; assume sensible defaults and state them. The drivers that
actually flip the decision:

- **Domain complexity** — invariants and rules, or mostly CRUD over forms?
- **Change rate** — will the rules churn, or is this stable?
- **Lifespan** — throwaway/internal tool vs a system that lives 5–10 years?
- **Team** — size, seniority, number of teams touching the code?
- **Scale** — independent scaling of parts? real throughput pressure?
- **Operational maturity** — can the org run containers, service discovery,
  distributed tracing, multiple pipelines? (Aspire lowers but doesn't erase this.)
- **Consistency** — strong/transactional, or is eventual consistency acceptable?
- **Hosting reality** — Azure/AWS/on-prem, IIS legacy, container platform?

## Step 2 — Map drivers to a style

```
Simple domain, small team, velocity matters
  → Single Clean-lite solution: Web + Application + Infrastructure + Domain,
    feature folders, IApplicationDbContext, minimal APIs. Don't over-build.

Non-trivial domain, one deployable, want clean seams + future options
  → Modular monolith (module-per-bounded-context, each with its own
    Domain/Application/Infrastructure projects + ArchTests).      ← best default

Genuinely complex domain with real invariants/rules
  → Rich-domain Clean Architecture inside the relevant module(s): aggregates with
    private setters, IBusinessRule/guards, value objects, typed IDs, domain events.

Real org/scaling pressure: many teams, independent deploy/scale, fault isolation
  → Microservices: Aspire AppHost + ServiceDefaults, YARP gateway, per-service DB,
    EventBus + transactional outbox. Prerequisite: clean modules to split along.

Reads and writes diverge sharply (reporting vs transactional)
  → CQRS split at the persistence level (EF for writes, Dapper/raw SQL projections
    for reads — the MM-DDD approach), not necessarily separate stores.

Product extended by plugins/third parties
  → Abstractions in a contracts package, implementations discovered via DI;
    strong-name the public contract assemblies and version them deliberately.
```

## Step 3 — Trade-off table

| Style | Buys you | Costs you | Ideal when | Avoid when |
|---|---|---|---|---|
| **Clean-lite (4 projects, feature folders)** | Speed, low ceremony, compiler-enforced direction | Tends anemic; rules scatter as complexity grows | CRUD-ish apps, small teams | Domain has rich, churning invariants |
| **Modular monolith** | Service-grade seams, single deploy/transaction, cheap future extraction | Discipline, many projects, per-module ArchTests to maintain | Most non-trivial systems; the safe default | True independent-scale/multi-team pressure already real |
| **Rich-domain Clean Arch (full DDD tactical)** | Invariants protected, domain testable in isolation | Highest modeling cost; EF mapping friction | Complex, long-lived core domain | Simple CRUD — pure overhead |
| **Microservices (Aspire/eShop-style)** | Independent deploy/scale, team autonomy, fault isolation | Ops complexity, network failure modes, distributed data, outbox machinery | Many teams, real scale, container-ready org | Before boundaries are proven; small team |
| **CQRS (persistence-level)** | Reads & writes optimize independently | Two data paths to maintain | Read/write shapes diverge sharply | Symmetric, simple models |
| **MediatR everywhere** | Uniform cross-cutting via behaviours, use-case-per-class | Indirection, library coupling | Teams that value the uniformity | Tiny apps; teams that find it magic |

## Step 4 — Default recommendations (the honest priors)

- For a typical business backend with some real logic: **modular monolith** —
  modules per bounded context, each with Domain/Application/Infrastructure projects,
  a shared BuildingBlocks kernel, integration events between modules, NetArchTest at
  both levels, Central Package Management. This keeps the microservices and full-DDD
  doors open without paying for either prematurely.
- Apply **full DDD tactical patterns only in the module(s) where the domain is
  genuinely complex** — a rich `Payments` module can sit next to a CRUD
  `Administration` module (MM-DDD literally does this).
- Treat **microservices** as an extraction you earn, not a starting point. When you
  do extract, copy eShop's ServiceDefaults pattern (resilience + OTel in one place)
  and never skip the outbox for cross-service events.
- Regardless of style: **separate projects for Domain and Application** (compiler
  enforcement is free), **Central Package Management**, and **at least one
  architecture test project**. These three are cheap and prevent the most common
  decay.

## Step 5 — Name the roads not taken

Whatever you recommend, explicitly state the 1–2 alternatives you rejected and the
driver that ruled them out (e.g. "Not microservices: single team, no
independent-scale need, boundaries unproven — a modular monolith gives the same
modularity without the ops tax; we can extract `Billing` later if load demands").
Capture it in an ADR (`adr-template.md`) — the rejected options are the part teams
most need recorded.
