# Pattern Catalog (.NET, evidence-backed)

Every pattern below was observed in real, working reference code: the
modular-monolith-with-DDD reference ("MM-DDD"), Jason Taylor's Clean Architecture
template ("JT"), Ardalis's Clean Architecture template ("Ardalis"), Microsoft's
eShop (Aspire microservices) and eShopOnWeb (clean monolith). Each entry gives the
**shape** it actually takes in C#, the **trade-off**, and whether it's
**recommended** or an **anti-pattern**. Use these as concrete templates, not theory.

## Table of contents
1. Clean Architecture layers (project-per-layer)
2. CQRS via MediatR + pipeline behaviours
3. DDD tactical patterns — aggregates, business rules, value objects, typed IDs
4. Result<T> vs exceptions; Specification pattern
5. Domain events & integration events (in-process vs cross-service)
6. Transactional outbox (IntegrationEventLogEF)
7. Modular monolith (module-per-context, enforced)
8. Microservices topology (Aspire, YARP, EventBus)
9. Persistence with EF Core
10. Central Package Management & solution conventions
11. API design patterns
12. Architecture enforcement (NetArchTest / ArchUnitNET)
13. Anti-patterns observed

---

## 1. Clean Architecture layers (project-per-layer)

**Observed shape** — both dominant templates use separate *projects* per layer, so
the compiler enforces direction:

```
JT:      Domain ← Application ← Infrastructure / Web   (+ AppHost, ServiceDefaults)
Ardalis: Core   ← UseCases    ← Infrastructure / Web   (+ AspireHost, ServiceDefaults)
eShopOnWeb: ApplicationCore ← Infrastructure ← Web / PublicApi
```

- **Domain/Core** holds entities, value objects, events, exceptions, domain
  interfaces — references nothing.
- **Application/UseCases** holds commands/queries/handlers and abstractions like
  `IApplicationDbContext` — references only Domain.
- **Infrastructure** implements the abstractions (EF Core DbContext, identity,
  email) — references Application.
- **Web** is composition root: endpoints, DI wiring — references Application and
  Infrastructure (for registration only).

**Key .NET-specific fact:** the project-reference graph *is* the dependency rule. If
`Domain.csproj` has no references, domain code physically cannot use EF Core. That's
stronger than package conventions — exploit it.

**Trade-off:** more projects to navigate; the payoff is mechanical enforcement and
independently testable layers. **Status:** Recommended baseline for any non-trivial
.NET backend.

---

## 2. CQRS via MediatR + pipeline behaviours

**Observed shape (JT):** every use case is a `record` command/query implementing
`IRequest<T>`, with a colocated handler:

```csharp
public record CreateTodoItemCommand : IRequest<int>
{
    public int ListId { get; init; }
    public string? Title { get; init; }
}

public class CreateTodoItemCommandHandler(IApplicationDbContext context)
    : IRequestHandler<CreateTodoItemCommand, int> { ... }
```

Organized **by feature**: `Application/TodoItems/Commands/CreateTodoItem/` contains
the command, handler, and its FluentValidation validator together.

**Cross-cutting concerns live in `IPipelineBehavior<,>`**, not in handlers. JT ships
five: `ValidationBehaviour` (runs all FluentValidation validators, throws on
failure), `AuthorizationBehaviour`, `LoggingBehaviour`, `PerformanceBehaviour`,
`UnhandledExceptionBehaviour`. Handlers stay pure orchestration.

**Trade-off:** indirection (where does this request go?) and a MediatR dependency, in
exchange for uniform cross-cutting handling and one-use-case-one-class. A valid
alternative seen in Ardalis's minimal flavor: plain handler classes/endpoints without
MediatR — same shape, less magic. **Status:** Recommended; the *use-case-per-class +
behaviours-for-cross-cutting* idea matters more than the specific library.

---

## 3. DDD tactical patterns — aggregates, business rules, value objects, typed IDs

**Rich aggregate (MM-DDD `Meeting`, eShop `Order`):** class with **private fields/
setters**, a **private parameterless constructor** (for EF), **static factory or
internal `CreateNew`** for construction, and behavior methods that mutate state only
after checking invariants. Marked with `IAggregateRoot`.

**Business rules as objects (MM-DDD):** the most distinctive .NET evidence — each
invariant is a class:

```csharp
public interface IBusinessRule
{
    bool IsBroken();
    string Message { get; }
}
// in Entity base:
protected void CheckRule(IBusinessRule rule)
{
    if (rule.IsBroken()) throw new BusinessRuleValidationException(rule);
}
```

Rules get names like `CommentCannotBeLikedByTheSameMemberMoreThanOnceRule` — the
rule set is explicit, individually unit-testable, and greppable, instead of `if`s
buried in services. (Ardalis achieves lighter-weight guarding with
`Ardalis.GuardClauses` at method entry; both are valid — rules-as-objects for
domain invariants, guard clauses for argument validation.)

**Value objects:** immutable types with value equality — a `ValueObject` base class
(MM-DDD, eShop SeedWork) or C# `record`s. Examples observed: `MoneyValue`,
`MeetingTerm`, `Address`. Behavior lives on the value.

**Typed IDs:** `TypedIdValueBase` (MM-DDD) / `ContributorId` (Ardalis) wrap GUIDs so
you can't pass a `MeetingId` where a `MemberId` belongs. Cheap compile-time safety.

**Trade-off:** modeling cost and EF Core mapping friction (see §9). Worth it where
invariants are real. **Status:** Recommended for complex domains; skip for CRUD.

---

## 4. Result<T> vs exceptions; Specification pattern

**Result (Ardalis):** use cases return `Ardalis.Result<T>` —
`public record GetContributorQuery(ContributorId Id) : IQuery<Result<ContributorDto>>`
— and the Web layer maps `Result` status (NotFound/Invalid/Ok) to HTTP. Expected
business outcomes flow as values; exceptions are reserved for the truly exceptional.
MM-DDD takes the opposite stance (throws `BusinessRuleValidationException`). Both
work; **pick one per codebase and be consistent**. Result shines on APIs where
failures are normal flow; exceptions+middleware is simpler when failures are rare.

**Specification (Ardalis, eShopOnWeb):** queries as objects via
`Ardalis.Specification` — encapsulate criteria/includes/ordering in a named class
(`ContributorByIdSpec`) executed by a generic repository. Keeps query logic testable
and out of controllers, and prevents `IQueryable` leakage. **Trade-off:** another
abstraction over EF; teams fluent in LINQ sometimes prefer direct DbContext in
handlers (JT does exactly that via `IApplicationDbContext`). Both are
evidence-backed; choose per team taste and consistency.

---

## 5. Domain events & integration events

**Two-tier event model observed consistently:**

- **Domain events (in-process):** `Entity`/`BaseEntity` collects events
  (`AddDomainEvent`, `DomainEvents` read-only list, `[NotMapped]`), dispatched via
  MediatR `INotification` on `SaveChanges`. Used for side effects within the same
  module/service.
- **Integration events (cross-boundary):** separate, flat, serializable contracts in
  their own project/folder (`IntegrationEvents` per module in MM-DDD; `EventBus`
  abstractions + `EventBusRabbitMQ` implementation in eShop). Modules/services never
  share domain types — they share integration event contracts only.

**Status:** Recommended. The separation is the point: domain events are rich and
internal; integration events are stable, versionable contracts.

---

## 6. Transactional outbox (IntegrationEventLogEF)

**Observed shape (eShop):** a dedicated `IntegrationEventLogEF` project persists
`IntegrationEventLogEntry` rows **in the same transaction** as the business change,
with an `EventStateEnum` (NotPublished/InProgress/Published/Failed); a publisher
forwards pending events to the bus afterward. This guarantees you never commit a
state change and lose its event (or vice versa). MM-DDD implements the same idea
with an outbox table processed by a background job (Quartz).

**Trade-off:** an extra table and a relay loop; the price of correctness for
event-driven integration. **Status:** Strongly recommended whenever events cross a
process boundary; skip for purely in-process domain events.

---

## 7. Modular monolith (module-per-context, enforced)

**Observed shape (MM-DDD)** — the gold standard:

```
src/
├── API/                       single host, thin — routes to modules
├── BuildingBlocks/            shared kernel: Entity, ValueObject, IBusinessRule,
│                              TypedIdValueBase, event/outbox infrastructure
├── Modules/
│   ├── Meetings/              Application / Domain / Infrastructure / IntegrationEvents / Tests
│   ├── Payments/              (same internal layering per module)
│   ├── Registrations/
│   ├── UserAccess/
│   └── Administration/
└── Tests/ArchTests            solution-level module-isolation tests
```

Each module is a set of projects with its own DbContext (separate schema), its own
composition (autofac module / DI extension), and **its own ArchTests**. Modules
communicate **only via integration events and module contracts** — the
solution-level NetArchTest explicitly allows `IntegrationEventHandler`s and forbids
everything else (see §12).

**Trade-off:** single deploy/transaction simplicity with service-grade seams; costs
discipline and more projects. **Status:** Strongly recommended default for systems
too complex for one flat Clean Architecture solution but without microservice
drivers — and the cheapest on-ramp to later extraction.

---

## 8. Microservices topology (Aspire, YARP, EventBus)

**Observed shape (eShop):**

```
eShop.AppHost            .NET Aspire orchestration (replaces docker-compose for dev)
eShop.ServiceDefaults    shared: AddServiceDiscovery, AddStandardResilienceHandler,
                         OpenTelemetry logs/metrics/traces — one extension call per service
Basket.API / Catalog.API / Ordering.* / Identity.API / Webhooks.API
                         decomposed by bounded context; Ordering further split into
                         Ordering.Domain / Ordering.Infrastructure / Ordering.API
EventBus + EventBusRabbitMQ   abstraction project + transport implementation
IntegrationEventLogEF    outbox (§6)
OrderProcessor / PaymentProcessor   background workers as separate services
YARP                     reverse proxy / gateway (Aspire.Hosting.Yarp +
                         Microsoft.Extensions.ServiceDiscovery.Yarp)
```

Concrete production signals: **database-per-service**, resilience via
`AddStandardResilienceHandler` (Polly under the hood) applied centrally in
ServiceDefaults, OpenTelemetry wired once and inherited by every service, gRPC for
internal sync calls where used, identity delegated to a dedicated service
(Duende/OpenIddict family).

**Trade-off:** independent deploy/scale and team autonomy at real operational cost.
**Status:** Recommended only under real org/scale pressure; the ServiceDefaults +
Aspire pattern is worth copying even with few services.

---

## 9. Persistence with EF Core

Evidence-backed strategies, by how much you protect the domain:

- **DbContext as the unit of work, exposed via interface (JT):**
  `IApplicationDbContext` in Application, implemented in Infrastructure; handlers use
  it directly. Lowest ceremony; entities are the model.
- **Repository over aggregate roots only (eShop, MM-DDD, Ardalis):** `IRepository<T>
  where T : IAggregateRoot` + `IUnitOfWork` (eShop SeedWork). No repository for
  non-roots — you load the aggregate, not its children.
- **Keeping aggregates clean:** private setters + private parameterless ctor +
  backing fields, mapped with `IEntityTypeConfiguration<T>` classes (fluent config in
  Infrastructure, zero attributes in Domain). Value objects via `OwnsOne`/value
  converters; typed IDs via value converters.
- MM-DDD goes further: reads via **raw SQL/Dapper** for queries, EF only for the
  write side — a pragmatic CQRS split at the persistence level.

**Anti-pattern:** EF attributes (`[Required]`, `[ForeignKey]`) and navigation-heavy
bidirectional graphs *as* the domain model, lazy-loading proxies in business logic,
and `IQueryable` leaking past the application layer.

**Rule of thumb:** interface-wrapped DbContext for CRUD-ish apps; aggregate
repositories + fluent configurations where you've invested in rich aggregates.

---

## 10. Central Package Management & solution conventions

**Observed shape (eShop, Ardalis):** `Directory.Packages.props` at the root with
`<ManagePackageVersionsCentrally>true</ManagePackageVersionsCentrally>` (and eShop
adds `CentralPackageTransitivePinningEnabled`); every `<PackageVersion>` lives there
(68 in eShop), grouped with shared version properties (`$(AspireVersion)` etc.).
Projects declare `<PackageReference Include="X" />` with **no version**.
`Directory.Build.props/targets` centralize compiler settings (nullable, implicit
usings, analyzers).

**Status:** Strongly recommended for any multi-project solution — the .NET
equivalent of a Maven BOM, and the single biggest lever against version drift.

---

## 11. API design patterns

- **DTOs/records at the boundary, never entities.** Commands/queries are `record`s;
  responses are DTOs mapped from domain (JT uses Mapster/AutoMapper profiles
  colocated with the use case). Serializing EF entities leaks internals and breaks
  contracts on refactor.
- **Minimal APIs / endpoint-per-use-case** (JT `Web/Endpoints`, Ardalis
  FastEndpoints flavor) over fat controllers — keeps the edge thin and maps 1:1 to
  use cases.
- **Validation at the edge** via FluentValidation validators colocated with commands,
  executed by the pipeline behaviour (§2) — the core trusts its inputs.
- **Result→HTTP mapping in one place** (Ardalis `ResultExtensions`): NotFound/
  Invalid/Unauthorized translate uniformly, not ad-hoc per endpoint.
- **Versioning and OpenAPI** configured centrally (eShop: Asp.Versioning + OpenAPI
  extensions in ServiceDefaults).

**Status:** Recommended. Anti-pattern: leaking EF entities or `IQueryable` through
the API surface.

---

## 12. Architecture enforcement (NetArchTest / ArchUnitNET)

The reference codebases **test** their boundaries; MM-DDD ships ArchTests at *two
levels*, and that structure is worth copying verbatim:

**Solution level — module isolation** (note the explicit, narrow exceptions for the
allowed communication channel):

```csharp
var result = Types.InAssemblies(meetingsAssemblies)
    .That()
        .DoNotImplementInterface(typeof(INotificationHandler<>))
        .And().DoNotHaveNameEndingWith("IntegrationEventHandler")
    .Should()
    .NotHaveDependencyOnAny(otherModuleNamespaces)
    .GetResult();
```

**Module level — layering:**

```csharp
Types.InAssembly(DomainAssembly)
    .Should().NotHaveDependencyOn(ApplicationAssembly.GetName().Name)
    .GetResult();
// + Application must not depend on Infrastructure
```

Combine with the compiler: separate projects make most violations impossible to
compile; NetArchTest/ArchUnitNET catches the rest (namespace discipline inside a
project, accidental references, convention rules like "handlers are sealed").

**Status:** Strongly recommended. Always pair a declared boundary with (a) the
project-reference graph and (b) an architecture test.

---

## 13. Anti-patterns observed (and how to detect them)

- **Anemic domain model** — entities are `{ get; set; }` property bags, all logic in
  services/handlers. Detect: public setters everywhere, no methods on entities,
  handlers full of business `if`s. Fix: private setters, behavior methods,
  `CheckRule`/guards (§3).
- **EF-as-domain / persistence leakage** — data annotations on aggregates,
  navigation-property graphs threaded through logic, lazy proxies, `IQueryable`
  beyond Application, entities serialized out of the API. Fix:
  `IEntityTypeConfiguration` in Infrastructure, DTOs at the edge (§9, §11).
- **Fat service / god handler** — one `XService`/`XManager` with every operation.
  Fix: use-case-per-class (§2) + rich domain (§3).
- **Unenforced boundaries** — clean diagram, single project with folders, everything
  `public`. Detect: no separate projects, no ArchTests. Fix: split projects, add
  NetArchTest (§12), use `internal` + `InternalsVisibleTo` for tests.
- **Distributed monolith** — services sharing a database, deploying in lockstep, or
  chaining sync HTTP calls per request. Fix: per-service data, async integration
  events with an outbox (§5–6), or recombine into a modular monolith (§7).
- **Premature microservices** — splitting before boundaries are proven. Fix: modular
  monolith first (§7); extract along proven seams.
- **Folder-by-layer inside one project** — `Controllers/ Services/ Repositories/`
  with everything referencing everything. Fix: feature folders + project-per-layer,
  or module-per-context.
- **Version drift** — per-project package versions. Fix: Central Package Management
  (§10).
