# Project Structures — copy-ready .NET skeletons

These layouts are extracted from the reference codebases. Use them as starting
templates and adapt names to the domain. In .NET, **project references are the
architecture** — each skeleton states the reference graph to enforce, plus the
architecture-test note.

## A. Clean Architecture solution (single bounded context)

```
Acme.Billing.sln
├── Directory.Packages.props        central package versions (CPM)
├── Directory.Build.props           nullable, implicit usings, analyzers
├── src/
│   ├── Domain/                     → references: NOTHING
│   │   ├── Common/                 BaseEntity (domain events), ValueObject, IAggregateRoot
│   │   ├── Entities/  (or InvoiceAggregate/)
│   │   ├── ValueObjects/           Money, InvoiceId (typed id)
│   │   ├── Events/                 InvoiceIssuedEvent : INotification
│   │   └── Exceptions/
│   ├── Application/                → references: Domain
│   │   ├── Common/
│   │   │   ├── Interfaces/         IApplicationDbContext, IEmailSender (ports)
│   │   │   └── Behaviours/         Validation, Logging, Performance, Authorization
│   │   └── Invoices/               feature folder
│   │       ├── Commands/IssueInvoice/   IssueInvoiceCommand (record) + Handler + Validator
│   │       └── Queries/GetInvoice/      GetInvoiceQuery + Handler + InvoiceDto
│   ├── Infrastructure/             → references: Application
│   │   ├── Data/                   AppDbContext, Configurations/ (IEntityTypeConfiguration<T>),
│   │   │                           Interceptors/ (domain-event dispatch on SaveChanges)
│   │   └── Services/               EmailSender, clock, identity
│   └── Web/                        → references: Application + Infrastructure (composition root)
│       ├── Endpoints/              minimal-API endpoint groups, one per feature
│       └── Program.cs
└── tests/
    ├── Domain.UnitTests/
    ├── Application.UnitTests/      (mock IApplicationDbContext or use SQLite)
    ├── Application.FunctionalTests/ (WebApplicationFactory + Testcontainers)
    └── ArchitectureTests/          NetArchTest: Domain⊥Application⊥Infrastructure
```

Dependency rule: Domain references nothing; Application → Domain; Infrastructure →
Application; Web is the only project that sees everything. Variant (Ardalis naming):
`Core` / `UseCases` / `Infrastructure` / `Web`, with `Ardalis.Result`,
`Ardalis.Specification`, `Ardalis.GuardClauses` in Core/UseCases.

## B. Modular monolith (multiple bounded contexts, one deployable)

```
Acme.sln
├── Directory.Packages.props
├── src/
│   ├── API/Acme.API/               single thin host: auth, swagger, routes → modules
│   ├── BuildingBlocks/             shared kernel — referenced by all modules
│   │   ├── Domain/                 Entity (events + CheckRule), ValueObject,
│   │   │                           IBusinessRule, IDomainEvent, TypedIdValueBase, IAggregateRoot
│   │   ├── Application/            common abstractions (commands, queries, outbox contracts)
│   │   └── Infrastructure/         event bus, outbox processing, common EF helpers
│   ├── Modules/
│   │   ├── Billing/                ← one folder per bounded context
│   │   │   ├── Acme.Modules.Billing.Domain/
│   │   │   │   ├── Invoices/       Invoice (aggregate), value objects
│   │   │   │   └── Invoices/Rules/ InvoiceCannotBeIssuedTwiceRule : IBusinessRule
│   │   │   ├── Acme.Modules.Billing.Application/      commands/queries/handlers + Contracts/
│   │   │   ├── Acme.Modules.Billing.Infrastructure/   BillingContext (own schema), configurations
│   │   │   ├── Acme.Modules.Billing.IntegrationEvents/ ← the ONLY assembly other modules may reference
│   │   │   └── Tests/ (Unit, Integration, ArchTests)
│   │   └── Customers/              (same internal layout)
│   └── Tests/ArchTests/            solution-level: module isolation rules
└── tests/...
```

Rules to enforce: modules reference **only** BuildingBlocks and other modules'
`IntegrationEvents` assemblies; within a module, Domain ⊥ Application ⊥
Infrastructure. Solution-level NetArchTest excludes `INotificationHandler<>`/
`*IntegrationEventHandler` from the isolation rule — events are the sanctioned
channel. Each module owns its DbContext and DB schema.

## C. Microservices (Aspire, eShop-style)

```
acme-platform/
├── Directory.Packages.props        CPM + CentralPackageTransitivePinningEnabled
├── src/
│   ├── Acme.AppHost/               .NET Aspire orchestration (dev-time composition)
│   ├── Acme.ServiceDefaults/       AddServiceDiscovery, AddStandardResilienceHandler,
│   │                               OpenTelemetry — every service calls one extension
│   ├── Gateway/                    YARP reverse proxy (+ ServiceDiscovery.Yarp)
│   ├── Catalog.API/                self-contained service (simple domain → single project)
│   ├── Basket.API/                 (Redis-backed, gRPC)
│   ├── Ordering.Domain/            ┐ complex service → split like skeleton A,
│   ├── Ordering.Infrastructure/    ├ with SeedWork/ (Entity, ValueObject,
│   ├── Ordering.API/               ┘  IAggregateRoot, IRepository<T>, IUnitOfWork)
│   ├── EventBus/                   abstraction project (IEventBus, IntegrationEvent)
│   ├── EventBusRabbitMQ/           transport implementation
│   ├── IntegrationEventLogEF/      transactional outbox (same-transaction event log)
│   ├── OrderProcessor/             background worker as its own service
│   └── Identity.API/               dedicated identity service
└── tests/ (+ e2e/)
```

Rules: database-per-service (no shared schema, ever); cross-service communication via
integration events through the outbox, sync calls only where unavoidable (gRPC) and
wrapped by the standard resilience handler; ServiceDefaults referenced by every
service so resilience/telemetry are configured once.

## D. Clean-lite (small CRUD app — don't over-build)

```
Acme.Tool.sln
├── src/
│   ├── Acme.Tool.Domain/           entities + the few real rules
│   ├── Acme.Tool.Application/      feature folders, handlers, IAppDbContext
│   ├── Acme.Tool.Infrastructure/   AppDbContext + configurations
│   └── Acme.Tool.Web/              minimal APIs
└── tests/ (Unit + one ArchitectureTests project)
```

Same reference direction as A, minimal ceremony: no MediatR if the team prefers
plain handlers, DTOs as records, no repositories (DbContext behind the interface).
Keep the Domain project anyway — it costs nothing and preserves the upgrade path.

## Solution conventions (all skeletons)

- `Directory.Packages.props` with `ManagePackageVersionsCentrally` — no versions in
  csproj files. `Directory.Build.props` for nullable/analyzers/lang version.
- Tests mirror src structure; an `ArchitectureTests` project ships from day one.
- `internal` by default inside modules; `InternalsVisibleTo` for the module's tests.
- Feature folders over type folders everywhere (Commands/Queries per feature, not
  global `Services/` buckets).
