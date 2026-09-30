# Architectural Review & Technical-Debt Checklist (.NET)

Use this when reviewing existing C#/.NET code or assessing risk/debt. Review for
*structure and boundaries*, not style nits. Lead findings with impact and a concrete
fix, not just a label. Phrase findings so the team can act: what's wrong, why it
costs them, what to do, and how urgent.

## What to look at first (highest signal)

1. **The project-reference graph.** Open the .sln/csproj files before any code. Does
   Domain reference EF Core or ASP.NET Core packages? Does Application reference
   Infrastructure? In .NET the csproj graph *is* the architecture — a wrong edge
   there predicts everything else. A single-project app with folder "layers" has no
   enforced boundaries at all.
2. **Where the business rules live.** Open the entities and the services/handlers.
   Entities that are all `{ get; set; }` with logic piled into `XService`/`XManager`
   classes → **anemic domain**, the most common avoidable debt. Rules belong on
   aggregates (private setters, behavior methods, `CheckRule`/guards).
3. **Boundaries — declared vs enforced.** Is there a NetArchTest/ArchUnitNET
   project, or just a diagram? Absence of architecture tests is itself a finding.
   Check access modifiers too: everything `public` means module internals are a
   reference away from becoming someone's dependency.
4. **EF Core coupling.** Data annotations on domain types, lazy-loading proxies,
   navigation-property webs driving business logic, `IQueryable` escaping the
   application layer, entities serialized straight out of controllers. All of these
   weld the domain and the API contract to the persistence model.
5. **The async/consistency seams.** Cross-module or cross-service effects done via
   direct calls and shared transactions everywhere? That's hidden coupling that
   blocks any future distribution. Events without an outbox across process
   boundaries = lost-event bugs waiting.

## Smell catalog (detect → impact → fix)

| Smell | How to detect | Why it costs | Fix |
|---|---|---|---|
| Anemic domain | Public setters everywhere; methodless entities; fat `XService` | Logic scatters/duplicates; invariants unguarded | Private setters, behavior methods, `IBusinessRule`/GuardClauses; use-case-per-handler |
| EF leakage | Attributes on aggregates; proxies/navigations in logic; entities in API responses | Domain & wire contract welded to schema; refactors ripple | `IEntityTypeConfiguration` in Infrastructure; DTO records at the edge |
| `IQueryable` escape | Repositories/services returning `IQueryable` upward | Query logic smears across layers; untestable | Specifications or materialize in Application |
| No enforced boundaries | One project, folder layers, no ArchTests, all `public` | Decay invisible until severe | Split projects; NetArchTest both levels; `internal` + InternalsVisibleTo |
| God handler/service | One class, many operations, all rules | Low cohesion; merge conflicts; untestable units | Feature folders, command/handler per use case |
| Distributed monolith | Services share a DB / deploy lockstep / sync HTTP chains | Network cost without decoupling | DB-per-service; integration events + outbox; or recombine into modular monolith |
| Missing outbox | Publish-to-bus after `SaveChanges`, no event log table | Lost or phantom events on crash | Transactional outbox (IntegrationEventLogEF pattern) |
| Premature microservices | Many services, unstable boundaries, chatty calls | Boundary moves across the network are very expensive | Modular monolith first; extract proven seams |
| Version drift | Versions scattered in csproj files; conflicts | "Works in my project" breakage | Central Package Management |
| DI grab-bag | 10+ constructor params; service locator (`IServiceProvider`) in handlers | Hidden deps; god classes in disguise | Split use cases; behaviours for cross-cutting |
| Async-over-sync / sync-over-async | `.Result`/`.Wait()` in request paths | Thread starvation under load | async end-to-end with CancellationToken |

## Risk & debt assessment output

When summarizing, organize findings as:

- **Critical (fix before building further):** wrong edges in the project graph
  (Domain→EF), services sharing a database, missing outbox on cross-service events,
  no boundaries on a codebase that's actively growing.
- **Significant (schedule soon):** anemic domain in a complex area, entities through
  the API, god handlers, sync-over-async in hot paths.
- **Watch (note, revisit):** acceptable simplifications (anemia in a genuinely CRUD
  module, direct DbContext use) that become debt only if complexity rises.

For each: state the **blast radius** (projects/teams it touches), the **trend**
(worsening as the system grows, or stable), and a **concrete first step**. Where a
decision is being changed, record it as an ADR (`adr-template.md`).

## Strengths matter too

Note what's done well (clean reference graph, rich aggregates, CPM, ArchTests,
ServiceDefaults-style centralization) so the team preserves it under pressure. A
review that only lists problems gets ignored.
