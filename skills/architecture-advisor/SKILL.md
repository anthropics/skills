---
name: architecture-advisor
description: Choose and justify a core architecture pattern for a service or module — layered, hexagonal, clean, CQRS, microservices, modular monolith, event-driven, functional core/imperative shell — using three selectors (domain complexity, team size, scaling needs), plus overlay tables for API style, frontend integration and data persistence. Produces a written justification with accepted trade-offs and rejected alternatives, ready for a design document. Use when starting a new service or module, filling the architectural decisions section of a design doc, deciding monolith vs microservices, or when asked which architecture fits.
author: jordimarsal
version: "1.0"
tags:
  - architecture
  - design
  - hexagonal
  - clean-architecture
  - cqrs
  - microservices
  - decision-making
---

# Architecture Advisor

Pick one core architecture pattern per service and justify it in writing. The
catalog does not force a choice for every task — consult it when the decision
is live: a new service, a new module with its own boundaries, or the
Architectural Decisions section of a design document.

## The procedure

1. **Read the catalog** ([references/catalog.md](references/catalog.md)) —
   each pattern lists what it is, when it fits, its trade-offs, and when NOT
   to use it.
2. **Answer the three selectors** in one line each:
   - *Domain complexity*: is the business logic rich and changing, or is the
     app mostly CRUD over a schema?
   - *Team size*: how many people own this service?
   - *Scaling needs*: do parts of the system genuinely need to scale or fail
     independently?
3. **Pick ONE core pattern per service.** Default when unsure: **modular
   monolith** — it delivers most benefits without the distributed tax, and
   extracting a service later is easier than merging two.
4. **If torn between two**, write both as alternatives with pros/cons in the
   design document and pick one. A reviewer challenges the justification, not
   the choice — so the justification carries the weight: name the trade-offs
   you accept and the alternative you rejected.
5. **Read the chosen pattern's detail file** and follow its principles and
   its "Do Not" list — that list is where each pattern actually fails:
   - [layered](references/layered.md) · [hexagonal](references/hexagonal.md) ·
     [clean](references/clean.md) · [cqrs](references/cqrs.md) ·
     [microservices](references/microservices.md) ·
     [modular-monolith](references/modular-monolith.md) ·
     [event-driven](references/event-driven.md)
6. **Choose overlays separately** — API style, frontend integration and data
   persistence are independent of the core pattern (catalog tail tables). A
   hexagonal service can expose REST; a modular monolith can use gRPC
   internally.

## The justification block

End with exactly this shape in the design document:

```markdown
## Architectural Decision

**Pattern:** <one core pattern>

**Selectors:** complexity: <low|medium|high — why> · team: <n> ·
scaling: <what needs independent scaling, or "none today">

**Accepted trade-offs:** <the two or three costs this choice carries>

**Rejected alternative:** <pattern> — <one-line reason>
```

## Never do

- Never default to microservices "for later" — unclear boundaries plus a
  small team is the textbook way to buy the tax without the benefit.
- Never mix two core patterns in one service ("hexagonal CQRS clean" is one
  pattern with extra steps; name the one that dominates).
- Never choose a pattern the team cannot enforce: Clean decays into Layered
  without discipline; event schemas rot without an owner; modular monolith
  boundaries erode without CI enforcement.
- Never leave the decision implicit — an architecture that is not written
  down with its trade-offs cannot be reviewed, only guessed at.

---

Part of the [harness](https://github.com/jordimarsal/harness) SDD suite (MIT).
