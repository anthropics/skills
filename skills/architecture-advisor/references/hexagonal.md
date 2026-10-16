# Architecture — Hexagonal (Ports & Adapters)

Core domain logic isolated behind Ports (interfaces); Adapters implement them for the
outside world (DB, HTTP, CLI). Chosen for complex business logic and long-term
maintainability: the domain has no framework, driver or transport dependencies.

## Principles

- **The domain owns the ports.** Interfaces the domain needs (repositories, gateways,
  message senders) are defined inside the domain, in domain language — never derived
  from a framework abstraction.
- **Adapters are replaceable details.** Postgres, Kafka, REST and the CLI are all
  adapters; swapping one must not touch a single line of domain or use-case code.
- **Use cases orchestrate.** Application services accept commands, load state through
  ports, apply rules, persist through ports. They are the only entry point for driving
  the domain.
- **Dependency rule.** Source code dependencies point inward only: adapter → port →
  domain. The domain imports nothing outward.

## Data Flow

Driving adapters (REST controller, scheduler, test) call a use case through its port →
the use case loads aggregates via repository ports → applies domain behavior → saves →
returns a result object. Driven adapters (persistence, messaging, HTTP clients)
implement the ports the domain defines. Mapping happens in the adapters; the domain
never sees transport or ORM types.

## Do Not

- Domain entities annotated with ORM/serialization/framework concerns.
- Ports named after the technology (`SqlUserRepository` in the domain) — name the role
  (`PolicyStore`), the adapter carries the tech.
- Use cases calling adapters directly, or adapters calling adapters.
- A "shared kernel" that quietly makes the domain depend on infrastructure.
