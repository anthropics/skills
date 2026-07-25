# Architecture Patterns Reference

Detailed guide to software architecture patterns with trade-offs and implementation guidance.

## Patterns Index

1. [Monolithic Architecture](#1-monolithic-architecture)
2. [Modular Monolith](#2-modular-monolith)
3. [Microservices Architecture](#3-microservices-architecture)
4. [Event-Driven Architecture](#4-event-driven-architecture)
5. [CQRS (Command Query Responsibility Segregation)](#5-cqrs)
6. [Event Sourcing](#6-event-sourcing)
7. [Hexagonal Architecture (Ports & Adapters)](#7-hexagonal-architecture)
8. [Clean Architecture](#8-clean-architecture)
9. [API Gateway Pattern](#9-api-gateway-pattern)

---

## 1. Monolithic Architecture

**Problem it solves:** Need to build and deploy a complete application as a single unit with minimal operational complexity.

**When to use:**
- Small team (1-5 developers)
- MVP or early-stage product
- Simple domain with clear boundaries
- Deployment simplicity is priority

**When NOT to use:**
- Multiple teams need independent deployment
- Parts of system have vastly different scaling needs
- Technology diversity is required

**Trade-offs:**
| Pros | Cons |
|------|------|
| Simple deployment | Scaling is all-or-nothing |
| Easy debugging | Large codebase becomes unwieldy |
| No network latency between components | Single point of failure |
| Simple testing | Technology lock-in |

**Structure example:**
```
monolith/
├── src/
│   ├── controllers/    # HTTP handlers
│   ├── services/       # Business logic
│   ├── repositories/   # Data access
│   ├── models/         # Domain entities
│   └── utils/          # Shared utilities
├── tests/
└── package.json
```

---

## 2. Modular Monolith

**Problem it solves:** Need monolith simplicity but with clear boundaries that enable future extraction to services.

**When to use:**
- Medium team (5-15 developers)
- Domain boundaries are becoming clearer
- Want option to extract services later
- Need better code organization than traditional monolith

**When NOT to use:**
- Already need independent deployment
- Teams can't coordinate releases

**Trade-offs:**
| Pros | Cons |
|------|------|
| Clear module boundaries | Still single deployment |
| Easier to extract services later | Requires discipline to maintain boundaries |
| Single database simplifies transactions | Can drift back to coupled monolith |
| Team ownership of modules | |

**Structure example:**
```
modular-monolith/
├── modules/
│   ├── users/
│   │   ├── api/           # Public interface
│   │   ├── internal/      # Implementation
│   │   └── index.ts       # Module exports
│   ├── orders/
│   │   ├── api/
│   │   ├── internal/
│   │   └── index.ts
│   └── payments/
├── shared/                # Cross-cutting concerns
└── main.ts
```

**Key rule:** Modules communicate only through their public API, never by importing internal files.

---

## 3. Microservices Architecture

**Problem it solves:** Need independent deployment, scaling, and technology choices for different parts of the system.

**When to use:**
- Large team (15+ developers) organized around business capabilities
- Different parts need different scaling
- Independent deployment is critical
- Technology diversity is beneficial

**When NOT to use:**
- Small team that can't handle operational complexity
- Domain boundaries are unclear
- Distributed transactions are common requirement
- Network latency is unacceptable

**Trade-offs:**
| Pros | Cons |
|------|------|
| Independent deployment | Network complexity |
| Independent scaling | Distributed system challenges |
| Technology flexibility | Operational overhead |
| Team autonomy | Data consistency challenges |
| Fault isolation | Testing complexity |

**Structure example:**
```
microservices/
├── services/
│   ├── user-service/
│   │   ├── src/
│   │   ├── Dockerfile
│   │   └── package.json
│   ├── order-service/
│   └── payment-service/
├── api-gateway/
├── infrastructure/
│   ├── kubernetes/
│   └── terraform/
└── docker-compose.yml
```

**Communication patterns:**
- Synchronous: REST, gRPC
- Asynchronous: Message queues (RabbitMQ, Kafka)

---

## 4. Event-Driven Architecture

**Problem it solves:** Need loose coupling between components that react to business events asynchronously.

**When to use:**
- Components need loose coupling
- Audit trail of all changes is valuable
- Real-time reactions to events
- Multiple consumers for same events

**When NOT to use:**
- Simple CRUD operations
- Synchronous responses required
- Team unfamiliar with async patterns
- Debugging simplicity is priority

**Trade-offs:**
| Pros | Cons |
|------|------|
| Loose coupling | Eventual consistency |
| Scalability | Debugging complexity |
| Audit trail built-in | Message ordering challenges |
| Easy to add new consumers | Infrastructure complexity |

**Event structure example:**
```typescript
interface DomainEvent {
  eventId: string;
  eventType: string;
  aggregateId: string;
  timestamp: Date;
  payload: Record<string, unknown>;
  metadata: {
    correlationId: string;
    causationId: string;
  };
}

// Example event
const orderCreated: DomainEvent = {
  eventId: "evt-123",
  eventType: "OrderCreated",
  aggregateId: "order-456",
  timestamp: new Date(),
  payload: {
    customerId: "cust-789",
    items: [...],
    total: 99.99
  },
  metadata: {
    correlationId: "req-001",
    causationId: "cmd-create-order"
  }
};
```

---

## 5. CQRS

**Problem it solves:** Read and write workloads have different requirements and need to be optimized separately.

**When to use:**
- Read/write ratio is heavily skewed (10:1 or more)
- Read and write models differ significantly
- Complex queries that don't map to write model
- Different scaling needs for reads vs writes

**When NOT to use:**
- Simple CRUD with balanced reads/writes
- Read and write models are nearly identical
- Team unfamiliar with pattern
- Added complexity isn't justified

**Trade-offs:**
| Pros | Cons |
|------|------|
| Optimized read models | Eventual consistency between models |
| Independent scaling | Complexity |
| Simplified queries | Synchronization logic |
| Better performance | More code to maintain |

**Structure example:**
```typescript
// Write side (Commands)
interface CreateOrderCommand {
  customerId: string;
  items: OrderItem[];
}

class OrderCommandHandler {
  async handle(cmd: CreateOrderCommand): Promise<void> {
    const order = Order.create(cmd);
    await this.repository.save(order);
    await this.eventBus.publish(order.events);
  }
}

// Read side (Queries)
interface OrderSummaryQuery {
  customerId: string;
  dateRange: DateRange;
}

class OrderQueryHandler {
  async handle(query: OrderSummaryQuery): Promise<OrderSummary[]> {
    // Query optimized read model (denormalized)
    return this.readDb.query(`
      SELECT * FROM order_summaries
      WHERE customer_id = ? AND created_at BETWEEN ? AND ?
    `, [query.customerId, query.dateRange.start, query.dateRange.end]);
  }
}
```

---

## 6. Event Sourcing

**Problem it solves:** Need complete audit trail and ability to reconstruct state at any point in time.

**When to use:**
- Audit trail is regulatory requirement
- Need to answer "how did we get here?"
- Complex domain with undo/redo requirements
- Debugging production issues requires history

**When NOT to use:**
- Simple CRUD applications
- No audit requirements
- Team unfamiliar with pattern
- Reporting on current state is primary need

**Trade-offs:**
| Pros | Cons |
|------|------|
| Complete audit trail | Storage grows indefinitely |
| Time-travel debugging | Query complexity |
| Natural fit for event-driven | Learning curve |
| Enables CQRS | Eventual consistency |

**Implementation example:**
```typescript
// Events
type OrderEvent =
  | { type: 'OrderCreated'; customerId: string; items: Item[] }
  | { type: 'ItemAdded'; itemId: string; quantity: number }
  | { type: 'OrderShipped'; trackingNumber: string };

// Aggregate rebuilt from events
class Order {
  private state: OrderState;

  static fromEvents(events: OrderEvent[]): Order {
    const order = new Order();
    events.forEach(event => order.apply(event));
    return order;
  }

  private apply(event: OrderEvent): void {
    switch (event.type) {
      case 'OrderCreated':
        this.state = { status: 'created', items: event.items };
        break;
      case 'ItemAdded':
        this.state.items.push({ id: event.itemId, qty: event.quantity });
        break;
      case 'OrderShipped':
        this.state.status = 'shipped';
        this.state.trackingNumber = event.trackingNumber;
        break;
    }
  }
}
```

---

## 7. Hexagonal Architecture

**Problem it solves:** Need to isolate business logic from external concerns (databases, APIs, UI) for testability and flexibility.

**When to use:**
- Business logic is complex and valuable
- Multiple interfaces to same domain (API, CLI, events)
- Testability is priority
- External systems may change

**When NOT to use:**
- Simple CRUD with no business logic
- Single interface to domain
- Overhead isn't justified

**Trade-offs:**
| Pros | Cons |
|------|------|
| Business logic isolation | More abstractions |
| Highly testable | Initial setup overhead |
| External systems are swappable | Can be over-engineered |
| Clear boundaries | Learning curve |

**Structure example:**
```
hexagonal/
├── domain/              # Business logic (no external deps)
│   ├── entities/
│   ├── services/
│   └── ports/           # Interfaces (what domain needs)
│       ├── OrderRepository.ts
│       └── PaymentGateway.ts
├── adapters/            # Implementations
│   ├── persistence/     # Database adapters
│   │   └── PostgresOrderRepository.ts
│   ├── payment/         # External service adapters
│   │   └── StripePaymentGateway.ts
│   └── api/             # HTTP adapters
│       └── OrderController.ts
└── config/              # Wiring it all together
```

---

## 8. Clean Architecture

**Problem it solves:** Need clear dependency rules where business logic doesn't depend on frameworks or external systems.

**When to use:**
- Long-lived applications that will outlive frameworks
- Business logic is the core value
- Team discipline to maintain boundaries
- Multiple delivery mechanisms (web, mobile, CLI)

**When NOT to use:**
- Short-lived projects
- Framework-centric applications
- Simple CRUD operations

**Trade-offs:**
| Pros | Cons |
|------|------|
| Framework independence | More code |
| Testable business logic | Can feel over-engineered |
| Clear dependency direction | Learning curve |
| Flexible delivery mechanisms | Initial setup cost |

**Dependency rule:** Dependencies point inward. Inner circles know nothing about outer circles.

```
┌─────────────────────────────────────────┐
│           Frameworks & Drivers          │
│  ┌─────────────────────────────────┐    │
│  │     Interface Adapters          │    │
│  │  ┌─────────────────────────┐    │    │
│  │  │    Application Layer    │    │    │
│  │  │  ┌─────────────────┐    │    │    │
│  │  │  │    Entities     │    │    │    │
│  │  │  │ (Domain Logic)  │    │    │    │
│  │  │  └─────────────────┘    │    │    │
│  │  └─────────────────────────┘    │    │
│  └─────────────────────────────────┘    │
└─────────────────────────────────────────┘
```

---

## 9. API Gateway Pattern

**Problem it solves:** Need single entry point for clients that routes to multiple backend services.

**When to use:**
- Multiple backend services
- Cross-cutting concerns (auth, rate limiting, logging)
- Different clients need different APIs
- Service aggregation needed

**When NOT to use:**
- Single backend service
- Simplicity is priority
- Team can't maintain gateway

**Trade-offs:**
| Pros | Cons |
|------|------|
| Single entry point | Single point of failure |
| Cross-cutting concerns centralized | Additional latency |
| Backend service abstraction | Complexity |
| Client-specific APIs | Can become bottleneck |

**Responsibilities:**
```
┌─────────────────────────────────────┐
│            API Gateway              │
├─────────────────────────────────────┤
│ • Authentication/Authorization      │
│ • Rate limiting                     │
│ • Request/Response transformation   │
│ • Load balancing                    │
│ • Circuit breaking                  │
│ • Caching                          │
│ • Logging/Monitoring               │
└─────────────────────────────────────┘
         │         │         │
         ▼         ▼         ▼
    ┌─────┐   ┌─────┐   ┌─────┐
    │Svc A│   │Svc B│   │Svc C│
    └─────┘   └─────┘   └─────┘
```

---

## Pattern Selection Quick Reference

| If you need... | Consider... |
|----------------|-------------|
| Simplicity, small team | Monolith |
| Clear boundaries, future flexibility | Modular Monolith |
| Independent deployment/scaling | Microservices |
| Loose coupling, async processing | Event-Driven |
| Separate read/write optimization | CQRS |
| Complete audit trail | Event Sourcing |
| Testable, swappable externals | Hexagonal |
| Framework independence | Clean Architecture |
| Single entry point, multiple services | API Gateway |
