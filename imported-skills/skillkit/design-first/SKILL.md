---
name: design-first
description: Guides the creation of technical design documents before writing code, producing architecture diagrams, data models, API interface definitions, implementation plans, and multi-option trade-off analyses. Use when the user asks to plan a feature, architect a system, design an API, explore implementation approaches, or requests a technical design or spec before coding — especially for complex features involving multiple components, ambiguous requirements, or significant architectural changes.
version: 1.0.0
triggers:
  - design first
  - plan before code
  - architecture
  - how should I implement
  - design document
tags:
  - planning
  - design
  - architecture
  - thinking
difficulty: intermediate
estimatedTime: 20
relatedSkills:
  - planning/task-decomposition
  - planning/verification-gates
---

# Design First Methodology

You are following a design-first approach. Before writing any code, design the solution.

## Core Principle

**Think first, code second.**

## When to Use Design First

Apply this methodology when:

- Building a new feature or component
- Making significant architectural changes
- The task involves multiple components or systems
- Requirements are complex or ambiguous
- Multiple valid approaches exist

Skip for trivial changes (typos, simple bug fixes, config changes).

## Design Process

### Phase 1: Understand the Problem

Before designing, ensure clarity on:

**Requirements Checklist:**
- [ ] What is the user/business need?
- [ ] What are the inputs and outputs?
- [ ] What are the constraints (performance, security, compatibility)?
- [ ] What are the edge cases?
- [ ] What are the non-requirements (out of scope)?

**Questions to Ask:**
- What exactly should this do?
- What should it NOT do?
- How will users interact with it?
- How will it integrate with existing systems?
- What happens when things go wrong?

### Phase 2: Explore Options

Generate multiple approaches before choosing:

```markdown
## Option A: [Approach Name]

**Description:** [Brief explanation]

**Pros:**
- [Advantage 1]
- [Advantage 2]

**Cons:**
- [Disadvantage 1]
- [Disadvantage 2]

**Complexity:** Low/Medium/High

---

## Option B: [Approach Name]
...
```

Evaluate options against:
- Requirements fit
- Implementation complexity
- Maintenance burden
- Performance characteristics
- Team familiarity

### Phase 3: Design the Solution

Create a design document covering:

#### System Overview
```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Client    │───▶│   Service   │───▶│  Database   │
└─────────────┘    └─────────────┘    └─────────────┘
```

#### Data Model
```typescript
interface Order {
  id: string;
  customerId: string;
  items: OrderItem[];
  status: OrderStatus;
  createdAt: Date;
  total: Money;
}
```

#### API/Interface Design
```typescript
// Public interface
interface OrderService {
  createOrder(customerId: string, items: OrderItem[]): Promise<Order>;
  getOrder(orderId: string): Promise<Order | null>;
  cancelOrder(orderId: string): Promise<void>;
}
```

#### Key Algorithms/Logic
```
Order Total Calculation:
1. Sum item prices (price × quantity)
2. Apply discounts (percentage-based first, then fixed)
3. Calculate tax (rate based on customer location)
4. Add shipping (free over threshold, otherwise flat rate)
```

#### Error Handling
- What errors can occur?
- How should they be handled?
- What should users see?

### Phase 4: Validate the Design

Before implementing, validate:

**Self-Review:**
- Does it meet all requirements?
- Are there simpler alternatives?
- What could go wrong?
- Is it testable?

**External Validation:**
- Rubber duck explanation (explain to yourself/others)
- Quick review with teammate
- Check against similar patterns in codebase

## Design Document Template

Use `DESIGN_TEMPLATE.md` as the standard artifact for each feature. It covers:

- **Overview** — one-paragraph summary of what is being built and why
- **Requirements** — functional and non-functional (performance, security)
- **Architecture** — component diagram and explanation
- **Data Model** — entity definitions and relationships
- **API Design** — interface definitions
- **Key Decisions** — decision table with options considered, choice made, and rationale
- **Implementation Plan** — ordered steps
- **Testing Strategy** — unit and integration test scope
- **Open Questions** — unresolved items

Create this file at the start of each design session and keep it updated as the design evolves.

## Design Levels

### High-Level Design (Architecture)
- System components and their interactions
- Data flow between systems
- Technology choices
- Deployment architecture

### Mid-Level Design (Module/Component)
- Class/module structure
- Interfaces and contracts
- State management
- Error handling strategy

### Low-Level Design (Implementation)
- Algorithm details
- Data structures
- Method signatures
- Edge case handling

## Anti-Patterns to Avoid

| Anti-Pattern | Mitigation |
|---|---|
| Big Design Up Front (BDUF) | Design enough to start; refine as you learn |
| Analysis Paralysis | Time-box the design phase; decide at 70% confidence |
| Design in Isolation | Align with existing codebase patterns and team conventions |

## Integration with Implementation

After design is approved:

1. **Review the design** one more time before coding
2. **Break into tasks** using task-decomposition skill
3. **Implement incrementally** - verify design assumptions as you code
4. **Update design** if you discover issues during implementation

The design document is living — update it as you learn.

## Signals You Need More Design

- "I'm not sure where to start"
- "This is getting complicated"
- "I keep refactoring"
- "The requirements are unclear"
- "Multiple approaches seem valid"

Stop and design before proceeding.
