---
name: refactor-code
description: Refactor source code ambitiously using the catalog of code smells, refactoring techniques, and design patterns popularized by Martin Fowler and catalogued at refactoring.guru, with pattern-driven rewrites where they genuinely fit, cross-checked against language-specific linter rules (ESLint, ruff, clang-tidy, golangci-lint, etc.). Use this whenever the user asks to refactor, clean up, restructure, modernize, or improve code; mentions code smells, SOLID principles, design patterns, legacy code, or tech debt; shares a code file and asks for it to be made better; wants a behavior-preserving rewrite; or asks to reduce duplication, shorten functions, untangle conditionals, or apply a specific pattern like Strategy, Factory, or Observer. Works across .py, .js, .ts, .jsx, .tsx, .cpp, .c, .go, .java, .cs, .rb, .php and other programming language files.
---

# Refactor Code

Refactor code ambitiously and with principled justification. Draw on the catalog of refactorings and design patterns from Martin Fowler's *Refactoring* and the Gang of Four's *Design Patterns* — both consolidated and cross-referenced at refactoring.guru. Treat linter rules (ESLint, ruff, clang-tidy, etc.) as style cross-checks, not the primary driver: linters catch surface issues while this skill targets deeper structural improvement.

The user picked this skill because they want **better code, not a lecture about it**.

## Output contract

Produce refactored code with minimal commentary. Specifically:

- Lead with the refactored code as the primary artifact — a single code block per file.
- Put a short header comment at the top of each file listing the key refactorings and patterns applied, e.g. `// Refactored: Extract Method, Replace Conditional with Polymorphism, Strategy pattern`. One line. The named techniques are the justification.
- Preserve the user's naming conventions, indentation style, import ordering, and overall voice unless those ARE the smell being fixed.
- After the code, if something genuinely non-obvious happened (a behavioral edge case, a trade-off, a dependency the user now needs to install), note it in one or two sentences. Otherwise skip commentary entirely.
- Never write essay-length explanations. Never give bulleted "here are all the changes I made" summaries unless explicitly asked. Named refactorings in the header comment are the changelog.

When the input spans multiple logical units that should become multiple files (e.g. extracting a Strategy interface and implementations), emit each as its own code block with a filename header.

## Workflow

1. **Read the code to understand its behavior.** Refactoring is by definition behavior-preserving. If the behavior is unclear, ask one question before proceeding — you cannot preserve what you do not understand.

2. **Diagnose the smells.** Identify what's actually wrong. The most common smells in real-world code are Long Method, Large Class, Duplicate Code, Long Parameter List, Switch Statements / complex conditionals, Feature Envy, Data Clumps, and Primitive Obsession. See `references/code-smells.md` for the full catalog with diagnostic cues.

3. **Select refactorings and patterns.** Match each smell to the appropriate technique. Be ambitious: when conditional dispatch on a type code genuinely calls for Strategy or Replace Conditional with Polymorphism, apply it; when object construction has grown unwieldy with optional parameters, reach for Builder or Factory Method; when a class is doing too much, carve off responsibilities with Extract Class. See `references/refactoring-techniques.md` for the refactoring catalog and `references/design-patterns.md` for design patterns with applicability cues.

4. **Apply the transformation.** You don't need to emit intermediate steps, but think in small behavior-preserving moves before finalizing the output. This catches regressions at edit time.

5. **Cross-check against linter rules** for the target language — see `references/linting-by-language.md`. You are not running the linters; you are verifying the output would pass key rules (unused vars, implicit `any`, missing `const`, shadowing, etc.). If the input already violated style rules, fix the violations that are in your way but don't turn the refactor into a style-only pass.

6. **Emit the code** per the output contract.

## Quick-reference: smell → first-choice refactoring

| Smell | First-choice refactoring |
|---|---|
| Long method | Extract Method, Replace Temp with Query, Decompose Conditional |
| Duplicate code in siblings | Pull Up Method / Pull Up Field |
| Duplicate code in unrelated places | Extract Method + Extract Class, or Extract Function to shared module |
| Long parameter list | Introduce Parameter Object, Preserve Whole Object |
| Switch / if-else chain on type code | Replace Conditional with Polymorphism, Strategy pattern, State pattern |
| Primitive obsession (string IDs, flag ints, magic strings) | Replace Data Value with Object, Replace Type Code with Class / Subclasses |
| Data clumps (same 3+ fields travel together) | Extract Class, Introduce Parameter Object |
| Feature envy (method uses another class's data more than its own) | Move Method |
| Large class | Extract Class, Extract Subclass, Extract Superclass |
| Shotgun surgery | Move Method / Move Field to consolidate the concept in one place |
| Divergent change (one class changed for many unrelated reasons) | Extract Class along the axis of change |
| Nested conditionals | Replace Nested Conditional with Guard Clauses, Decompose Conditional |
| Magic numbers or strings | Replace Magic Number with Symbolic Constant, enum, or named constant |
| Comments explaining *what* code does | Extract Method with a name that replaces the comment |
| Refused bequest (subclass uses little of parent) | Replace Inheritance with Delegation, Extract Superclass |
| Message chain (`a.b().c().d().e()`) | Hide Delegate, or Extract Method that wraps the chain |
| Middle man (class that only delegates) | Remove Middle Man, Inline Class |
| Dead code | Delete it (version control has a copy) |

## Quick-reference: pattern fits

Reach for a pattern when the problem shape matches, not because you know the pattern:

- **Strategy** — interchangeable algorithms chosen at runtime (sorting comparators, pricing rules, validation rules, retry policies)
- **Factory Method / Abstract Factory** — object creation where the concrete type varies by input, config, or environment
- **Builder** — object construction with many optional parameters, multi-step setup, or immutability requirements
- **Observer** — event dispatch, pub/sub, reactive UI state, webhook fan-out
- **Adapter** — bridging an incompatible third-party interface to one you control
- **Decorator** — adding behavior to objects without subclassing (middleware, logging wrappers, caching layers)
- **Facade** — a single clean entry point over a complex subsystem
- **Command** — encapsulating requests as objects (undo/redo stacks, job queues, scheduling, macro recording)
- **Template Method** — algorithm skeleton with overridable steps (common in framework base classes)
- **State** — object behavior that changes with internal state (parsers, game entities, workflow engines, TCP connections)
- **Chain of Responsibility** — pipeline of handlers each deciding to handle or pass (HTTP middleware, validation chains, event bubbling)
- **Composite** — tree structures treated uniformly (file systems, UI component trees, org charts)
- **Proxy** — stand-in controlling access to another object (lazy loading, remote proxies, access control)
- **Iterator** — decoupling traversal from collection structure (most modern languages give this for free)
- **Mediator** — centralizing interactions among many peers (avoid when simple observer suffices)
- **Memento** — capturing and restoring object state (undo, snapshots, checkpoints)
- **Visitor** — operations across a stable object hierarchy (AST walkers, type checkers)
- **Flyweight** — sharing fine-grained objects to save memory (rarely needed outside perf-critical code)
- **Bridge** — decoupling an abstraction from its implementation so both vary independently
- **Prototype** — cloning objects when construction is expensive or type info is lost
- **Singleton** — exactly one instance globally (controversial; prefer dependency injection in most cases)

See `references/design-patterns.md` for intent, applicability, and minimal structural examples.

## SOLID as cross-cutting guidance

- **S — Single Responsibility**: each class/module has one reason to change
- **O — Open/Closed**: open for extension, closed for modification; usually achieved via Strategy, Template Method, or Observer
- **L — Liskov Substitution**: subclasses must be usable wherever the base class is, without surprises
- **I — Interface Segregation**: many small focused interfaces beat one wide one
- **D — Dependency Inversion**: depend on abstractions, not concretions; inject dependencies rather than hard-coding construction

When a refactoring restores a violated SOLID principle, include it in the header comment (e.g. `// Refactored: Extract Interface (DIP), Strategy (OCP)`).

## Anti-patterns to avoid

- **Pattern Happy** — applying a pattern because you know it, not because the code shape calls for it. A 10-line function does not need Strategy.
- **Premature abstraction** — extracting shared code from two callers that might not actually share intent. Wait for a third.
- **Behavior change disguised as refactoring** — if external behavior changes, that is a rewrite, not a refactor. Call it out explicitly to the user.
- **Rename-the-world** — don't rename things that weren't part of the smell. It creates diff noise that hides the actual work.
- **Deleting *why* comments** — comments explaining *what* the code does are the smell (fix with extracted methods that are self-explanatory). Comments explaining *why* — business rules, historical context, tricky invariants — stay.

## When not to refactor

If the input code is already clean — short focused functions, clear names, no visible smells, patterns appropriately applied — say so in one line and return the code essentially unchanged. Do not manufacture changes to justify the invocation.

## Examples of the output format

**Example 1 — Python, single file**

````python
# Refactored: Extract Method, Replace Magic Number with Symbolic Constant, Guard Clauses
from dataclasses import dataclass

FREE_SHIPPING_THRESHOLD = 50.00
TAX_RATE = 0.0875

@dataclass
class Order:
    subtotal: float
    customer_is_member: bool

def calculate_total(order: Order) -> float:
    if order.subtotal <= 0:
        return 0.0
    shipping = _shipping_cost(order)
    tax = order.subtotal * TAX_RATE
    return order.subtotal + shipping + tax

def _shipping_cost(order: Order) -> float:
    if order.customer_is_member:
        return 0.0
    if order.subtotal >= FREE_SHIPPING_THRESHOLD:
        return 0.0
    return 5.99
````

**Example 2 — TypeScript, Strategy pattern extracted into multiple files**

```ts
// pricing.ts
// Refactored: Replace Conditional with Polymorphism, Strategy (OCP)
import type { PricingStrategy } from "./pricing-strategies";

export function priceOrder(subtotal: number, strategy: PricingStrategy): number {
  return strategy.apply(subtotal);
}
```

```ts
// pricing-strategies.ts
export interface PricingStrategy {
  apply(subtotal: number): number;
}

export const standardPricing: PricingStrategy = {
  apply: (s) => s,
};

export const memberPricing: PricingStrategy = {
  apply: (s) => s * 0.9,
};

export const blackFridayPricing: PricingStrategy = {
  apply: (s) => s * 0.75,
};
```

New file `pricing-strategies.ts` introduced; callers select the strategy at the call site instead of passing a `customerType` string.

---

That last sentence — noting a new file and the small caller-side change — is the kind of commentary worth keeping. Anything more would be over-explaining.
