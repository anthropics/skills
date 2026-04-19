# Design Patterns

The Gang-of-Four catalog of 23 patterns, organized by purpose. Each entry: **intent**, **applicability cues** (when the code shape matches the pattern), and **language notes** where worthwhile.

## Table of contents

1. [Creational Patterns](#creational-patterns)
2. [Structural Patterns](#structural-patterns)
3. [Behavioral Patterns](#behavioral-patterns)
4. [Choosing a pattern (decision hints)](#choosing-a-pattern)

---

## Creational Patterns

Patterns for object construction.

### Factory Method
**Intent**: Defer instantiation of a class to a method (usually in a subclass or named static method) so the caller asks for an object without knowing the concrete type.
**Applicability**: The concrete type depends on input, config, or environment. Construction involves selection among variants. Naming a constructor improves readability (`User.fromJson`, `Duration.ofSeconds`).
**Language note**: In JS/TS/Python, plain module functions that return objects are Factory Methods — no class required.

### Abstract Factory
**Intent**: Provide an interface for creating families of related objects without specifying their concrete classes.
**Applicability**: Multiple related objects must be used together and come from the same "family" (e.g., a UI toolkit with Windows widgets vs. Mac widgets — mixing families would break). Plug-in architectures.
**Note**: Often overkill; a single Factory Method is usually sufficient. Reach for Abstract Factory when you genuinely have multiple product families that must stay internally consistent.

### Builder
**Intent**: Separate the construction of a complex object from its representation so the same construction process can build different representations.
**Applicability**: Many optional parameters (long constructor argument lists). Multi-step construction where intermediate states are invalid. Immutable objects that need fluent construction.
**Language note**: In Python, prefer keyword-only arguments and dataclasses. In JS/TS, options objects (`new Thing({opt1, opt2})`) often beat full Builder. Use full Builder when construction has real steps (e.g., SQL query builders, HTTP request builders).

### Prototype
**Intent**: Create new objects by cloning existing ones rather than instantiating from class.
**Applicability**: Construction is expensive or complex and an existing instance can serve as template. Avoiding parallel factory hierarchies when subclasses already exist. Rarely needed with modern languages.
**Language note**: In JS this is essentially how inheritance works; in other languages it's a deliberate pattern (deep copy + modify).

### Singleton
**Intent**: Ensure a class has exactly one instance with a global access point.
**Applicability**: Truly global resources (connection pools, config loaders) where multiple instances would be incorrect or wasteful.
**Note**: Controversial. Hard to test, hard to subclass, hides dependencies. In most cases, dependency injection (pass the shared instance as a constructor arg) is strictly better. Reach for Singleton only when the language/framework requires it.

## Structural Patterns

Patterns for composing classes and objects.

### Adapter
**Intent**: Convert the interface of a class into another interface clients expect.
**Applicability**: Integrating a third-party library or legacy class into code that expects a different API. Making two incompatible interfaces work together.
**Variants**: *Object adapter* (wrap + delegate — more flexible) vs *class adapter* (multiple inheritance — not available in Java/C#/JS).

### Bridge
**Intent**: Decouple an abstraction from its implementation so the two can vary independently.
**Applicability**: You have an abstraction hierarchy (`Shape` → `Circle`, `Square`) and an implementation hierarchy (`Renderer` → `RasterRenderer`, `VectorRenderer`) and you'd end up with a combinatorial subclass explosion (`RasterCircle`, `VectorCircle`, `RasterSquare`, `VectorSquare`). Split them — `Shape` holds a `Renderer` by composition.
**Note**: Often confused with Adapter. Adapter unifies after the fact; Bridge is designed in from the start to avoid explosion.

### Composite
**Intent**: Compose objects into tree structures where clients treat individual objects and compositions uniformly.
**Applicability**: Tree-shaped data (file systems, UI component trees, org charts, nested expressions, menu systems). Clients should be able to call `render()` on a leaf or a branch with the same code.

### Decorator
**Intent**: Attach additional responsibilities to an object dynamically by wrapping it in a decorator that conforms to the same interface.
**Applicability**: Adding orthogonal behaviors (logging, caching, auth, compression) without subclass explosion. Middleware in web frameworks is Decorator. Python decorators (the `@` syntax) are the functional form.
**Note**: Uses the same interface as the wrapped object so decorators can be stacked.

### Facade
**Intent**: Provide a unified, simplified interface to a complex subsystem.
**Applicability**: A subsystem with many classes where common tasks require orchestrating several of them. Simplifying a library's surface for typical use while still allowing advanced users direct access. API gateways.

### Flyweight
**Intent**: Use sharing to support large numbers of fine-grained objects efficiently by separating intrinsic (shared) from extrinsic (per-context) state.
**Applicability**: Memory-critical code with many objects that share most of their state (glyphs in a text renderer, particles in a game, tiles in a map). Rarely needed outside performance-critical domains.

### Proxy
**Intent**: Provide a surrogate that controls access to another object.
**Variants**:
- *Virtual Proxy* — lazy-load expensive objects
- *Remote Proxy* — local representative of a remote object (RPC stubs, ORM lazy relations)
- *Protection Proxy* — access control
- *Smart Reference* — counting references, auto-releasing, caching
**Applicability**: Any of the above needs. Proxy conforms to the same interface as the real object so clients can't tell.

## Behavioral Patterns

Patterns for communication between objects.

### Chain of Responsibility
**Intent**: Give multiple objects a chance to handle a request by passing it along a chain until one handles it.
**Applicability**: HTTP middleware pipelines. Validation chains. Event bubbling. Approval workflows. Exception handlers. Any situation where "try each handler until one fits" is the pattern.

### Command
**Intent**: Encapsulate a request as an object, letting you parameterize clients with requests, queue them, log them, and support undo.
**Applicability**: Undo/redo stacks. Job queues. Macro recording. Transaction logs. Task scheduling. Keyboard/menu binding (bind a Command to a key).

### Iterator
**Intent**: Provide sequential access to the elements of an aggregate without exposing its internal representation.
**Applicability**: Custom collection types needing traversal support. Multiple traversal orders (in-order, post-order).
**Language note**: Modern languages ship this for free (`__iter__` in Python, `Symbol.iterator` in JS, `IEnumerable` in C#, `for range` in Go). Only reach for an explicit Iterator class when you need unusual iteration behavior (external state, parallel iterators, etc.).

### Mediator
**Intent**: Define an object that encapsulates how a set of objects interact, so they don't refer to each other explicitly.
**Applicability**: GUI dialogs where many widgets coordinate (dialog is the mediator). Chat rooms (users don't message each other directly). Air traffic control systems.
**Note**: Use sparingly — mediator can become a god object that everybody talks to. When the interactions are mostly one-to-many and one-way, Observer is a better fit.

### Memento
**Intent**: Capture and externalize an object's state so it can be restored later, without violating encapsulation.
**Applicability**: Undo in editors (save a memento before each action). Checkpointing in long computations. Rollback in transactions. Save states in games.

### Observer
**Intent**: Define a one-to-many dependency so that when one object changes state, all dependents are notified and updated automatically.
**Applicability**: Event systems. Pub/sub. Reactive UI state (the heart of modern frontend frameworks). Model/View separation. Webhook dispatchers.
**Language note**: First-class functions/lambdas and event emitters make Observer lightweight in most modern languages. React's re-render mechanism is Observer under the hood.

### State
**Intent**: Allow an object to alter its behavior when its internal state changes — it appears to change its class.
**Applicability**: Objects whose behavior changes significantly based on a state (parsers, TCP connections, game entities, workflow engines, document editors). When you'd otherwise write long conditionals on a state field in every method.
**Relation to Strategy**: structurally identical; State is typically about an object managing its own state transitions, while Strategy is about a caller choosing an interchangeable algorithm.

### Strategy
**Intent**: Define a family of algorithms, encapsulate each one, and make them interchangeable — clients vary the algorithm independently.
**Applicability**: Sorting comparators. Pricing rules. Validation rules. Retry/backoff policies. Compression algorithms. Pathfinding variants in games.
**Language note**: In languages with first-class functions, Strategy often collapses to "pass a function" — don't build a full class hierarchy when `sort(items, byPrice)` works.

### Template Method
**Intent**: Define the skeleton of an algorithm in a superclass, deferring some steps to subclasses so they can override specific parts without changing the overall structure.
**Applicability**: Framework base classes ("handle request" calls `authenticate`, `validate`, `process`, `respond` — override as needed). Test setup/teardown patterns. Multi-step workflows where the sequence is fixed but the steps vary.
**Relation to Strategy**: Template Method uses inheritance for variation; Strategy uses composition. Prefer Strategy in modern code (less coupling). Template Method is useful when the variations are truly subtypes.

### Visitor
**Intent**: Represent an operation to be performed on the elements of an object structure, letting you define new operations without changing the element classes.
**Applicability**: Stable hierarchies (rare changes) where many different operations are needed (AST walkers, type checkers, serializers, pretty-printers for compilers). Cross-cutting traversals of trees.
**Warning**: Visitor inverts the normal "add a subclass" direction of extensibility — it makes adding operations easy but adding element types hard. Only use when you're certain the element hierarchy is stable.

---

## Choosing a pattern

Common shape → pattern mapping:

| Code shape | Likely pattern |
|---|---|
| `if (type === 'a') ... else if (type === 'b') ...` | Strategy, State, or Replace Conditional with Polymorphism |
| 5+ optional constructor parameters | Builder (or options object) |
| Multiple related objects that must be used together | Abstract Factory |
| Wrapping to add features (logging, caching, auth) | Decorator |
| Adapting an incompatible third-party API | Adapter |
| Tree traversal with uniform leaf/branch behavior | Composite |
| "Try each handler until one fits" | Chain of Responsibility |
| Event / pub-sub / reactive | Observer |
| Undo/redo, queueing actions | Command + Memento |
| Behavior changes based on object state | State |
| Lazy loading / access control / remoting | Proxy |
| Many peers all coordinating | Mediator |
| Many operations over a stable hierarchy | Visitor |

## Pattern-Happy warning

Designers starting out tend to over-apply patterns. A healthy refactor introduces a pattern because the code shape already matches — not because the pattern is in your vocabulary. When in doubt:

- If it's under ~50 lines and there's no variation axis, no pattern.
- If there are two variants and they'll likely never multiply, simple polymorphism (or a function passed in) beats a named pattern.
- If you can explain the code to a colleague without using the pattern name, the pattern isn't carrying its weight.
