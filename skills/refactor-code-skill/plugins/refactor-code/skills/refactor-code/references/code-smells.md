# Code Smells

A catalog of the 22 classic code smells, grouped into the five families Martin Fowler uses. Each entry has diagnostic cues (how to recognize it) and the first-choice refactorings.

## Bloaters

Code that has grown too large to work with.

### Long Method
**Cues**: function spans more than ~20 lines, or contains comments that break it into conceptual sections, or requires you to scroll to see it all.
**Fix**: Extract Method (aggressively — methods of 5–10 lines are fine), Replace Temp with Query, Introduce Parameter Object, Decompose Conditional.

### Large Class
**Cues**: a class with dozens of fields, or many methods, or methods touching disjoint subsets of fields (suggesting two classes in one).
**Fix**: Extract Class (along the axis of which fields co-vary), Extract Subclass (if variation is along a type axis), Extract Interface.

### Primitive Obsession
**Cues**: strings used as IDs, pairs of ints representing ranges, bools-as-flags, magic strings for states, dates-as-strings. Code does parsing or validation on every use.
**Fix**: Replace Data Value with Object, Replace Type Code with Class / Subclasses / State / Strategy, Replace Array with Object, Introduce Parameter Object.

### Long Parameter List
**Cues**: more than 3–4 parameters, especially when many are of the same type (easy to pass in wrong order) or when groups of them always travel together.
**Fix**: Introduce Parameter Object, Preserve Whole Object, Replace Parameter with Method Call, use keyword-only args (Python) or options objects (JS/TS).

### Data Clumps
**Cues**: the same 3+ fields appearing together in multiple class definitions, method signatures, or parameter lists. `(x, y)` every time. `(street, city, zip, country)` passed around as four separate args.
**Fix**: Extract Class for the clump, Introduce Parameter Object at the call boundary.

## Object-Orientation Abusers

Incomplete or incorrect application of OO principles.

### Switch Statements (or long if-else chains on a type tag)
**Cues**: `switch(customer.type)` or `if (shape.kind === "circle") ... else if (shape.kind === "square") ...`, repeated in multiple places.
**Fix**: Replace Conditional with Polymorphism, Replace Type Code with Subclasses / State / Strategy. This is the single most powerful OO refactoring.
**Note**: a single local switch that won't be repeated is fine. The smell is the *pattern* of dispatching on a type tag, especially when repeated.

### Temporary Field
**Cues**: an instance field used only by a specific algorithm, sitting null or meaningless the rest of the time.
**Fix**: Extract Class for the algorithm and move the field there; Introduce Null Object if the field's absence drives conditionals elsewhere.

### Refused Bequest
**Cues**: a subclass uses only a small fraction of its parent's methods or overrides many to throw `NotImplementedError`.
**Fix**: Replace Inheritance with Delegation, Extract Superclass to move only the truly shared behavior up.

### Alternative Classes with Different Interfaces
**Cues**: two classes that do similar jobs but have incompatible method names (`fetch()` vs `retrieve()`, `push()` vs `enqueue()`).
**Fix**: Rename Method to align them, Move Method to move behavior where it belongs, Extract Superclass once aligned.

## Change Preventers

Structures that force small changes to ripple across many places.

### Divergent Change
**Cues**: one class gets modified for many unrelated reasons — "I changed Customer for the tax logic, and again for the email logic, and again for reporting."
**Fix**: Extract Class along each axis of change. Each class should have a single reason to change (SRP).

### Shotgun Surgery
**Cues**: one conceptual change requires edits in many classes — the dual of divergent change. "Every time we add a currency, we touch Product, Cart, Invoice, and Emailer."
**Fix**: Move Method / Move Field to consolidate the scattered concept into a single class. Inline Class if the scattered pieces belonged together anyway.

### Parallel Inheritance Hierarchies
**Cues**: every time you add a subclass to one hierarchy, you must add a matching subclass to another. `Employee`/`Manager`/`Developer` paralleled by `EmployeeRecord`/`ManagerRecord`/`DeveloperRecord`.
**Fix**: Move Method and Move Field so one hierarchy references the other, then collapse or delete the parallel hierarchy.

## Dispensables

Code that exists without earning its keep.

### Comments
**Cues**: a comment is explaining *what* the next block of code does (not *why*).
**Fix**: Extract Method where the method name replaces the comment. Rename variables to carry meaning. Keep comments that explain *why*, trade-offs, business rules, or non-obvious constraints.

### Duplicate Code
**Cues**: the same expression or block appears in two places. Near-identical code with small variations.
**Fix**: Extract Method (same class), Pull Up Method (sibling classes), Extract Class (different classes), Form Template Method (variations across a hierarchy), Substitute Algorithm (if one version is clearly better).

### Lazy Class
**Cues**: a class that doesn't do enough to justify its existence — maybe it was useful once and has been refactored down to nothing.
**Fix**: Inline Class, Collapse Hierarchy.

### Data Class
**Cues**: a class that is only fields with getters and setters, no behavior. (Distinct from intentional DTOs and value objects, which are fine.)
**Fix**: Move Method to pull behavior onto the data — often the behavior is living in a class that's envious of this data (see Feature Envy).

### Dead Code
**Cues**: a variable, parameter, method, class, or branch that is never executed or referenced.
**Fix**: Delete it. Version control remembers. Dead code rots and confuses readers.

### Speculative Generality
**Cues**: abstract classes or interfaces with only one implementation, parameters "in case we need them later", hook methods no one calls, base classes added "just in case".
**Fix**: Inline Class, Collapse Hierarchy, Remove Parameter, Rename Method. YAGNI.

## Couplers

Classes that are too entangled with each other.

### Feature Envy
**Cues**: a method that calls more methods on another object than on `self`/`this`. The method is "jealous" of another class's data.
**Fix**: Move Method to the class the method is envious of. If it uses data from several classes, Extract Method first to isolate the envious part.

### Inappropriate Intimacy
**Cues**: two classes that know too much about each other's internals — one accessing private fields, bidirectional pointers that nobody really needs in both directions.
**Fix**: Move Method / Move Field, Change Bidirectional Association to Unidirectional, Extract Class to carry the shared concept, Replace Inheritance with Delegation.

### Message Chains
**Cues**: `a.getB().getC().getD().value` — chains of calls through multiple objects. Callers depend on the entire navigation path.
**Fix**: Hide Delegate (a.b.c becomes a.getC()), or Extract Method that wraps the chain behind a clean name. (Fluent APIs and builder chains are NOT this smell — those are intentional.)

### Middle Man
**Cues**: a class where most methods just delegate to another object.
**Fix**: Remove Middle Man (let callers talk to the real object), Inline Method, Replace Delegation with Inheritance (rarely).
**Note**: some middle men are intentional — facades and proxies. The smell is when the delegation serves no purpose.

---

## Diagnostic pattern

When reading unfamiliar code, scan in this order:

1. **Size**: is the function/class too long? (Bloaters)
2. **Conditionals**: is there dispatch on a type tag? (OO Abusers — Switch Statements)
3. **Duplication**: does the same thing appear twice? (Duplicate Code)
4. **Ownership**: does this method belong where it lives? (Feature Envy)
5. **Change axes**: what would change this code? Do unrelated changes touch the same class, or does one change touch many classes? (Change Preventers)
6. **Fit**: do primitive types carry meaning they shouldn't? (Primitive Obsession)

That scan finds roughly 80% of real-world smells in a first pass.
