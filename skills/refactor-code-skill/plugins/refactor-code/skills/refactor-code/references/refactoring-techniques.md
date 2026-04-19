# Refactoring Techniques

The Fowler catalog, grouped by Fowler's six families. Each entry: **what it does** → **when to use**.

## Table of contents

1. [Composing Methods](#composing-methods)
2. [Moving Features Between Objects](#moving-features-between-objects)
3. [Organizing Data](#organizing-data)
4. [Simplifying Conditional Expressions](#simplifying-conditional-expressions)
5. [Simplifying Method Calls](#simplifying-method-calls)
6. [Dealing with Generalization](#dealing-with-generalization)

---

## Composing Methods

Breaking down methods and organizing their internals.

### Extract Method
Turn a code fragment into its own method named for what it does. → Whenever a comment would otherwise explain a chunk of code. The single most-used refactoring.

### Inline Method
Replace a method call with the method body and delete the method. → When the method body is as clear as its name, or the method is unhelpful indirection.

### Extract Variable
Pull an expression into a well-named local variable. → When an expression is hard to read or appears multiple times in a method.

### Inline Temp
Replace a variable with the expression that assigned it. → When the variable is referenced only once and its name adds nothing.

### Replace Temp with Query
Turn a local variable holding a computation into a method that computes it. → When the value is used in more than one place, or when extracting other methods would need access to the value.

### Split Temporary Variable
If one variable is reassigned for two different purposes, give each purpose its own variable. → When a temp is being reused for distinct things — loop counters and accumulators excepted.

### Remove Assignments to Parameters
Assign to a new local variable rather than mutating the parameter. → Always for readability, and required in languages where parameter mutation is confusing (Java) or forbidden (Scala).

### Replace Method with Method Object
Turn a long method into its own class where locals become fields. → When Extract Method is blocked by tangled locals that are all mutually dependent.

### Substitute Algorithm
Replace an algorithm's body with a cleaner implementation of the same behavior. → When you have a simpler algorithm and tests to prove equivalence.

## Moving Features Between Objects

Moving behavior and state to the classes where they belong.

### Move Method
Move a method to the class it uses most. → When a method is more interested in another class than its own (Feature Envy).

### Move Field
Move a field to the class that uses it most. → When a field is accessed more by another class than its own.

### Extract Class
Split one class into two when it has grown to hold two sets of responsibilities. → Large Class smell; divergent change; a subset of fields that co-vary and is used together.

### Inline Class
Merge a small class back into its main user. → Lazy Class; when a class doesn't earn its existence.

### Hide Delegate
Add methods on the client-facing class that forward to a delegate, so clients don't navigate through. → Message Chain smell; when exposing the delegate leaks implementation.

### Remove Middle Man
Let clients talk to the real object directly. → Middle Man smell; when most of a class is pure delegation.

### Introduce Foreign Method
When you need a method on a class you cannot modify, write a helper function that takes an instance of that class as its first parameter. → External library classes you can't modify.

### Introduce Local Extension
Subclass or wrap a class you can't modify to add methods to it. → When you need many helpers for an external class.

## Organizing Data

Restoring meaning to data that's been smeared into primitives or mismanaged.

### Self Encapsulate Field
Access a field through getters/setters even within the owning class. → Before changing how the field is represented, or when subclasses need to override access.

### Replace Data Value with Object
Turn a simple data item (usually a primitive) into its own class. → Primitive Obsession; when the primitive starts getting validated, formatted, or has associated behavior.

### Change Value to Reference
Turn a value object into a reference (shared instance) object. → When many objects need to share and observe the same underlying entity.

### Change Reference to Value
Turn a reference object into a value (immutable, compared by content) object. → When immutability would simplify reasoning; small, identity-less objects.

### Replace Array with Object
Use a class with named fields instead of a positional array. → When array indices carry semantic meaning — `row[0]` is the name, `row[1]` is the age, etc.

### Replace Magic Number with Symbolic Constant
Name the number. → Every magic number with special meaning (`86400`, `3.14159`, `0.0875` for tax rate).

### Encapsulate Field
Make a public field private and add accessors. → Public mutable state.

### Encapsulate Collection
Return a read-only view of a collection field; add explicit add/remove methods. → When clients mutate a collection they shouldn't.

### Replace Type Code with Class
Replace an integer/string tag with a class. → Primitive Obsession via type codes; when the tag drives no behavior.

### Replace Type Code with Subclasses
When the tag determines behavior and is immutable, create a subclass per value. → Switch Statements on a type code where the value never changes after construction.

### Replace Type Code with State/Strategy
When the tag determines behavior and can change at runtime, use State (if state-like) or Strategy (if interchangeable). → Switch Statements where the type can change during the object's lifetime.

### Replace Subclass with Fields
Collapse subclasses whose only difference is constant return values into a single class with fields. → Speculative Generality; subclasses that differ only in constants.

## Simplifying Conditional Expressions

Making control flow readable.

### Decompose Conditional
Extract the condition, then-branch, and else-branch into separately named methods. → Complex if-then-else where the pieces have identifiable purposes.

### Consolidate Conditional Expression
Combine a sequence of checks with the same outcome into one `or`-ed / `and`-ed expression, then Extract Method. → Multiple conditionals with identical bodies.

### Consolidate Duplicate Conditional Fragments
Move code that appears at the start/end of every branch out of the conditional. → When both branches do the same setup or cleanup.

### Remove Control Flag
Replace a boolean flag that controls loop/method flow with `break`/`return`. → Loops that track "found" flags and continue running after finding the answer.

### Replace Nested Conditional with Guard Clauses
Handle edge cases with early returns at the top of the method so the "main path" sits un-indented at the bottom. → Deeply nested if-else where most branches handle special cases.

### Replace Conditional with Polymorphism
Replace a type-tag conditional with polymorphic dispatch across subclasses. → Switch Statements on a type code, especially repeated in multiple places.

### Introduce Null Object
Replace null checks with a "null object" subclass that responds to messages inertly. → Many repeated null checks for the same field.

### Introduce Assertion
Make an assumed-true condition explicit with an assertion. → When code silently depends on an invariant that isn't visible.

## Simplifying Method Calls

Making method signatures and call sites clean.

### Rename Method
Give a method a name that matches what it does. → When the current name misleads, under-specifies, or has drifted from the implementation.

### Add Parameter / Remove Parameter
Self-explanatory. → When a method needs additional information, or when a parameter is no longer used.

### Separate Query from Modifier
Split a method that both returns a value and has a side effect into two methods. → Methods whose name suggests a query but which also mutate — surprises callers.

### Parameterize Method
Combine several similar methods into one that takes a parameter. → `setHeight()`, `setWidth()` that share 90% of their implementation.

### Replace Parameter with Explicit Methods
Split one method with a flag parameter into multiple methods. → `setValue(String kind, int value)` where `kind` selects behavior → `setHeight(int)`, `setWidth(int)`.

### Preserve Whole Object
Pass the whole object instead of several of its fields. → Long Parameter List composed of fields from one object.

### Replace Parameter with Method Call
If a parameter can be obtained via another method call, remove it. → When the caller computes the value from accessible state just to pass it in.

### Introduce Parameter Object
Bundle a clump of parameters into an object. → Long Parameter List, especially with Data Clumps.

### Remove Setting Method
Remove setters for fields that should only be set at construction. → Fields that are logically immutable.

### Hide Method
Reduce visibility of a method that isn't actually used externally. → Over-broad public APIs.

### Replace Constructor with Factory Method
Use a named static method instead of a constructor for creation. → When construction has variants (named factories like `List.of()`, `Duration.ofSeconds()`) or should return a subclass/cached instance.

### Replace Error Code with Exception / Replace Exception with Test
Use exceptions for exceptional conditions, tests for expected conditions. → Error codes ignored by callers (use exceptions); exceptions thrown for normal flow (use tests).

## Dealing with Generalization

Moving features up and down class hierarchies.

### Pull Up Field / Pull Up Method
Move a member from subclasses to the superclass when all subclasses share it. → Duplicate Code in siblings.

### Pull Up Constructor Body
Move common constructor logic into the superclass constructor. → Sibling constructors duplicating initialization.

### Push Down Field / Push Down Method
Move a member from the superclass to only the subclasses that need it. → Refused Bequest where some subclasses don't use the member.

### Extract Subclass / Extract Superclass / Extract Interface
Create a new class that some or all instances of the current class become. → When there's variation along a type axis (subclass), common behavior across classes (superclass), or a shared calling contract (interface).

### Collapse Hierarchy
Merge a subclass and superclass when they're no longer meaningfully different. → Speculative Generality in inheritance.

### Form Template Method
Move the invariant algorithm to the superclass and let subclasses override the varying steps. → Two or more methods in siblings that do the same high-level thing with different steps.

### Replace Inheritance with Delegation
Hold an instance of the former parent as a field and forward calls selectively. → Refused Bequest, or when inheritance is causing the Is-A relationship to break.

### Replace Delegation with Inheritance
Inherit from the delegate class instead of wrapping it. → When you find yourself forwarding nearly every method to a delegate *and* Is-A holds. (Rare — the reverse is usually better.)

---

## Choosing the right refactoring

When multiple refactorings could apply, prefer the one that:

1. **Addresses the root smell**, not a downstream symptom. A Long Method caused by Switch Statements on a type code is fixed by Replace Conditional with Polymorphism, not by Extract Method (which would just scatter the switch into extracted methods).
2. **Preserves the caller surface**. Refactorings that don't change the public API are safer to apply in one shot; API-changing refactorings may need a deprecation cycle in real systems.
3. **Uses existing language features**. In languages with first-class functions (JS/TS, Python, Go, Kotlin), Strategy often collapses to "pass a function" rather than a full class hierarchy — use the simpler form when available.
