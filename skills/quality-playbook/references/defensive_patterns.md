# Finding Defensive Patterns (Step 5)

Defensive code patterns are evidence of past failures or known risks. Every null guard, try/catch, normalization function, and sentinel check exists because something went wrong — or because someone anticipated it would. Your job is to find these patterns systematically and convert them into fitness-to-purpose scenarios and boundary tests.

## Systematic Search

Don't skim — grep the codebase methodically. The exact patterns depend on the project's language. Here are common defensive-code indicators grouped by what they protect against:

**Null/nil guards:**

| Language | Grep pattern |
|---|---|
| Python | `None`, `is None`, `is not None` |
| Java | `null`, `Optional`, `Objects.requireNonNull` |
| Scala | `Option`, `None`, `.getOrElse`, `.isEmpty` |
| TypeScript | `undefined`, `null`, `??`, `?.` |
| Go | `== nil`, `!= nil`, `if err != nil` |
| Rust | `Option`, `unwrap`, `.is_none()`, `?` |

**Exception/error handling:**

| Language | Grep pattern |
|---|---|
| Python | `except`, `try:`, `raise` |
| Java | `catch`, `throws`, `try {` |
| Scala | `Try`, `catch`, `recover`, `Failure` |
| TypeScript | `catch`, `throw`, `.catch(` |
| Go | `if err != nil`, `errors.New`, `fmt.Errorf` |
| Rust | `Result`, `Err(`, `unwrap_or`, `match` |

**Internal/private helpers (often defensive):**

| Language | Grep pattern |
|---|---|
| Python | `def _`, `__` |
| Java/Scala | `private`, `protected` |
| TypeScript | `private`, `#` (private fields) |
| Go | lowercase function names (unexported) |
| Rust | `pub(crate)`, non-`pub` functions |

**Sentinel values, fallbacks, boundary checks:** Search for `== 0`, `< 0`, `default`, `fallback`, `else`, `match`, `switch` — these are language-agnostic.

## What to Look For Beyond Grep

- **Bugs that were fixed** — Git history, TODO comments, workarounds, defensive code that checks for things that "shouldn't happen"
- **Design decisions** — Comments explaining "why" not just "what." Configuration that could have been hardcoded but isn't. Abstractions that exist for a reason.
- **External data quirks** — Any place the code normalizes, validates, or rejects input from an external system
- **Parsing functions** — Every parser (regex, string splitting, format detection) has failure modes. What happens with malformed input? Empty input? Unexpected types?
- **Boundary conditions** — Zero values, empty strings, maximum ranges, first/last elements, type boundaries

## Converting Findings to Scenarios

For each defensive pattern, ask: "What failure does this prevent? What input would trigger this code path?"

The answer becomes a fitness-to-purpose scenario:

```markdown
### Scenario N: [Memorable Name]

**Requirement tag:** [Req: inferred — from function_name() behavior] *(use the canonical `[Req: tier — source]` format from SKILL.md Phase 1, Step 1)*

**What happened:** [The failure mode this code prevents. Reference the actual function, file, and line. Frame as a vulnerability analysis, not a fabricated incident.]

**The requirement:** [What the code must do to prevent this failure.]

**How to verify:** [A concrete test that would fail if this regressed.]
```

## Converting Findings to Boundary Tests

Each defensive pattern also maps to a boundary test:

```python
# Python (pytest)
def test_defensive_pattern_name(fixture):
    """[Req: inferred — from function_name() guard] guards against X."""
    # Mutate fixture to trigger the defensive code path
    # Assert the system handles it gracefully
```

```java
// Java (JUnit 5)
@Test
@DisplayName("[Req: inferred — from methodName() guard] guards against X")
void testDefensivePatternName() {
    fixture.setField(null);  // Trigger defensive code path
    var result = process(fixture);
    assertNotNull(result);  // Assert graceful handling
}
```

```scala
// Scala (ScalaTest)
// [Req: inferred — from methodName() guard]
"defensive pattern: methodName()" should "guard against X" in {
  val input = fixture.copy(field = None)  // Trigger defensive code path
  val result = process(input)
  result should equal (defined)  // Assert graceful handling
}
```

```typescript
// TypeScript (Jest)
test('[Req: inferred — from functionName() guard] guards against X', () => {
    const input = { ...fixture, field: null };  // Trigger defensive code path
    const result = process(input);
    expect(result).toBeDefined();  // Assert graceful handling
});
```

```go
// Go (testing)
func TestDefensivePatternName(t *testing.T) {
    // [Req: inferred — from FunctionName() guard] guards against X
    t.Helper()
    fixture.Field = nil  // Trigger defensive code path
    result, err := Process(fixture)
    if err != nil {
        t.Fatalf("expected graceful handling, got error: %v", err)
    }
    // Assert the system handled it
}
```

```rust
// Rust (cargo test)
#[test]
fn test_defensive_pattern_name() {
    // [Req: inferred — from function_name() guard] guards against X
    let input = Fixture { field: None, ..default_fixture() };
    let result = process(&input);
    assert!(result.is_ok(), "expected graceful handling");
}
```

## Minimum Bar

You should find at least 2–3 defensive patterns per source file in the core logic modules. If you find fewer, read function bodies more carefully — not just signatures and comments.

For a medium-sized project (5–15 source files), expect to find 15–30 defensive patterns total. Each one should produce at least one boundary test.
