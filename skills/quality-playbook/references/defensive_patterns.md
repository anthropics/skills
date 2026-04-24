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

## State Machine Patterns

State machines are a special category of defensive pattern. When you find status fields, lifecycle phases, or mode flags, trace the full state machine — see SKILL.md Step 5a for the complete process.

**How to find state machines:**

| Language | Grep pattern |
|---|---|
| Python | `status`, `state`, `phase`, `mode`, `== "running"`, `== "pending"` |
| Java | `enum.*Status`, `enum.*State`, `.getStatus()`, `switch.*status` |
| Scala | `sealed trait.*State`, `case object`, `status match` |
| TypeScript | `status:`, `state:`, `Status =`, `switch.*status` |
| Go | `Status`, `State`, `type.*Phase`, `switch.*status` |
| Rust | `enum.*State`, `enum.*Status`, `match.*state` |

**For each state machine found:**

1. List every possible state value (read the enum or grep for assignments)
2. For each handler/consumer that checks state, verify it handles ALL states
3. Look for states you can enter but never leave (terminal state without cleanup)
4. Look for operations that should be available in a state but are blocked by an incomplete guard

## Enumeration and Whitelist Completeness

When a function uses `switch`/`case`, `match`, if-else chains, or any dispatch construct to handle a set of named constants (feature bits, enum values, command codes, event types, permission flags), perform the **two-list enumeration check**:

1. **List A (defined):** Extract every constant from the relevant header, enum, or spec that the code should handle. Use grep — do not list from memory.
2. **List B (handled):** Extract every case label, branch condition, or map key from the dispatch code. Use grep or line-by-line read — do not summarize.
3. **Diff:** Compare the two lists. Any constant in A but not in B is a potential gap. Any constant in B but not in A is a potential dead case.

**Why this exists:** AI models reliably hallucinate completeness for switch/case constructs. The model sees a function with many case labels, sees constants defined elsewhere, and concludes all constants are handled without actually checking. In one observed case, the model asserted that a kernel feature-bit whitelist "preserves supported ring transport bits including VIRTIO_F_RING_RESET" when that constant was entirely absent from the switch — the model hallucinated coverage because the constant existed in a header the function's callers used. The mechanical two-list check is the only reliable countermeasure.

**Triage verification probes must produce executable evidence.** When triage confirms or rejects an enumeration finding via verification probe, prose reasoning alone is insufficient. The probe must produce a test assertion for each constant: `assert "case VIRTIO_F_RING_RESET:" in source_of("vring_transport_features"), "RING_RESET at line NNN"`. This rule exists because in v1.3.16, the triage correctly received a minority finding about RING_RESET but rejected it with a hallucinated claim that "lines 3527-3528 explicitly preserve RING_RESET" — those lines were actually the `default:` branch. Had the triage been forced to write an assertion, it would have failed, exposing the hallucination.

**Code-side lists must be extracted from the code, not copied from requirements.** When performing the two-list check in the code review or spec audit, the "handled" list must be extracted directly from the function body with per-item line numbers. Do not copy from REQUIREMENTS.md, CONTRACTS.md, the audit prompt, or any other generated artifact. If the two lists (code-extracted vs. requirements-claimed) are word-for-word identical, that is a red flag that the code list was copied — redo the extraction. In v1.3.17, the code review's "case labels present" list was identical to the requirements list, proving it was copied rather than extracted. Three spec auditors then inherited this false list and none independently verified. The per-item line-number citation prevents this: you cannot cite "line 3527: `case VIRTIO_F_RING_RESET:`" when line 3527 actually contains `default:`.

**Mechanical verification artifacts outrank prose lists.** If `quality/mechanical/<function>_cases.txt` exists for a dispatch function, use it as the authoritative source for what the function handles. Do not replace it with a hand-written list. If no mechanical artifact exists, generate one using a non-interactive shell pipeline (e.g., `awk` + `grep`) before writing contracts or requirements about the function's coverage.

**Artifact integrity risk:** In v1.3.19 testing, the model executed the correct extraction command but wrote its own fabricated output to the file instead of letting the shell redirect capture it. The fabricated file included a hallucinated `case VIRTIO_F_RING_RESET:` line that the real command does not produce. To mitigate: `quality/mechanical/verify.sh` re-runs every extraction command and diffs against saved files. If any diff is non-empty, the artifact was tampered with and must be regenerated.

**Where to apply:** Feature-bit negotiation functions, protocol message dispatchers, permission check switches, configuration option handlers, codec/format registration tables, HTTP method/status code handlers, and any function where a `default:` or `else` clause silently drops unrecognized values.

**Converting state machine gaps to scenarios:**

```markdown
### Scenario N: [Status] blocks [operation]

**Requirement tag:** [Req: inferred — from handler() status guard]

**What happened:** The [handler] only allows [operation] when status is "[allowed_states]", but the system can enter "[missing_state]" status (e.g., due to [condition]). When this happens, the user cannot [operation] and has no workaround through the interface.

**The requirement:** [operation] must be available in all states where the user would reasonably need it, including [missing_state].

**How to verify:** Set up a [entity] in "[missing_state]" status. Attempt [operation]. Assert it succeeds or provides a clear error with a workaround.
```

## Missing Safeguard Patterns

Search for operations that commit the user to expensive, irreversible, or long-running work without adequate preview or confirmation:

| Pattern | What to look for |
|---|---|
| Pre-commit information gap | Operations that start batch jobs, fan-out expansions, or API calls without showing estimated cost, scope, or duration |
| Silent expansion | Fan-out or multiplication steps where the final work count isn't known until runtime, with no warning shown |
| No termination condition | Polling loops, watchers, or daemon processes that check for new work but never check whether all work is done |
| Retry without backoff | Error handling that retries immediately or on a fixed interval without exponential backoff, risking rate limit floods |

**Converting missing safeguards to scenarios:**

```markdown
### Scenario N: No [safeguard] before [operation]

**Requirement tag:** [Req: inferred — from init_run()/start_watch() behavior]

**What happened:** [Operation] commits the user to [consequence] without showing [missing information]. In practice, a [example] fanned out from [small number] to [large number] units with no warning, resulting in [cost/time consequence].

**The requirement:** Before committing to [operation], display [safeguard] showing [what the user needs to see].

**How to verify:** Initiate [operation] and assert that [safeguard information] is displayed before the point of no return.
```

## Minimum Bar

You should find at least 2–3 defensive patterns per source file in the core logic modules. If you find fewer, read function bodies more carefully — not just signatures and comments.

For a medium-sized project (5–15 source files), expect to find 15–30 defensive patterns total. Each one should produce at least one boundary test. Additionally, trace at least one state machine if the project has status/state fields, and check at least one long-running operation for missing safeguards.
