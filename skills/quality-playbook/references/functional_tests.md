# Writing Functional Tests

This is the most important deliverable. The Markdown files are documentation. The functional test file is the automated safety net. Name it using the project's conventions: `test_functional.py` (Python/pytest), `FunctionalSpec.scala` (Scala/ScalaTest), `FunctionalTest.java` (Java/JUnit), `functional.test.ts` (TypeScript/Jest), `functional_test.go` (Go), etc.

## Structure: Three Test Groups

Organize tests into three logical groups using whatever structure the test framework provides — classes (Python/Java), describe blocks (TypeScript/Jest), traits (Scala), or subtests (Go):

```
Spec Requirements
    — One test per testable spec section
    — Each test's documentation cites the spec requirement

Fitness Scenarios
    — One test per QUALITY.md scenario (1:1 mapping)
    — Named to match: test_scenario_N_memorable_name (or equivalent convention)

Boundaries and Edge Cases
    — One test per defensive pattern from Step 5
    — Targets null guards, try/catch, normalization, fallbacks
```

## Test Count Heuristic

**Target = (testable spec sections) + (QUALITY.md scenarios) + (defensive patterns from Step 5)**

Example: 12 spec sections + 10 scenarios + 15 defensive patterns = 37 tests as a target.

For a medium-sized project (5–15 source files), this typically yields 35–50 functional tests. Significantly fewer suggests missed requirements or shallow exploration. Don't pad to hit a number — every test should exercise real project code and verify a meaningful property.

## Import Pattern: Match the Existing Tests

Before writing any test code, read 2–3 existing test files and identify how they import project modules. This is critical — projects handle imports differently and getting it wrong means every test fails with resolution errors.

Common patterns by language:

**Python:**
- `sys.path.insert(0, "src/")` then bare imports (`from module import func`)
- Package imports (`from myproject.module import func`)
- Relative imports with conftest.py path manipulation

**Java:**
- `import com.example.project.Module;` matching the package structure
- Test source root must mirror main source root

**Scala:**
- `import com.example.project._` or `import com.example.project.{ClassA, ClassB}`
- SBT project layout: `src/test/scala/` mirrors `src/main/scala/`

**TypeScript/JavaScript:**
- `import { func } from '../src/module'` with relative paths
- Path aliases from `tsconfig.json` (e.g., `@/module`)

**Go:**
- Same package: test files in the same directory with `package mypackage`
- Black-box testing: `package mypackage_test` with explicit imports
- Internal packages may require specific import paths

**Rust:**
- `use crate::module::function;` for unit tests in the same crate
- `use myproject::module::function;` for integration tests in `tests/`

Whatever pattern the existing tests use, copy it exactly. Do not guess or invent a different pattern.

## Create Test Setup BEFORE Writing Tests

Every test framework has a mechanism for shared setup. If your tests use shared fixtures or test data, you MUST create the setup file before writing tests. Test frameworks do not auto-discover fixtures from other directories.

**By language:**

**Python (pytest):** Create `quality/conftest.py` defining every fixture. Fixtures in `tests/conftest.py` are NOT available to `quality/test_functional.py`. Preferred: write tests that create data inline using `tmp_path` to eliminate conftest dependency.

**Java (JUnit):** Use `@BeforeEach`/`@BeforeAll` methods in the test class, or create a shared `TestFixtures` utility class in the same package.

**Scala (ScalaTest):** Mix in a trait with `before`/`after` blocks, or use inline data builders. If using SBT, ensure the test file is in the correct source tree.

**TypeScript (Jest):** Use `beforeAll`/`beforeEach` in the test file, or create a `quality/testUtils.ts` with factory functions.

**Go (testing):** Helper functions in the same `_test.go` file with `t.Helper()`. Use `t.TempDir()` for temporary directories. Go convention strongly prefers inline setup — avoid shared test state.

**Rust (cargo test):** Helper functions in a `#[cfg(test)] mod tests` block or a `test_utils.rs` module. Use builder patterns for constructing test data. For integration tests, place files in `tests/`.

**Rule: Every fixture or test helper referenced must be defined.** If a test depends on shared setup that doesn't exist, the test will error during setup (not fail during assertion) — producing broken tests that look like they pass.

**Preferred approach across all languages:** Write tests that create their own data inline. This eliminates cross-file dependencies:

```python
# Python
def test_config_validation(tmp_path):
    config = {"pipeline": {"name": "Test", "steps": [...]}}
```

```java
// Java
@Test
void testConfigValidation(@TempDir Path tempDir) {
    var config = Map.of("pipeline", Map.of("name", "Test"));
}
```

```typescript
// TypeScript
test('config validation', () => {
    const config = { pipeline: { name: 'Test', steps: [] } };
});
```

```go
// Go
func TestConfigValidation(t *testing.T) {
    tmpDir := t.TempDir()
    config := Config{Pipeline: Pipeline{Name: "Test"}}
}
```

```rust
// Rust
#[test]
fn test_config_validation() {
    let config = Config { pipeline: Pipeline { name: "Test".into() } };
}
```

**After writing all tests, run the test suite and check for setup errors.** Setup errors (fixture not found, import failures) count as broken tests regardless of how the framework categorizes them.

## No Placeholder Tests

Every test must import and call actual project code. If a test body is `pass`, or its only assertion is `assert isinstance(errors, list)`, or it checks a trivial property like `assert hasattr(cls, 'validate')`, delete it and write a real test or drop it entirely. A test that doesn't exercise project code is worse than no test — it inflates the count and creates false confidence.

If you genuinely cannot write a meaningful test for a defensive pattern (e.g., it requires a running server or external service), note it as untestable in a comment rather than writing a placeholder.

## Read Before You Write: The Function Call Map

Before writing a single test, build a function call map. For every function you plan to test:

1. **Read the function/method signature** — not just the name, but every parameter, its type, and default value. In Python, read the `def` line and type hints. In Java, read the method signature and generics. In Scala, read the method definition and implicit parameters. In TypeScript, read the type annotations.
2. **Read the documentation** — docstrings, Javadoc, TSDoc, ScalaDoc. They often specify return types, exceptions, and edge case behavior.
3. **Read one existing test that calls it** — existing tests show you the exact calling convention, fixture shape, and assertion pattern.
4. **Read real data files** — if the function processes configs, schemas, or data files, read an actual file from the project. Your test fixtures must match this shape exactly.

**Common failure pattern:** The agent explores the architecture, understands conceptually what a function does, then writes a test call with guessed parameters. The test fails because the real function takes `(config, items_data, limit)` not `(items, seed, strategy)`. Reading the actual signature takes 5 seconds and prevents this entirely.

**Library version awareness:** Check the project's dependency manifest (`requirements.txt`, `build.sbt`, `package.json`, `pom.xml`, `build.gradle`, `Cargo.toml`) to verify what's available. Use the test framework's skip mechanism for optional dependencies: Python `pytest.importorskip()`, JUnit `Assumptions.assumeTrue()`, ScalaTest `assume()`, Jest conditional `describe.skip`, Go `t.Skip()`, Rust `#[ignore]` with a comment explaining the prerequisite.

## Writing Spec-Derived Tests

Walk each spec document section by section. For each section, ask: "What testable requirement does this state?" Then write a test.

Each test should:
1. **Set up** — Load a fixture, create test data, configure the system
2. **Execute** — Call the function, run the pipeline, make the request
3. **Assert specific properties** the spec requires

```python
# Python (pytest)
class TestSpecRequirements:
    def test_requirement_from_spec_section_N(self, fixture):
        """[Req: formal — Design Doc §N] X should produce Y."""
        result = process(fixture)
        assert result.property == expected_value
```

```java
// Java (JUnit 5)
class SpecRequirementsTest {
    @Test
    @DisplayName("[Req: formal — Design Doc §N] X should produce Y")
    void testRequirementFromSpecSectionN() {
        var result = process(fixture);
        assertEquals(expectedValue, result.getProperty());
    }
}
```

```scala
// Scala (ScalaTest)
class SpecRequirements extends FlatSpec with Matchers {
  // [Req: formal — Design Doc §N] X should produce Y
  "Section N requirement" should "produce Y from X" in {
    val result = process(fixture)
    result.property should equal (expectedValue)
  }
}
```

```typescript
// TypeScript (Jest)
describe('Spec Requirements', () => {
  test('[Req: formal — Design Doc §N] X should produce Y', () => {
    const result = process(fixture);
    expect(result.property).toBe(expectedValue);
  });
});
```

```go
// Go (testing)
func TestSpecRequirement_SectionN_XProducesY(t *testing.T) {
    // [Req: formal — Design Doc §N] X should produce Y
    result := Process(fixture)
    if result.Property != expectedValue {
        t.Errorf("expected %v, got %v", expectedValue, result.Property)
    }
}
```

```rust
// Rust (cargo test)
#[test]
fn test_spec_requirement_section_n_x_produces_y() {
    // [Req: formal — Design Doc §N] X should produce Y
    let result = process(&fixture);
    assert_eq!(result.property, expected_value);
}
```

## What Makes a Good Functional Test

- **Traceable** — Test name, display name, or documentation comment says which spec requirement it verifies
- **Specific** — Checks a specific property, not just "something happened"
- **Robust** — Uses real data (fixtures from the actual system), not synthetic data
- **Cross-variant** — If the project handles multiple input types, test all of them
- **Tests at the right layer** — Test the *behavior* you care about. If the requirement is "invalid data doesn't produce wrong output," test the pipeline output — don't just test that the schema validator rejects the input.

## Cross-Variant Testing Strategy

If the project handles multiple input types, cross-variant coverage is where silent bugs hide. Aim for roughly 30% of tests exercising all variants — the exact percentage matters less than ensuring every cross-cutting property is tested across all variants.

Use your framework's parametrization mechanism:

```python
# Python (pytest)
@pytest.mark.parametrize("variant", [variant_a, variant_b, variant_c])
def test_feature_works(variant):
    output = process(variant.input)
    assert output.has_expected_property
```

```java
// Java (JUnit 5)
@ParameterizedTest
@MethodSource("variantProvider")
void testFeatureWorks(Variant variant) {
    var output = process(variant.getInput());
    assertTrue(output.hasExpectedProperty());
}
```

```scala
// Scala (ScalaTest)
Seq(variantA, variantB, variantC).foreach { variant =>
  it should s"work for ${variant.name}" in {
    val output = process(variant.input)
    output should have ('expectedProperty (true))
  }
}
```

```typescript
// TypeScript (Jest)
test.each([variantA, variantB, variantC])(
  'feature works for %s', (variant) => {
    const output = process(variant.input);
    expect(output).toHaveProperty('expectedProperty');
});
```

```go
// Go (testing) — table-driven tests
func TestFeatureWorksAcrossVariants(t *testing.T) {
    variants := []Variant{variantA, variantB, variantC}
    for _, v := range variants {
        t.Run(v.Name, func(t *testing.T) {
            output := Process(v.Input)
            if !output.HasExpectedProperty() {
                t.Errorf("variant %s: missing expected property", v.Name)
            }
        })
    }
}
```

```rust
// Rust (cargo test) — iterate over cases
#[test]
fn test_feature_works_across_variants() {
    let variants = [variant_a(), variant_b(), variant_c()];
    for v in &variants {
        let output = process(&v.input);
        assert!(output.has_expected_property(),
            "variant {}: missing expected property", v.name);
    }
}
```

If parametrization doesn't fit, loop explicitly within a single test.

**Which tests should be cross-variant?** Any test verifying a property that *should* hold regardless of input type: entity identity, structural properties, required links, temporal fields, domain-specific semantics.

**After writing all tests, do a cross-variant audit.** Count cross-variant tests divided by total. If below 30%, convert more.

## Anti-Patterns to Avoid

These patterns look like tests but don't catch real bugs:

- **Existence-only checks** — Finding one correct result doesn't mean all are correct. Also check count or verify comprehensively.
- **Presence-only assertions** — Asserting a value exists only proves presence, not correctness. Assert the actual value.
- **Single-variant testing** — Testing one input type and hoping others work. Use parametrization.
- **Positive-only testing** — You must test that invalid input does NOT produce bad output.
- **Incomplete negative assertions** — When testing rejection, assert ALL consequences are absent, not just one.
- **Catching exceptions instead of checking output** — Testing that code crashes in a specific way isn't testing that it handles input correctly. Test the output.

### The Exception-Catching Anti-Pattern in Detail

```java
// Java — WRONG: tests the validation mechanism
@Test
void testBadValueRejected() {
    fixture.setField("invalid");  // Schema rejects this!
    assertThrows(ValidationException.class, () -> process(fixture));
    // Tells you nothing about output
}

// Java — RIGHT: tests the requirement
@Test
void testBadValueNotInOutput() {
    fixture.setField(null);  // Schema accepts null for Optional
    var output = process(fixture);
    assertFalse(output.contains(badProperty));  // Bad data absent
    assertTrue(output.contains(expectedType));   // Rest still works
}
```

```scala
// Scala — WRONG: tests the decoder, not the requirement
"bad value" should "be rejected" in {
  val input = fixture.copy(field = "invalid")  // Circe decoder fails!
  a [DecodingFailure] should be thrownBy process(input)
  // Tells you nothing about output
}

// Scala — RIGHT: tests the requirement
"missing optional field" should "not produce bad output" in {
  val input = fixture.copy(field = None)  // Option[String] accepts None
  val output = process(input)
  output should not contain badProperty  // Bad data absent
  output should contain (expectedType)   // Rest still works
}
```

```typescript
// TypeScript — WRONG: tests the validation mechanism
test('bad value rejected', () => {
    fixture.field = 'invalid';  // Zod schema rejects this!
    expect(() => process(fixture)).toThrow(ZodError);
    // Tells you nothing about output
});

// TypeScript — RIGHT: tests the requirement
test('bad value not in output', () => {
    fixture.field = undefined;  // Schema accepts undefined for optional
    const output = process(fixture);
    expect(output).not.toContain(badProperty);  // Bad data absent
    expect(output).toContain(expectedType);      // Rest still works
});
```

```python
# Python — WRONG: tests the validation mechanism
def test_bad_value_rejected(fixture):
    fixture.field = "invalid"  # Schema rejects this!
    with pytest.raises(ValidationError):
        process(fixture)
    # Tells you nothing about output

# Python — RIGHT: tests the requirement
def test_bad_value_not_in_output(fixture):
    fixture.field = None  # Schema accepts None for Optional
    output = process(fixture)
    assert field_property not in output  # Bad data absent
    assert expected_type in output  # Rest still works
```

```go
// Go — WRONG: tests the error, not the outcome
func TestBadValueRejected(t *testing.T) {
    fixture.Field = "invalid"  // Validator rejects this!
    _, err := Process(fixture)
    if err == nil { t.Fatal("expected error") }
    // Tells you nothing about output
}

// Go — RIGHT: tests the requirement
func TestBadValueNotInOutput(t *testing.T) {
    fixture.Field = ""  // Zero value is valid
    output, err := Process(fixture)
    if err != nil { t.Fatalf("unexpected error: %v", err) }
    if containsBadProperty(output) { t.Error("bad data should be absent") }
    if !containsExpectedType(output) { t.Error("expected data should be present") }
}
```

```rust
// Rust — WRONG: tests the error, not the outcome
#[test]
fn test_bad_value_rejected() {
    let input = Fixture { field: "invalid".into(), ..default() };
    assert!(process(&input).is_err());  // Tells you nothing about output
}

// Rust — RIGHT: tests the requirement
#[test]
fn test_bad_value_not_in_output() {
    let input = Fixture { field: None, ..default() };  // Option accepts None
    let output = process(&input).expect("should succeed");
    assert!(!output.contains(bad_property));  // Bad data absent
    assert!(output.contains(expected_type));   // Rest still works
}
```

Always check your Step 5b schema map before choosing mutation values.

## Testing at the Right Layer

Ask: "What does the *spec* say should happen?" The spec says "invalid data should not appear in output" — not "validation layer should reject it." Test the spec, not the implementation.

**Exception:** When a spec explicitly mandates a specific mechanism (e.g., "must fail-fast at the schema layer"), testing that mechanism is appropriate. But this is rare.

## Fitness-to-Purpose Scenario Tests

For each scenario in QUALITY.md, write a test. This is a 1:1 mapping:

```scala
// Scala (ScalaTest)
class FitnessScenarios extends FlatSpec with Matchers {
  // [Req: formal — QUALITY.md Scenario 1]
  "Scenario 1: [Name]" should "prevent [failure mode]" in {
    val result = process(fixture)
    result.property should equal (expectedValue)
  }
}
```

```python
# Python (pytest)
class TestFitnessScenarios:
    """Tests for fitness-to-purpose scenarios from QUALITY.md."""

    def test_scenario_1_memorable_name(self, fixture):
        """[Req: formal — QUALITY.md Scenario 1] [Name].
        Requirement: [What the code must do].
        """
        result = process(fixture)
        assert condition_that_prevents_the_failure
```

```java
// Java (JUnit 5)
class FitnessScenariosTest {
    @Test
    @DisplayName("[Req: formal — QUALITY.md Scenario 1] [Name]")
    void testScenario1MemorableName() {
        var result = process(fixture);
        assertTrue(conditionThatPreventsFailure(result));
    }
}
```

```typescript
// TypeScript (Jest)
describe('Fitness Scenarios', () => {
  test('[Req: formal — QUALITY.md Scenario 1] [Name]', () => {
    const result = process(fixture);
    expect(conditionThatPreventsFailure(result)).toBe(true);
  });
});
```

```go
// Go (testing)
func TestScenario1_MemorableName(t *testing.T) {
    // [Req: formal — QUALITY.md Scenario 1] [Name]
    // Requirement: [What the code must do]
    result := Process(fixture)
    if !conditionThatPreventsFailure(result) {
        t.Error("scenario 1 failed: [describe expected behavior]")
    }
}
```

```rust
// Rust (cargo test)
#[test]
fn test_scenario_1_memorable_name() {
    // [Req: formal — QUALITY.md Scenario 1] [Name]
    // Requirement: [What the code must do]
    let result = process(&fixture);
    assert!(condition_that_prevents_the_failure(&result));
}
```

## Boundary and Negative Tests

One test per defensive pattern from Step 5:

```typescript
// TypeScript (Jest)
describe('Boundaries and Edge Cases', () => {
  test('[Req: inferred — from functionName() guard] guards against X', () => {
    const input = { ...validFixture, field: null };
    const result = process(input);
    expect(result).not.toContainBadOutput();
  });
});
```

```python
# Python (pytest)
class TestBoundariesAndEdgeCases:
    """Tests for boundary conditions, malformed input, error handling."""

    def test_defensive_pattern_name(self, fixture):
        """[Req: inferred — from function_name() guard] guards against X."""
        # Mutate to trigger defensive code path
        # Assert graceful handling
```

```java
// Java (JUnit 5)
class BoundariesAndEdgeCasesTest {
    @Test
    @DisplayName("[Req: inferred — from methodName() guard] guards against X")
    void testDefensivePatternName() {
        fixture.setField(null);  // Trigger defensive code path
        var result = process(fixture);
        assertNotNull(result);  // Assert graceful handling
        assertFalse(result.containsBadData());
    }
}
```

```scala
// Scala (ScalaTest)
class BoundariesAndEdgeCases extends FlatSpec with Matchers {
  // [Req: inferred — from methodName() guard]
  "defensive pattern: methodName()" should "guard against X" in {
    val input = fixture.copy(field = None)  // Trigger defensive code path
    val result = process(input)
    result should equal (defined)
    result.get should not contain badData
  }
}
```

```go
// Go (testing)
func TestDefensivePattern_FunctionName_GuardsAgainstX(t *testing.T) {
    // [Req: inferred — from FunctionName() guard] guards against X
    input := defaultFixture()
    input.Field = nil  // Trigger defensive code path
    result, err := Process(input)
    if err != nil {
        t.Fatalf("expected graceful handling, got: %v", err)
    }
    // Assert result is valid despite edge-case input
}
```

```rust
// Rust (cargo test)
#[test]
fn test_defensive_pattern_function_name_guards_against_x() {
    // [Req: inferred — from function_name() guard] guards against X
    let input = Fixture { field: None, ..default_fixture() };
    let result = process(&input).expect("expected graceful handling");
    // Assert result is valid despite edge-case input
}
```

Use your Step 5b schema map when choosing mutation values. Every mutation must use a value the schema accepts.

Systematic approach:
- **Missing fields** — Optional field absent? Set to null.
- **Wrong types** — Field gets different type? Use schema-valid alternative.
- **Empty values** — Empty list? Empty string? Empty dict?
- **Boundary values** — Zero, negative, maximum, first, last.
- **Cross-module boundaries** — Module A produces unusual but valid output — does B handle it?

If you found 10+ defensive patterns but wrote only 4 boundary tests, go back and write more. Target a 1:1 ratio.
